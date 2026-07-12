//! `select()` resolution + the native `config_setting` match computation (T20 select). A `select({...})`
//! crosses the PACKAGE boundary UNRESOLVED (as [`razel_bzl_api::BzlValue::Select`]); THIS is the resolution
//! locus — against the target's configuration, over `config_setting` CTs that carry a [`ConfigMatchInfo`]. The
//! semantics are Bazel-faithful: most-specific-match wins; ambiguous matches / no-match-no-default / an
//! unknown `values` key are TYPED errors (fail-closed, never a silent branch), and `//conditions:default`
//! matches least-specifically (only when no real condition matches).
//!
//! Host-only v1 scope (honest, REAL — matching, not hardcoded): a `config_setting` matches iff its
//! `constraint_values` are all in the resolving configuration's constraint set AND its `values`
//! (cpu/compilation_mode) all equal the resolving configuration's values. `define_values`/`flag_values` are
//! ACCEPTED at load but FAIL CLOSED on USE (razel does not evaluate `--define`/build-setting flags in v1).

use razel_bzl_api::{BzlValue, ProviderId, ProviderInstance, SelectArm, TargetDecl};
use razel_core::{Error, NodeKey};
use razel_engine_api::{Demand, DemandContext};
use razel_source::ExternalRepos;
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{render_label, resolve_dep, target_visibility, ConfiguredTarget, ConfiguredTargetKey};

/// Bazel's always-matches-least-specifically pseudo-condition. Never resolved as a config_setting target.
pub const CONDITIONS_DEFAULT: &str = "//conditions:default";

/// The builtin `ConfigMatchInfo` provider a `config_setting` CT carries: `matched` (Bool) + `settings` (a
/// List of the constraint/value tokens it matched on — the specificity SET for most-specific-match). A
/// SELECT reads it off the condition's CT to decide the winning branch.
pub const CONFIG_MATCH_INFO: &str = "ConfigMatchInfo";

/// The `values` keys razel evaluates in host-only v1. An unknown key is a fail-closed typed error (never a
/// silent no-match) — the honest boundary (TF's `apple_platform_type`, `define`-style keys, … are deferred).
const SUPPORTED_VALUES_KEYS: &[&str] = &["cpu", "compilation_mode"];

/// Composition-root config data for `select()` resolution: per-configuration constraint set (the target
/// platform's `constraint_value` LABELS) + per-configuration `values` (cpu/compilation_mode). Host-only v1:
/// typically ONE entry (the host configuration). Thin but REAL — the match is computed from THIS data, never
/// a hardcoded verdict. Empty = no configuration resolvable (a select with real conditions then fails closed).
#[derive(Clone, Default)]
pub struct SelectConfig {
    /// config name → the set of constraint_value labels the target platform provides (`@platforms//cpu:aarch64`).
    pub platforms: HashMap<String, Vec<String>>,
    /// config name → `{cpu, compilation_mode}` values a `config_setting(values=…)` matches against.
    pub values: HashMap<String, BTreeMap<String, String>>,
}

/// Build the `ConfigMatchInfo` provider instance for a computed match.
fn config_match_provider(matched: bool, settings: Vec<String>) -> ProviderInstance {
    ProviderInstance {
        provider: ProviderId::from_name(CONFIG_MATCH_INFO),
        fields: vec![
            ("matched".to_owned(), BzlValue::Bool(matched)),
            ("settings".to_owned(), BzlValue::List(settings.into_iter().map(BzlValue::Str).collect())),
        ],
    }
}

/// Read a `config_setting` CT's [`ConfigMatchInfo`] → `(matched, specificity settings)`. `None` if the CT is
/// not a config_setting (no such provider) — the select-resolver turns that into a typed "not a config_setting"
/// error (a select condition that names a non-config_setting target is fail-closed).
pub fn read_config_match(ct: &ConfiguredTarget) -> Option<(bool, Vec<String>)> {
    let pi = ct.provider(&ProviderId::from_name(CONFIG_MATCH_INFO))?;
    let matched = match pi.get("matched") {
        Some(BzlValue::Bool(b)) => *b,
        _ => return None,
    };
    let settings = match pi.get("settings") {
        Some(BzlValue::List(items)) => {
            items.iter().filter_map(|i| if let BzlValue::Str(s) = i { Some(s.clone()) } else { None }).collect()
        }
        _ => return None,
    };
    Some((matched, settings))
}

/// The outcome of resolving a target's `select()` attrs — mirrors the `ComputeResult` restart contract so the
/// CT caller threads it straight through.
pub(crate) enum SelectResolution {
    /// Every select resolved; the target carries concrete attr values now.
    Ready(TargetDecl),
    /// Some `config_setting` CT was not yet built — restart after they are.
    Missing(Vec<NodeKey>),
    /// A typed resolution failure (ambiguous / no-match-no-default / unknown values key / non-config_setting
    /// condition).
    Error(Error),
}

/// Resolve every `select()`-valued attr of `target` against the target's configuration (T20 select),
/// substituting each with its concrete resolved value BEFORE dep resolution / rule eval sees it. A target with
/// NO selects returns byte-identical (empty request set — existing analysis paths unchanged). Restart-driven: a
/// select's condition labels name `config_setting` targets whose CTs carry a `ConfigMatchInfo`; they are
/// requested as a group and an unbuilt one re-queues. A condition that names a NON-config_setting target (no
/// `ConfigMatchInfo`) is a typed error; a config_setting that fails closed on use (define_values) PROPAGATES
/// its error through the request (the engine surfaces the dep error).
pub(crate) fn resolve_target_selects(
    ctk: &ConfiguredTargetKey,
    target: TargetDecl,
    repos: &ExternalRepos,
    ctx: &mut dyn DemandContext,
) -> SelectResolution {
    // Fast path: no select attr → byte-identical to the pre-select analysis.
    if !target.attrs.iter().any(|(_, v)| matches!(v, BzlValue::Select(_))) {
        return SelectResolution::Ready(target);
    }
    // (1) collect every REAL condition label (deduped; `//conditions:default` is never a target).
    let mut cond_labels: Vec<String> = Vec::new();
    for (_, v) in &target.attrs {
        if let BzlValue::Select(arms) = v {
            for arm in arms {
                if let SelectArm::Branch { conditions, .. } = arm {
                    for (label, _) in conditions {
                        if label != CONDITIONS_DEFAULT && !cond_labels.contains(label) {
                            cond_labels.push(label.clone());
                        }
                    }
                }
            }
        }
    }
    // (2) resolve each condition to a config_setting CT key (config threaded), request the group.
    let mut keys: Vec<NodeKey> = Vec::with_capacity(cond_labels.len());
    for label in &cond_labels {
        match resolve_dep(ctk, label, repos) {
            Ok(k) => keys.push(k),
            Err(e) => return SelectResolution::Error(e),
        }
    }
    let demands = ctx.request_group(&keys);
    let mut missing: Vec<NodeKey> = Vec::new();
    let mut matches: HashMap<String, (bool, Vec<String>)> = HashMap::new();
    for (i, d) in demands.into_iter().enumerate() {
        match d {
            Demand::Missing => missing.push(keys[i].clone()),
            Demand::Ready(v) => match v.as_any().downcast_ref::<ConfiguredTarget>() {
                Some(ct) => match read_config_match(ct) {
                    Some(m) => {
                        matches.insert(cond_labels[i].clone(), m);
                    }
                    None => {
                        return SelectResolution::Error(Error::Invalid {
                            what: "select condition".into(),
                            detail: format!(
                                "condition '{}' of a select on //{}:{} is not a config_setting (no ConfigMatchInfo)",
                                cond_labels[i], ctk.package, ctk.name
                            ),
                        })
                    }
                },
                None => {
                    return SelectResolution::Error(Error::Invalid {
                        what: "select condition".into(),
                        detail: "a select condition CT was not a ConfiguredTarget".into(),
                    })
                }
            },
        }
    }
    if !missing.is_empty() {
        return SelectResolution::Missing(missing);
    }
    // (3) substitute each select attr with its resolved value (Bazel most-specific-match / fail-closed).
    let target_label = render_label(&ctk.package, &ctk.name);
    let mut attrs = target.attrs.clone();
    for (_, v) in attrs.iter_mut() {
        if let BzlValue::Select(arms) = v {
            match resolve_select_attr(arms, &matches, &target_label) {
                Ok(resolved) => *v = resolved,
                Err(e) => return SelectResolution::Error(e),
            }
        }
    }
    SelectResolution::Ready(TargetDecl { attrs, ..target })
}

/// Extract a `List[str]` attr (`constraint_values`) — empty if absent / not a string list.
fn attr_str_list(target: &TargetDecl, name: &str) -> Vec<String> {
    match target.attrs.iter().find(|(n, _)| n == name).map(|(_, v)| v) {
        Some(BzlValue::List(items)) => {
            items.iter().filter_map(|i| if let BzlValue::Str(s) = i { Some(s.clone()) } else { None }).collect()
        }
        _ => Vec::new(),
    }
}

/// Extract a `{str: str}` attr (`values`/`define_values`/`flag_values`) — empty if absent / not a dict.
fn attr_str_dict(target: &TargetDecl, name: &str) -> Vec<(String, String)> {
    match target.attrs.iter().find(|(n, _)| n == name).map(|(_, v)| v) {
        Some(BzlValue::Dict(pairs)) => pairs
            .iter()
            .filter_map(|(k, v)| match (k, v) {
                (BzlValue::Str(k), BzlValue::Str(v)) => Some((k.clone(), v.clone())),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

/// Compute a native `config_setting`'s CT: a [`ConfigMatchInfo`]-carrying [`ConfiguredTarget`] (no actions,
/// no deps). v1 slice: `constraint_values` ⊆ the resolving configuration's constraint set AND `values`
/// (cpu/compilation_mode) all equal the configuration's values. `define_values`/`flag_values` are fail-closed
/// on USE (this node is demanded only when a select names it). An unknown `values` key is a typed error.
pub fn compute_config_match(
    ctk: &ConfiguredTargetKey,
    target: &TargetDecl,
    select_config: &SelectConfig,
) -> Result<ConfiguredTarget, Error> {
    let constraint_values = attr_str_list(target, "constraint_values");
    let values = attr_str_dict(target, "values");
    let define_values = attr_str_dict(target, "define_values");
    let flag_values = attr_str_dict(target, "flag_values");
    let visibility = target_visibility(target);

    // Fail-closed on USE: razel does not evaluate `--define` / build-setting flags in v1. A select actually
    // decided by such a config_setting errors here (never a silent no-op) — the node is demanded only on use.
    if !define_values.is_empty() || !flag_values.is_empty() {
        return Err(Error::Unsupported {
            what: "config_setting define_values/flag_values",
            detail: format!(
                "//{}:{} uses define_values/flag_values, which razel does not evaluate in v1 (accepted-fail-closed-on-use)",
                ctk.package, ctk.name
            ),
        });
    }

    // The resolving configuration's constraint set + values (host-only: the config name keys both maps).
    let config_name = ctk.configuration.as_deref();
    let constraints: Vec<String> = config_name.and_then(|c| select_config.platforms.get(c)).cloned().unwrap_or_default();
    let config_vals: BTreeMap<String, String> =
        config_name.and_then(|c| select_config.values.get(c)).cloned().unwrap_or_default();

    // A config_setting with real conditions but NO resolving configuration cannot be evaluated — fail closed
    // (never coerce a missing config to "matches" or "no-match" arbitrarily).
    if config_name.is_none() && (!constraint_values.is_empty() || !values.is_empty()) {
        return Err(Error::Unsupported {
            what: "config_setting resolution",
            detail: format!(
                "//{}:{} has constraint_values/values but the target has no configuration to resolve against",
                ctk.package, ctk.name
            ),
        });
    }

    let mut settings: Vec<String> = Vec::new();
    let mut matched = true;
    // constraint_values ⊆ the resolving platform's constraint set.
    for cv in &constraint_values {
        settings.push(cv.clone());
        if !constraints.contains(cv) {
            matched = false;
        }
    }
    // values: only the supported keys (unknown = fail-closed); each must equal the configuration's value.
    for (k, v) in &values {
        if !SUPPORTED_VALUES_KEYS.contains(&k.as_str()) {
            return Err(Error::Unsupported {
                what: "config_setting values key",
                detail: format!(
                    "//{}:{}: unsupported values key '{}' (v1 supports {:?}; an unknown key fails closed)",
                    ctk.package, ctk.name, k, SUPPORTED_VALUES_KEYS
                ),
            });
        }
        settings.push(format!("values:{k}={v}"));
        if config_vals.get(k) != Some(v) {
            matched = false;
        }
    }
    // MUTANT `mutant_config_setting_matches_all`: short-circuit the match to TRUE regardless of the config →
    // a config_setting that should NOT match now does, turning the ambiguity + fail-closed proofs red.
    if cfg!(feature = "mutant_config_setting_matches_all") {
        matched = true;
    }
    settings.sort(); // canonical specificity set (order-independent)
    Ok(ConfiguredTarget { providers: vec![config_match_provider(matched, settings)], actions: Vec::new(), dep_outputs: Vec::new(), visibility })
}

/// Resolve ONE `select()` attribute value (a SelectorList of arms) against the pre-fetched condition matches,
/// concatenating the arms. Each arm resolves independently: a Concrete arm to itself, a Branch to its winning
/// condition's value (Bazel most-specific-match). `matches[label] = (matched, specificity settings)`.
pub fn resolve_select_attr(
    arms: &[SelectArm],
    matches: &HashMap<String, (bool, Vec<String>)>,
    target_label: &str,
) -> Result<BzlValue, Error> {
    let mut resolved: Vec<BzlValue> = Vec::with_capacity(arms.len());
    for arm in arms {
        match arm {
            SelectArm::Concrete(v) => resolved.push(v.clone()),
            SelectArm::Branch { conditions, no_match_error } => {
                resolved.push(resolve_branch(conditions, no_match_error, matches, target_label)?);
            }
        }
    }
    concat_resolved(resolved, target_label)
}

/// Resolve ONE select Branch (`select({cond: value, …})`) to its winning condition's value. Bazel semantics:
/// most-specific real match wins; ambiguous (multiple matches, none most-specific) is a typed error; no real
/// match falls to `//conditions:default`, else a typed no-match error (naming the target + the conditions,
/// or the `no_match_error`).
fn resolve_branch(
    conditions: &[(String, BzlValue)],
    no_match_error: &str,
    matches: &HashMap<String, (bool, Vec<String>)>,
    target_label: &str,
) -> Result<BzlValue, Error> {
    let default = conditions.iter().find(|(l, _)| l == CONDITIONS_DEFAULT).map(|(_, v)| v);

    // MUTANT `mutant_select_default_always_wins`: prefer `//conditions:default` over any real match → a target
    // that should take a specific branch takes the default. Turns the match proofs red.
    if cfg!(feature = "mutant_select_default_always_wins") {
        if let Some(d) = default {
            return Ok(d.clone());
        }
    }
    // MUTANT `mutant_select_takes_first_branch`: ignore matching entirely and take the FIRST real condition's
    // value (dict order) → the wrong branch is chosen. Turns the resolves-to-correct-branch proof red.
    if cfg!(feature = "mutant_select_takes_first_branch") {
        if let Some((_, v)) = conditions.iter().find(|(l, _)| l != CONDITIONS_DEFAULT) {
            return Ok(v.clone());
        }
    }

    // The real (non-default) conditions that MATCHED, with their specificity sets.
    let matching: Vec<(&String, &BzlValue, &Vec<String>)> = conditions
        .iter()
        .filter(|(l, _)| l != CONDITIONS_DEFAULT)
        .filter_map(|(l, v)| match matches.get(l) {
            Some((true, settings)) => Some((l, v, settings)),
            _ => None,
        })
        .collect();

    if matching.is_empty() {
        if let Some(d) = default {
            return Ok(d.clone());
        }
        if !no_match_error.is_empty() {
            return Err(Error::Invalid { what: "select".into(), detail: no_match_error.to_owned() });
        }
        let conds: Vec<&str> = conditions.iter().filter(|(l, _)| l != CONDITIONS_DEFAULT).map(|(l, _)| l.as_str()).collect();
        return Err(Error::Invalid {
            what: "select".into(),
            detail: format!(
                "configurable attribute of '{target_label}' has no matching condition and no //conditions:default (conditions: {conds:?})"
            ),
        });
    }
    match most_specific(&matching) {
        Some(v) => Ok(v.clone()),
        None => {
            let conds: Vec<&str> = matching.iter().map(|(l, _, _)| l.as_str()).collect();
            Err(Error::Invalid {
                what: "select".into(),
                detail: format!(
                    "configurable attribute of '{target_label}' matches multiple conditions with no most-specific resolution (ambiguous): {conds:?}"
                ),
            })
        }
    }
}

/// Bazel specialization: the unique match whose specificity set is a STRICT SUPERSET of every other match's
/// (it "specializes" all others). `None` if no such unique match exists (ambiguous). A SINGLE match trivially
/// specializes the empty rest → returned.
fn most_specific<'a>(matching: &'a [(&String, &'a BzlValue, &'a Vec<String>)]) -> Option<&'a BzlValue> {
    for (i, (_, vi, ri)) in matching.iter().enumerate() {
        let ri_set: HashSet<&String> = ri.iter().collect();
        let specializes_all = matching.iter().enumerate().all(|(j, (_, _, rj))| {
            if i == j {
                return true;
            }
            let rj_set: HashSet<&String> = rj.iter().collect();
            // i specializes j iff ri ⊋ rj (strict superset).
            rj_set.is_subset(&ri_set) && ri_set.len() > rj_set.len()
        });
        if specializes_all {
            return Some(vi);
        }
    }
    None
}

/// Concatenate resolved select arms (Bazel `+`): a single arm is itself; all-List arms concatenate into one
/// List; all-Dict arms merge (later-wins). Any other mix is a typed error (non-concatenable). This mirrors
/// Bazel's SelectorList join over the resolved values.
fn concat_resolved(values: Vec<BzlValue>, target_label: &str) -> Result<BzlValue, Error> {
    if values.len() == 1 {
        return Ok(values.into_iter().next().expect("len 1"));
    }
    if values.iter().all(|v| matches!(v, BzlValue::List(_))) {
        let mut out: Vec<BzlValue> = Vec::new();
        for v in values {
            if let BzlValue::List(items) = v {
                out.extend(items);
            }
        }
        return Ok(BzlValue::List(out));
    }
    if values.iter().all(|v| matches!(v, BzlValue::Dict(_))) {
        let mut out: Vec<(BzlValue, BzlValue)> = Vec::new();
        for v in values {
            if let BzlValue::Dict(pairs) = v {
                for (k, val) in pairs {
                    out.retain(|(ek, _)| ek != &k); // later-wins (Bazel dict `|`)
                    out.push((k, val));
                }
            }
        }
        return Ok(BzlValue::Dict(out));
    }
    Err(Error::Invalid {
        what: "select".into(),
        detail: format!("configurable attribute of '{target_label}' concatenates non-list/non-dict select arms (not joinable)"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use razel_bzl_api::TargetDecl;

    fn s(x: &str) -> BzlValue {
        BzlValue::Str(x.into())
    }
    fn list(xs: &[&str]) -> BzlValue {
        BzlValue::List(xs.iter().map(|x| s(x)).collect())
    }
    fn ckey(name: &str, cfg: Option<&str>) -> ConfiguredTargetKey {
        ConfiguredTargetKey {
            package: "p".into(),
            name: name.into(),
            configuration: cfg.map(|c| c.into()),
            exec_platform: None,
            rule_transition: None,
        }
    }
    fn cs_target(name: &str, constraint_values: &[&str], values: &[(&str, &str)]) -> TargetDecl {
        let mut attrs = Vec::new();
        if !constraint_values.is_empty() {
            attrs.push(("constraint_values".into(), list(constraint_values)));
        }
        if !values.is_empty() {
            attrs.push((
                "values".into(),
                BzlValue::Dict(values.iter().map(|(k, v)| (s(k), s(v))).collect()),
            ));
        }
        TargetDecl { kind: "config_setting".into(), name: name.into(), attrs, origin: None }
    }
    /// The host config: aarch64+osx constraints, cpu=darwin_arm64, compilation_mode=fastbuild.
    fn host() -> SelectConfig {
        let mut platforms = HashMap::new();
        platforms.insert("host".into(), vec!["@platforms//cpu:aarch64".to_string(), "@platforms//os:osx".to_string()]);
        let mut values = HashMap::new();
        values.insert(
            "host".to_string(),
            BTreeMap::from([("cpu".to_string(), "darwin_arm64".to_string()), ("compilation_mode".to_string(), "fastbuild".to_string())]),
        );
        SelectConfig { platforms, values }
    }
    fn matched(m: &ConfiguredTarget) -> bool {
        read_config_match(m).unwrap().0
    }

    /// config_setting matches iff its constraint_values ⊆ the host constraint set AND its values equal the
    /// host's. A darwin-arm setting matches the darwin host; a linux setting does NOT. RED under
    /// `mutant_config_setting_matches_all` (the linux setting then matches too).
    #[test]
    fn config_setting_matches_by_constraints_and_values() {
        let sc = host();
        let darwin = compute_config_match(&ckey("darwin", Some("host")), &cs_target("darwin", &["@platforms//cpu:aarch64", "@platforms//os:osx"], &[]), &sc).unwrap();
        assert!(matched(&darwin), "aarch64+osx ⊆ host → match");
        let linux = compute_config_match(&ckey("linux", Some("host")), &cs_target("linux", &["@platforms//os:linux"], &[]), &sc).unwrap();
        assert!(!matched(&linux), "a linux config_setting must NOT match a darwin host (RED under mutant_config_setting_matches_all)");
        // values: cpu matches, then a wrong cpu no-matches.
        let cpu_ok = compute_config_match(&ckey("cpu", Some("host")), &cs_target("cpu", &[], &[("cpu", "darwin_arm64")]), &sc).unwrap();
        assert!(matched(&cpu_ok), "values cpu=darwin_arm64 matches the host");
        let cpu_no = compute_config_match(&ckey("cpu2", Some("host")), &cs_target("cpu2", &[], &[("cpu", "k8")]), &sc).unwrap();
        assert!(!matched(&cpu_no), "values cpu=k8 does not match a darwin host");
    }

    /// Fail-closed config_setting: an unknown `values` key is a typed error; `define_values`/`flag_values` are
    /// accepted at load but fail closed on USE.
    #[test]
    fn config_setting_fail_closed_surfaces() {
        let sc = host();
        assert!(
            matches!(compute_config_match(&ckey("u", Some("host")), &cs_target("u", &[], &[("apple_platform_type", "macos")]), &sc), Err(Error::Unsupported { .. })),
            "an unknown values key (TF's apple_platform_type) is a typed error"
        );
        let dv = TargetDecl {
            kind: "config_setting".into(),
            name: "d".into(),
            attrs: vec![("define_values".into(), BzlValue::Dict(vec![(s("framework_shared_object"), s("true"))]))],
            origin: None,
        };
        assert!(
            matches!(compute_config_match(&ckey("d", Some("host")), &dv, &sc), Err(Error::Unsupported { .. })),
            "define_values fails closed on use (razel does not evaluate --define in v1)"
        );
    }

    /// Build a matches map from (label, matched, specificity-settings) triples.
    fn mk_matches(entries: &[(&str, bool, &[&str])]) -> HashMap<String, (bool, Vec<String>)> {
        entries.iter().map(|(l, m, set)| ((*l).to_string(), (*m, set.iter().map(|x| x.to_string()).collect()))).collect()
    }

    /// select() resolves to the MATCHING condition's branch — not the first dict entry, not the default. Here
    /// the first entry (`:linux`) does NOT match and the second (`:darwin`) DOES → the darwin branch wins. RED
    /// under `mutant_select_takes_first_branch` (takes `:linux`) and `mutant_select_default_always_wins`.
    #[test]
    fn select_resolves_to_matching_branch() {
        let arms = vec![SelectArm::Branch {
            conditions: vec![
                (":darwin".into(), list(&["//dep:darwin"])),
                (":linux".into(), list(&["//dep:linux"])),
                (CONDITIONS_DEFAULT.into(), list(&["//dep:default"])),
            ],
            no_match_error: String::new(),
        }];
        let matches = mk_matches(&[(":linux", false, &["@platforms//os:linux"]), (":darwin", true, &["@platforms//cpu:aarch64"])]);
        let resolved = resolve_select_attr(&arms, &matches, "//p:t").unwrap();
        assert_eq!(resolved, list(&["//dep:darwin"]), "resolves to the MATCHING (darwin) branch, not first-entry / default");
    }

    /// `//conditions:default` is the fallback ONLY when no real condition matches (least-specific).
    #[test]
    fn select_falls_to_default_when_no_match() {
        let arms = vec![SelectArm::Branch {
            conditions: vec![(":linux".into(), list(&["//dep:linux"])), (CONDITIONS_DEFAULT.into(), list(&["//dep:default"]))],
            no_match_error: String::new(),
        }];
        let matches = mk_matches(&[(":linux", false, &["@platforms//os:linux"])]);
        assert_eq!(resolve_select_attr(&arms, &matches, "//p:t").unwrap(), list(&["//dep:default"]), "no real match → default");
    }

    /// most-specific-match: a matching condition whose constraint set is a STRICT SUPERSET of another matching
    /// condition wins (Bazel specialization) — never ambiguous.
    #[test]
    fn select_most_specific_wins() {
        let arms = vec![SelectArm::Branch {
            conditions: vec![(":osx".into(), list(&["//dep:osx"])), (":osx_arm".into(), list(&["//dep:osx_arm"]))],
            no_match_error: String::new(),
        }];
        // both match; :osx_arm's set ⊋ :osx's set → :osx_arm specializes → wins.
        let matches = mk_matches(&[
            (":osx", true, &["@platforms//os:osx"]),
            (":osx_arm", true, &["@platforms//os:osx", "@platforms//cpu:aarch64"]),
        ]);
        assert_eq!(resolve_select_attr(&arms, &matches, "//p:t").unwrap(), list(&["//dep:osx_arm"]), "the more-specific (superset) condition wins");
    }

    /// Fail-closed resolution: two INCOMPARABLE matching conditions = ambiguous typed error; no match + no
    /// default = a typed no-match error naming the conditions.
    #[test]
    fn select_fail_closed_ambiguous_and_no_match() {
        // ambiguous: both match, neither specializes the other.
        let ambiguous = vec![SelectArm::Branch {
            conditions: vec![(":a".into(), list(&["//a"])), (":b".into(), list(&["//b"]))],
            no_match_error: String::new(),
        }];
        let both = mk_matches(&[(":a", true, &["@platforms//os:osx"]), (":b", true, &["@platforms//cpu:aarch64"])]);
        assert!(
            matches!(resolve_select_attr(&ambiguous, &both, "//p:t"), Err(Error::Invalid { .. })),
            "two incomparable matches are an ambiguous typed error"
        );
        // no match + no default → typed error naming the conditions.
        let no_default = vec![SelectArm::Branch { conditions: vec![(":a".into(), list(&["//a"]))], no_match_error: String::new() }];
        let none = mk_matches(&[(":a", false, &[])]);
        let err = resolve_select_attr(&no_default, &none, "//p:t").unwrap_err();
        assert!(matches!(err, Error::Invalid { .. }), "no match + no default is a typed error");
        if let Error::Invalid { detail, .. } = err {
            assert!(detail.contains("//p:t") && detail.contains(":a"), "the no-match error names the target + conditions: {detail}");
        }
    }

    /// A `[base] + select(...)` SelectorList CONCATENATES the resolved arms (Bazel list `+`).
    #[test]
    fn select_concatenates_list_arms() {
        let arms = vec![
            SelectArm::Concrete(list(&["//base"])),
            SelectArm::Branch { conditions: vec![(":a".into(), list(&["//a"])), (CONDITIONS_DEFAULT.into(), list(&[]))], no_match_error: String::new() },
        ];
        let matches = mk_matches(&[(":a", true, &["@platforms//os:osx"])]);
        assert_eq!(resolve_select_attr(&arms, &matches, "//p:t").unwrap(), list(&["//base", "//a"]), "concat: base ++ matched branch");
    }
}
