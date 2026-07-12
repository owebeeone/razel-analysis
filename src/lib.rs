//! `razel-analysis` — the `CONFIGURED_TARGET` node-kind: the analysis phase over the proven engine. For a
//! target it runs the rule's implementation (via the `BzlEvaluator::evaluate_rule` seam) and yields the
//! providers the rule publishes. Dependency edges are real engine edges: a target's label-typed attrs resolve
//! to `CONFIGURED_TARGET(dep)` nodes (restart-driven), so providers propagate granularly across the target
//! graph and the engine's early cutoff applies per target.
//!
//! Key shape is the FULL ADR-0010 configured-target key from commit #1 — `{label, configuration, exec_platform,
//! rule_transition}` — even though v1 always passes `None`/identity. The config dimension is THREADED into each
//! dependency's key (an identity transform now; a real transition slots in at that one site later) so adding
//! real configurations is additive, not a rewrite (anti-corner invariant III).
//!
//! SPIKE scope (honest, fail-closed): a target instantiated by the generic `target()` placeholder (no rule
//! origin) is `Unsupported` here — there is no impl to run. `ctx.actions`/`ctx.toolchains` do not exist yet
//! (toolchain resolution is v3 pitfall #4's own G4 exam). The rule `.bzl`'s own `load()`s are not yet threaded
//! into `evaluate_rule` (self-contained rule `.bzl`s only).

use razel_bzl_api::{
    encode_provider_instance, ActionTemplate, BzlEvaluator, BzlModule, BzlValue, DepProviders, EvalEnv, LoadKind,
    ProviderId, ProviderInstance, ResolvedToolchain,
};
use razel_toolchain::{ResolvedToolchainContextValue, ToolchainContextKey, ToolchainType, ToolchainTypeReq};
use razel_core::{Digest, Error, Key, KindId, NodeKey, Value, ValuePolicy};
use razel_engine_api::{ComputeResult, Demand, DemandContext, DemandEngine, NodeFunction};
use razel_ids::{ConfigId, RootRelativePath};
use razel_load::{resolve_load, BzlLoadKey, BzlModuleValue};
use razel_os_api::{HostPath, System};
use razel_package::{Package, PackageKey};
use razel_source::{resolve_source_path, ExternalRepos, FileKey, FileValue};
use std::any::Any;
use std::sync::Arc;

/// `select()` resolution + the native `config_setting` match computation (T20 select).
mod select;
pub use select::{SelectConfig, CONFIG_MATCH_INFO};

pub const CONFIGURED_TARGET: KindId = KindId(40);

/// The configured-target key — the FULL ADR-0010 shape from commit #1. `package` + `name` are the label;
/// `configuration` / `exec_platform` / `rule_transition` are the analysis dimensions (all `None` in v1, but
/// PRESENT so they participate in identity + encode, and adding a real value later is a new distinct key).
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ConfiguredTargetKey {
    pub package: String,
    pub name: String,
    pub configuration: Option<String>,
    pub exec_platform: Option<String>,
    pub rule_transition: Option<String>,
}
impl Key for ConfiguredTargetKey {
    fn kind(&self) -> KindId {
        CONFIGURED_TARGET
    }
    fn encode(&self) -> Vec<u8> {
        let mut b = Vec::new();
        enc_str(&mut b, &self.package);
        enc_str(&mut b, &self.name);
        enc_opt(&mut b, &self.configuration);
        enc_opt(&mut b, &self.exec_platform);
        enc_opt(&mut b, &self.rule_transition);
        b
    }
}
fn enc_str(b: &mut Vec<u8>, s: &str) {
    b.extend_from_slice(&(s.len() as u32).to_be_bytes());
    b.extend_from_slice(s.as_bytes());
}
fn enc_opt(b: &mut Vec<u8>, o: &Option<String>) {
    match o {
        None => b.push(0),
        Some(s) => {
            b.push(1);
            enc_str(b, s);
        }
    }
}

/// A byte cursor for fail-closed key decoding (a malformed key is a typed error, never a silent default).
struct Cur<'a> {
    b: &'a [u8],
    i: usize,
}
impl<'a> Cur<'a> {
    fn new(b: &'a [u8]) -> Self {
        Self { b, i: 0 }
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8], Error> {
        if self.i + n > self.b.len() {
            return Err(Error::Invalid { what: "CONFIGURED_TARGET key".into(), detail: "truncated".into() });
        }
        let s = &self.b[self.i..self.i + n];
        self.i += n;
        Ok(s)
    }
    fn str(&mut self) -> Result<String, Error> {
        // Fail-closed all the way: even the (in practice infallible) 4-byte→array conversion is a typed error,
        // not an unwrap, so a malformed key can never panic here.
        let raw = self.take(4)?;
        let arr: [u8; 4] = raw.try_into().map_err(|_| Error::Invalid {
            what: "CONFIGURED_TARGET key".into(),
            detail: "bad length prefix".into(),
        })?;
        let len = u32::from_be_bytes(arr) as usize;
        let s = self.take(len)?;
        String::from_utf8(s.to_vec()).map_err(|_| Error::Invalid { what: "CONFIGURED_TARGET key".into(), detail: "non-utf8".into() })
    }
    fn opt(&mut self) -> Result<Option<String>, Error> {
        match self.take(1)?[0] {
            0 => Ok(None),
            1 => Ok(Some(self.str()?)),
            t => Err(Error::Invalid { what: "CONFIGURED_TARGET key".into(), detail: format!("bad option tag {t}") }),
        }
    }
}
/// Decode a `CONFIGURED_TARGET` key's canonical bytes — THE one decode of CT identity (the artifact-model
/// lockdown §2 "no second channel" rule): `razel-action`'s `GeneratingActionKey`/`TargetCompletionKey`
/// codecs delegate here rather than re-implementing the CT frame. Fail-closed: malformed input is a typed
/// `Error::Invalid`, never a panic.
pub fn decode_ct_key(bytes: &[u8]) -> Result<ConfiguredTargetKey, Error> {
    let mut c = Cur::new(bytes);
    let package = c.str()?;
    let name = c.str()?;
    let configuration = c.opt()?;
    let exec_platform = c.opt()?;
    let rule_transition = c.opt()?;
    Ok(ConfiguredTargetKey { package, name, configuration, exec_platform, rule_transition })
}

/// One declared output of a DIRECT dependency, stamped with its PRODUCING action — the per-invocation
/// files-chaining map (`RazelV4ArtifactModelLockdown.md` §3 R3 note / decision A: "my inputs are my dep's
/// outputs"). Built at analysis time from the deps' `{providers, actions}` (which the CT already fetched to
/// propagate providers), it rides the CT VALUE — never a node key (the frozen ACTION/ARTIFACT keys don't
/// reshape). The `ACTION` node's `InputResolver` consults it via the owner CT value: an action input path
/// matching a dep output resolves to `Derived{producer_ct, action_index}` (fail-closed — anything else is a
/// sibling output, a source, or a typed error, never absorbed).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DepOutput {
    pub exec_path: String,
    pub producer_ct: ConfiguredTargetKey,
    pub action_index: u32,
}

/// `CONFIGURED_TARGET` value: the providers the rule published + the action templates it declared + the
/// files-chaining map of its DIRECT deps' outputs (all consumed by the execution phase). Plain, `comparable`
/// (canonical order from the seam → early cutoff), `serializable`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ConfiguredTarget {
    pub providers: Vec<ProviderInstance>,
    pub actions: Vec<ActionTemplate>,
    /// The DIRECT-dep output → producing-action chaining map (see [`DepOutput`]). Empty for a leaf target
    /// (no deps) or a target whose deps declare no outputs.
    pub dep_outputs: Vec<DepOutput>,
    /// The target's `visibility` label-strings (C7, D7) — carried on the CT VALUE so a DEPENDENT can enforce
    /// the cross-package edge (default private; `["//visibility:public"]` = visible everywhere). Empty =
    /// private. In the digest so a visibility edit invalidates dependents (an edge that was allowed may error).
    pub visibility: Vec<String>,
}
impl ConfiguredTarget {
    /// Provider lookup on the ONE identity funnel (lockdown C2): keyed by `ProviderId`'s derived `Eq` —
    /// never a raw name comparison (a bzl-differing identity is a DIFFERENT provider).
    pub fn provider(&self, id: &ProviderId) -> Option<&ProviderInstance> {
        self.providers.iter().find(|p| &p.provider == id)
    }
}
impl Value for ConfiguredTarget {
    fn policy(&self) -> ValuePolicy {
        ValuePolicy { comparable: true, always_dirty: false, shareable: true, serializable: true, process_local: false }
    }
    fn value_eq(&self, other: &dyn Value) -> bool {
        other.as_any().downcast_ref::<ConfiguredTarget>().is_some_and(|o| o == self)
    }
    fn content_digest(&self) -> Digest {
        let mut b = encode_providers(&self.providers);
        b.extend_from_slice(&(self.actions.len() as u64).to_be_bytes());
        for a in &self.actions {
            enc_str(&mut b, &a.mnemonic);
            for list in [&a.argv, &a.inputs, &a.outputs] {
                b.extend_from_slice(&(list.len() as u64).to_be_bytes());
                for s in list {
                    enc_str(&mut b, s);
                }
            }
            b.extend_from_slice(&(a.env.len() as u64).to_be_bytes());
            for (k, v) in &a.env {
                enc_str(&mut b, k);
                enc_str(&mut b, v);
            }
        }
        // The files-chaining map, APPENDED after the (frozen-boundary) actions block: a self-delimiting
        // count-anchored run of (exec_path, length-framed producer CT key, action index). A dep-output edit
        // that changes the producing action is thus a value + digest change (and a `value_eq` change → the
        // dependent action re-runs). Empty for a leaf → byte-identical to the pre-chaining digest.
        b.extend_from_slice(&(self.dep_outputs.len() as u64).to_be_bytes());
        for d in &self.dep_outputs {
            enc_str(&mut b, &d.exec_path);
            let ct = d.producer_ct.encode();
            b.extend_from_slice(&(ct.len() as u64).to_be_bytes());
            b.extend_from_slice(&ct);
            b.extend_from_slice(&d.action_index.to_be_bytes());
        }
        // Visibility (C7), appended count-anchored after the dep_outputs run: a visibility edit changes the
        // value + digest, so a dependent whose cross-package edge's legality flips re-analyzes. Empty
        // (private) → a self-delimiting `0` count, so a pre-C7 leaf digest widens by exactly 8 bytes.
        b.extend_from_slice(&(self.visibility.len() as u64).to_be_bytes());
        for v in &self.visibility {
            enc_str(&mut b, v);
        }
        Digest::of(&b)
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
}
fn encode_providers(ps: &[ProviderInstance]) -> Vec<u8> {
    // Lead with the provider COUNT so the providers block is self-delimiting — otherwise, when this is followed by
    // the action block in ConfiguredTarget::content_digest, the providers↔actions boundary is unanchored and a
    // provider field could in principle bleed into the action count (a #1-class collision). Each provider is
    // encoded by the canonical razel-bzl-api codec (the single source of truth — no local BzlValue encoder).
    let mut b = Vec::new();
    b.extend_from_slice(&(ps.len() as u64).to_be_bytes());
    for p in ps {
        encode_provider_instance(p, &mut b);
    }
    b
}

/// Merge one dep-output entry into the accumulating files-chaining map with the fail-closed dedup/conflict
/// discipline — SHARED by the DIRECT-dep-output stamp and the TRANSITIVE-closure merge. An entry whose
/// `exec_path` is already mapped to the SAME `(producer CT, action index)` is a benign duplicate (the
/// diamond: one producer reached by two dependency paths) and is deduped; the SAME `exec_path` from a
/// DIFFERENT producer is a typed [`Error::Conflict`] (two distinct dependencies claim one output path —
/// never a silent first-wins). `owner` is only for the error message.
fn merge_dep_output(
    dep_outputs: &mut Vec<DepOutput>,
    entry: DepOutput,
    owner: &ConfiguredTargetKey,
) -> Result<(), Error> {
    if let Some(prev) = dep_outputs.iter().find(|d| d.exec_path == entry.exec_path) {
        if prev.producer_ct != entry.producer_ct || prev.action_index != entry.action_index {
            return Err(Error::Conflict {
                what: "duplicate dep output".into(),
                detail: format!(
                    "//{}:{}: dep output '{}' is produced by two distinct dependencies",
                    owner.package, owner.name, entry.exec_path
                ),
            });
        }
        return Ok(()); // benign duplicate (diamond) — dedup, do not re-push.
    }
    dep_outputs.push(entry);
    Ok(())
}

/// Resolve a dependency label string to a `CONFIGURED_TARGET` key, threading the PARENT's configuration into
/// the child (an identity transform in v1 — a real rule/configuration transition slots in here later, additive).
/// Forms: `":name"` (same package), `"//pkg:name"` (absolute), and `"@repo//pkg:name"` (external repo, T17 —
/// canonical D1 package text `@<repo>//<pkg>`, DECLARED repo resolves / UNDECLARED stays a typed error). Every
/// other form fails closed (never mis-resolved). `repos` is the external-repo registry (empty = internal-only,
/// so all existing internal resolutions are byte-identical).
pub(crate) fn resolve_dep(parent: &ConfiguredTargetKey, lbl: &str, repos: &ExternalRepos) -> Result<NodeKey, Error> {
    let (package, name) = if let Some(rest) = lbl.strip_prefix('@') {
        // `@repo//pkg:name` — an external-repo label. Parse the canonical D1 package text `@<repo>//<pkg>`
        // (root package → `@<repo>//`). Fail-closed for an UNDECLARED repo (never a workspace fallback).
        let (repo, after) = match rest.split_once("//") {
            Some((repo, after)) if !repo.is_empty() => (repo, after),
            _ => return Err(Error::Unsupported { what: "dep label form", detail: format!("expected '@repo//pkg:name', got '{lbl}'") }),
        };
        let (pkg_rel, n) = match after.split_once(':') {
            Some((p, n)) if !n.is_empty() => (p, n),
            _ => return Err(Error::Unsupported { what: "dep label form", detail: format!("expected '@repo//pkg:name', got '{lbl}'") }),
        };
        if !repos.contains(repo) {
            return Err(Error::NotFound {
                what: "external repository".into(),
                detail: format!("undeclared repository '@{repo}' in dep label '{lbl}' (fail-closed — no workspace fallback)"),
            });
        }
        let package = if cfg!(feature = "mutant_repo_prefix_stripped_from_package") {
            // MUTANT: drop the `@<repo>//` marker → the external package string collapses to its bare pkg-rel,
            // colliding in CT identity with an internal package of the same suffix. Turns
            // `external_and_internal_same_suffix_packages_are_distinct_cts` RED (the D1 distinct-identity law).
            pkg_rel.to_string()
        } else {
            format!("@{repo}//{pkg_rel}")
        };
        (package, n.to_string())
    } else if let Some(rest) = lbl.strip_prefix("//") {
        match rest.split_once(':') {
            Some((p, n)) if !n.is_empty() => (p.to_string(), n.to_string()),
            _ => return Err(Error::Unsupported { what: "dep label form", detail: format!("expected //pkg:name, got '{lbl}'") }),
        }
    } else if let Some(n) = lbl.strip_prefix(':') {
        if n.is_empty() {
            return Err(Error::Unsupported { what: "dep label form", detail: "empty target name".into() });
        }
        (parent.package.clone(), n.to_string())
    } else {
        return Err(Error::Unsupported { what: "dep label form", detail: format!("expected ':name', '//pkg:name', or '@repo//pkg:name', got '{lbl}'") });
    };
    // MUTANT: dropping the parent's configuration here regresses anti-corner (III) (config not threaded).
    let (configuration, exec_platform, rule_transition) = if cfg!(feature = "mutant_ct_drops_config") {
        (None, None, None)
    } else {
        (parent.configuration.clone(), parent.exec_platform.clone(), parent.rule_transition.clone())
    };
    Ok(NodeKey::from_key(&ConfiguredTargetKey { package, name, configuration, exec_platform, rule_transition }))
}

/// Render a `(package, name)` as the ctx.label string for the rule eval. An external package already carries
/// its `@<repo>//` prefix (canonical D1 text) → `@<repo>//<pkg>:<name>`; an internal package → `//<pkg>:<name>`.
/// The ONE place the label-string form is produced (rust.bzl's v1 `_pkg`/`_name` parse it; C1 swaps in a Label).
pub(crate) fn render_label(package: &str, name: &str) -> String {
    if package.starts_with('@') {
        format!("{package}:{name}")
    } else {
        format!("//{package}:{name}")
    }
}

/// The repo a D1 exec-space path belongs to: `external/<repo>/…` → `Some(repo)`, a main-repo path → `None`.
/// Used to scope a rule `.bzl`'s `//`-relative `load()`s to its DEFINING repo (row-3 per-repo load context)
/// when threading its transitive load closure into `evaluate_rule`.
fn repo_context_of(exec_path: &str) -> Option<String> {
    exec_path.strip_prefix("external/").and_then(|rest| rest.split('/').next()).map(|s| s.to_string())
}

/// The C7 well-known visibility specs (D7 minimal cut: public/private only; groups + package labels later).
const VISIBILITY_PUBLIC: &str = "//visibility:public";
const VISIBILITY_PRIVATE: &str = "//visibility:private";

/// Extract a target's `visibility` label-strings (C7). Absent → empty (the private default). `pub(crate)`:
/// the `config_setting` CT (select.rs) carries the same visibility on its match-info value.
pub(crate) fn target_visibility(target: &razel_bzl_api::TargetDecl) -> Vec<String> {
    match target.attrs.iter().find(|(n, _)| n == "visibility").map(|(_, v)| v) {
        Some(BzlValue::List(items)) => {
            items.iter().filter_map(|i| if let BzlValue::Str(s) = i { Some(s.clone()) } else { None }).collect()
        }
        Some(BzlValue::Str(s)) => vec![s.clone()],
        _ => Vec::new(),
    }
}

/// Enforce a dependency edge's visibility (C7, D7): a SAME-package edge is always allowed; a CROSS-package
/// edge to a `//visibility:public` target is allowed; a cross-package edge to a private (default/absent)
/// target is a typed analysis error naming BOTH labels (Bazel's shape). Unknown visibility forms (groups /
/// `//pkg:__pkg__`) fail closed — deferred, never silently allowed. RED under `mutant_visibility_ignored`.
fn check_visibility(
    parent_pkg: &str,
    dep_pkg: &str,
    parent_label: &str,
    dep_label: &str,
    dep_visibility: &[String],
) -> Result<(), Error> {
    // MUTANT: skip enforcement → a private cross-package dep silently resolves (the D7 hole this guards).
    if cfg!(feature = "mutant_visibility_ignored") {
        return Ok(());
    }
    if parent_pkg == dep_pkg {
        return Ok(()); // same-package edges are always visible (Bazel)
    }
    let mut public = false;
    for v in dep_visibility {
        match v.as_str() {
            VISIBILITY_PUBLIC => public = true,
            VISIBILITY_PRIVATE => {}
            other => {
                return Err(Error::Unsupported {
                    what: "visibility form",
                    detail: format!("unsupported visibility '{other}' on '{dep_label}' (v1: //visibility:public|private only)"),
                })
            }
        }
    }
    if public {
        return Ok(());
    }
    Err(Error::Invalid {
        what: "visibility".into(),
        detail: format!(
            "target '{dep_label}' is not visible to '{parent_label}' (default private; add visibility = [\"//visibility:public\"])"
        ),
    })
}

/// `CONFIGURED_TARGET`: analyze one target — resolve its selects + deps, then run its rule's impl → providers.
pub struct ConfiguredTargetFn {
    sys: Arc<dyn System>,
    root: HostPath,
    eval: Arc<dyn BzlEvaluator>,
    repos: ExternalRepos,
    /// Composition-root config data for `select()` resolution (T20 select): per-configuration constraint set +
    /// values. EMPTY by default (existing callers unchanged — a target with no selects is byte-identical, and
    /// a select with real conditions over an empty config fails closed); the host seeds the real host config.
    select_config: SelectConfig,
}
impl ConfiguredTargetFn {
    pub fn new(sys: Arc<dyn System>, root: HostPath, eval: Arc<dyn BzlEvaluator>) -> Self {
        Self::new_with_repos(sys, root, eval, ExternalRepos::empty())
    }
    pub fn new_with_repos(sys: Arc<dyn System>, root: HostPath, eval: Arc<dyn BzlEvaluator>, repos: ExternalRepos) -> Self {
        Self::new_with_repos_and_select(sys, root, eval, repos, SelectConfig::default())
    }
    pub fn new_with_repos_and_select(
        sys: Arc<dyn System>,
        root: HostPath,
        eval: Arc<dyn BzlEvaluator>,
        repos: ExternalRepos,
        select_config: SelectConfig,
    ) -> Self {
        Self { sys, root, eval, repos, select_config }
    }

    /// `alias` analysis (T19-P2): forward the `actual` target's providers + dep-output chaining. The alias's
    /// OWN visibility rides its CT value (a DEPENDENT enforces the alias edge); the alias→actual edge enforces
    /// `actual`'s visibility here (a private cross-package `actual` is a typed error). An alias declares NO
    /// actions of its own. LANGUAGE-AGNOSTIC — it forwards whatever providers `actual` published, so it serves
    /// rust targets today and non-rust targets later without change.
    fn compute_alias(
        &self,
        ctk: &ConfiguredTargetKey,
        target: &razel_bzl_api::TargetDecl,
        ctx: &mut dyn DemandContext,
    ) -> ComputeResult {
        // `actual` is a single label string (Bazel's alias.actual). Fail closed on any other shape.
        let actual = match target.attrs.iter().find(|(n, _)| n == "actual").map(|(_, v)| v) {
            Some(BzlValue::Str(s)) => s.clone(),
            _ => {
                return ComputeResult::Error(Error::Invalid {
                    what: "alias 'actual'".into(),
                    detail: format!("//{}:{} alias requires a single 'actual' label string", ctk.package, ctk.name),
                })
            }
        };
        let visibility = target_visibility(target);
        let parent_label = render_label(&ctk.package, &ctk.name);
        // Resolve + request the `actual` CT (restart-driven; config threaded via resolve_dep).
        let dep_key = match resolve_dep(ctk, &actual, &self.repos) {
            Ok(k) => k,
            Err(e) => return ComputeResult::Error(e),
        };
        let dv = match ctx.request(&dep_key) {
            Demand::Missing => return ComputeResult::Missing { recorded_dep_keys: vec![dep_key] },
            Demand::Ready(v) => v,
        };
        let act = match dv.as_any().downcast_ref::<ConfiguredTarget>() {
            Some(ct) => ct,
            None => return ComputeResult::Error(Error::Invalid { what: "alias actual".into(), detail: "not a ConfiguredTarget".into() }),
        };
        let dep_ct_key = match decode_ct_key(dep_key.canonical()) {
            Ok(k) => k,
            Err(e) => return ComputeResult::Error(e),
        };
        // Enforce the alias→actual edge (a private `actual` in another package is a typed error, just like a
        // normal dep edge). Uses the `actual`'s own visibility carried on its CT value.
        if let Err(e) = check_visibility(&ctk.package, &dep_ct_key.package, &parent_label, &actual, &act.visibility) {
            return ComputeResult::Error(e);
        }
        // Forward the `actual`'s providers VERBATIM — the whole point of an alias.
        // MUTANT `mutant_alias_breaks_provider_passthrough`: drop the actual's providers → a dependent that
        // reads a forwarded provider (e.g. `dep[RustInfo]` in rust.bzl) can no longer find it and the build
        // fails closed. Turns the alias provider-passthrough proof RED (unfiltered).
        let providers = if cfg!(feature = "mutant_alias_breaks_provider_passthrough") {
            Vec::new()
        } else {
            act.providers.clone()
        };
        // Build the dep-output chaining EXACTLY as a direct dependent of `actual` would (paths a + b), so the
        // alias is TRANSPARENT: the actual's OWN action outputs map to the actual's CT, and its transitive
        // dep_outputs pass through with the producer CT carried verbatim. A dependent that names `actual`'s
        // rlib as a rustc input then resolves it to the actual's generating action through the alias.
        let mut dep_outputs: Vec<DepOutput> = Vec::new();
        for (idx, tmpl) in act.actions.iter().enumerate() {
            for out in &tmpl.outputs {
                let entry = DepOutput { exec_path: out.clone(), producer_ct: dep_ct_key.clone(), action_index: idx as u32 };
                if let Err(e) = merge_dep_output(&mut dep_outputs, entry, ctk) {
                    return ComputeResult::Error(e);
                }
            }
        }
        for d in &act.dep_outputs {
            if let Err(e) = merge_dep_output(&mut dep_outputs, d.clone(), ctk) {
                return ComputeResult::Error(e);
            }
        }
        ComputeResult::Ready(Arc::new(ConfiguredTarget { providers, actions: Vec::new(), dep_outputs, visibility }))
    }
}

impl NodeFunction for ConfiguredTargetFn {
    fn compute(&self, key: &NodeKey, ctx: &mut dyn DemandContext) -> ComputeResult {
        let ctk = match decode_ct_key(key.canonical()) {
            Ok(k) => k,
            Err(e) => return ComputeResult::Error(e),
        };

        // (1) the target's declaration from its package.
        let pkg_key = NodeKey::from_key(&PackageKey(RootRelativePath(ctk.package.clone())));
        let pv = match ctx.request(&pkg_key) {
            Demand::Missing => return ComputeResult::Missing { recorded_dep_keys: vec![pkg_key] },
            Demand::Ready(v) => v,
        };
        let package = match pv.as_any().downcast_ref::<Package>() {
            Some(p) => p,
            None => return ComputeResult::Error(Error::Invalid { what: "PACKAGE value".into(), detail: "not a Package".into() }),
        };
        let target = match package.get(&ctk.name) {
            Some(t) => t.clone(),
            None => return ComputeResult::Error(Error::NotFound { what: "target".into(), detail: format!("//{}:{}", ctk.package, ctk.name) }),
        };
        // (1b) `alias` — a native forwarding target (kind = "alias", no rule origin). It re-publishes the
        // `actual` target's providers VERBATIM and threads its dep-output chaining, so a dependent sees
        // `actual` exactly as if it depended on it directly (Bazel's alias). Language-agnostic — it forwards
        // WHATEVER providers `actual` published (nothing here assumes rust). Handled BEFORE the rule-origin
        // check: an alias has no impl to run.
        if target.kind == "alias" {
            return self.compute_alias(&ctk, &target, ctx);
        }
        // (1c) `config_setting` — a native decl (kind = "config_setting", no rule origin). Its CT carries a
        // `ConfigMatchInfo` (match/no-match against the resolving configuration's constraint set + values) that
        // a select() reads. Handled BEFORE the rule-origin check (no impl to run), like alias.
        if target.kind == "config_setting" {
            return match select::compute_config_match(&ctk, &target, &self.select_config) {
                Ok(ct) => ComputeResult::Ready(Arc::new(ct)),
                Err(e) => ComputeResult::Error(e),
            };
        }
        // (1d) Resolve any `select()`-valued attrs against the target's configuration (T20 select) BEFORE dep
        // resolution / rule eval — restart-driven over the referenced `config_setting` CTs. A target with no
        // select is byte-identical (empty request set); the resolved attrs replace the raw selector.
        let target = match select::resolve_target_selects(&ctk, target, &self.repos, ctx) {
            select::SelectResolution::Ready(t) => t,
            select::SelectResolution::Missing(keys) => return ComputeResult::Missing { recorded_dep_keys: keys },
            select::SelectResolution::Error(e) => return ComputeResult::Error(e),
        };
        // (2) the rule origin — a generic target() placeholder has none, and there is no impl to run: fail closed.
        let origin = match &target.origin {
            Some(o) => o.clone(),
            None => return ComputeResult::Error(Error::Unsupported {
                what: "analyze a target with no rule definition",
                detail: format!("//{}:{} was not instantiated by a rule()", ctk.package, ctk.name),
            }),
        };
        // This target's own visibility (C7) — carried on the CT value so DEPENDENTS enforce the edge.
        let visibility = target_visibility(&target);
        let parent_label = render_label(&ctk.package, &ctk.name);

        // (3a) depend on the rule .bzl's CONTENT for invalidation. BZL_LOAD alone is NOT enough: its value is
        // the RuleDef (schema), which drops the impl — so an impl-only edit would cut off there and serve STALE
        // providers. FILE's content digest catches an impl change (the source is re-evaluated below).
        // (MUTANT: dropping this dep makes an impl-only edit invisible → stale analysis.)
        if !cfg!(feature = "mutant_ct_skips_rule_file_dep") {
            let rule_file_key = NodeKey::from_key(&FileKey(RootRelativePath(origin.bzl.clone())));
            let rfv = match ctx.request(&rule_file_key) {
                Demand::Missing => return ComputeResult::Missing { recorded_dep_keys: vec![rule_file_key] },
                Demand::Ready(v) => v,
            };
            match rfv.as_any().downcast_ref::<FileValue>() {
                Some(f) if f.exists => {}
                Some(_) => return ComputeResult::Error(Error::NotFound { what: "rule .bzl".into(), detail: origin.bzl.clone() }),
                None => return ComputeResult::Error(Error::Invalid { what: "FILE value".into(), detail: "rule .bzl dep was not a FileValue".into() }),
            }
        }

        // (3b) the rule's attribute schema (to identify label-typed deps) via BZL_LOAD of its .bzl —
        // requested under the SAME row-1 contract key the loading phase uses (Build{is_prelude:false},
        // v1 semantics row, evaluator-served env id), so the module node is shared, never re-keyed.
        let bzl_key = match BzlLoadKey::v1(RootRelativePath(origin.bzl.clone()), self.eval.as_ref()) {
            Ok(k) => NodeKey::from_key(&k),
            Err(e) => return ComputeResult::Error(e),
        };
        let bm = match ctx.request(&bzl_key) {
            Demand::Missing => return ComputeResult::Missing { recorded_dep_keys: vec![bzl_key] },
            Demand::Ready(v) => v,
        };
        let module = match bm.as_any().downcast_ref::<BzlModuleValue>() {
            Some(m) => &m.0,
            None => return ComputeResult::Error(Error::Invalid { what: "BZL_LOAD value".into(), detail: "not a BzlModuleValue".into() }),
        };
        let (schema, required_toolchains) = match module.get(&origin.name) {
            Some(BzlValue::Rule(rd)) => (rd.attrs.clone(), rd.toolchains.clone()),
            _ => return ComputeResult::Error(Error::Invalid {
                what: "rule definition".into(),
                detail: format!("'{}' is not a rule in {}", origin.name, origin.bzl),
            }),
        };

        // (4) resolve label-typed attrs to CONFIGURED_TARGET(dep) nodes (config threaded into each child).
        let mut dep_keys: Vec<NodeKey> = Vec::new();
        let mut dep_labels: Vec<String> = Vec::new();
        for (aname, aty) in &schema {
            if !aty.is_label() {
                continue;
            }
            let Some((_, val)) = target.attrs.iter().find(|(n, _)| n == aname) else { continue };
            let labels: Vec<String> = match val {
                BzlValue::List(items) => {
                    items.iter().filter_map(|i| if let BzlValue::Str(s) = i { Some(s.clone()) } else { None }).collect()
                }
                BzlValue::Str(s) => vec![s.clone()],
                _ => Vec::new(),
            };
            for lbl in labels {
                match resolve_dep(&ctk, &lbl, &self.repos) {
                    Ok(k) => {
                        dep_keys.push(k);
                        dep_labels.push(lbl);
                    }
                    Err(e) => return ComputeResult::Error(e),
                }
            }
        }

        // (5) request the dep configured-targets (restart-driven) and collect their providers AND their
        // declared outputs (the files-chaining map: each dep output → its producing action). The dep CT
        // value already carries {providers, actions}; the same fetch feeds both.
        let demands = ctx.request_group(&dep_keys);
        let mut missing: Vec<NodeKey> = Vec::new();
        let mut dep_providers: Vec<DepProviders> = Vec::new();
        let mut dep_outputs: Vec<DepOutput> = Vec::new();
        for (i, d) in demands.into_iter().enumerate() {
            match d {
                Demand::Missing => missing.push(dep_keys[i].clone()),
                Demand::Ready(v) => match v.as_any().downcast_ref::<ConfiguredTarget>() {
                    Some(ct) => {
                        // The dep CT key (decode is total on our own encode) — used for the visibility check
                        // AND the files-chaining below (decoded ONCE).
                        let dep_ct_key = match decode_ct_key(dep_keys[i].canonical()) {
                            Ok(k) => k,
                            Err(e) => return ComputeResult::Error(e),
                        };
                        // (C7) enforce the cross-package visibility edge BEFORE consuming the dep — a private
                        // cross-package dep is a typed analysis error. RED under `mutant_visibility_ignored`.
                        if let Err(e) = check_visibility(&ctk.package, &dep_ct_key.package, &parent_label, &dep_labels[i], &ct.visibility) {
                            return ComputeResult::Error(e);
                        }
                        dep_providers.push(DepProviders { label: dep_labels[i].clone(), providers: ct.providers.clone() });
                        // files-chaining (MUTANT `mutant_chain_drops_dep_files` drops the whole map → a dep's
                        // declared output named as a dependent action input can no longer resolve to its
                        // producer; it falls through to Source, the file is absent on disk, and the build
                        // fails closed — the granular re-run edge is also severed). The dep CT key is the one
                        // we requested (decode is total on our own encode); a duplicate exec-path from two
                        // DISTINCT producers is a typed Conflict (fail-closed, never a silent first-wins).
                        if !cfg!(feature = "mutant_chain_drops_dep_files") {
                            // (a) the dep's OWN declared action outputs → {this dep CT, action idx}.
                            for (idx, tmpl) in ct.actions.iter().enumerate() {
                                for out in &tmpl.outputs {
                                    let entry = DepOutput {
                                        exec_path: out.clone(),
                                        producer_ct: dep_ct_key.clone(),
                                        action_index: idx as u32,
                                    };
                                    if let Err(e) = merge_dep_output(&mut dep_outputs, entry, &ctk) {
                                        return ComputeResult::Error(e);
                                    }
                                }
                            }
                            // (b) the TRANSITIVE closure: merge the dep's OWN (already-transitive) dep_outputs.
                            // Each dep CT was computed by THIS same function, so its `dep_outputs` is ITS full
                            // transitive closure; merging every direct dep's closure gives the parent the whole
                            // graph's producer map (values-only, same digest frame — the map rides the CT VALUE,
                            // no key reshape). The producer_ct is carried VERBATIM: it names the TRUE producing
                            // analysis node (a dep-of-dep), never the intermediary — so a rustc `-L`/`--extern`
                            // input that names a dep-of-dep rlib resolves to its real generating ACTION, and a
                            // diamond (one crate reached via two paths) dedups on identical (producer, idx)
                            // rather than false-conflicting.
                            // MUTANT `mutant_transitive_outputs_not_merged`: drop this merge → a dep-of-dep rlib
                            // a dependent action lists as an input can no longer resolve to a producer; it falls
                            // through to Source, the derived file is absent on disk, and the multi-crate chain
                            // fails closed (typed NotFound) — the rust self-host chain proof goes RED.
                            if !cfg!(feature = "mutant_transitive_outputs_not_merged") {
                                for d in &ct.dep_outputs {
                                    if let Err(e) = merge_dep_output(&mut dep_outputs, d.clone(), &ctk) {
                                        return ComputeResult::Error(e);
                                    }
                                }
                            }
                        }
                    }
                    None => return ComputeResult::Error(Error::Invalid { what: "CONFIGURED_TARGET dep".into(), detail: "not a ConfiguredTarget".into() }),
                },
            }
        }

        // (5b) resolve the rule's required toolchains via ONE TOOLCHAIN_CONTEXT node carrying the FULL
        // required type-set (all mandatory in v1 — `rule(toolchains=[…])` has no optional marker yet),
        // keyed by the target's CONFIGURATION (the ADR-0010 lockdown: the target platform is DERIVED from
        // the configuration inside the toolchain node, never passed as a platform-string key). Restart-
        // driven; the resolved map is threaded into evaluate_rule as ctx.toolchains. FAIL-CLOSED: a
        // toolchain-requiring target with no configuration cannot be resolved — error rather than coerce a
        // missing config to a default (that would be an Absorb). A target that requires no toolchains skips
        // this entirely (its configuration may legitimately be None in v1).
        let mut toolchains: Vec<ResolvedToolchain> = Vec::new();
        if !required_toolchains.is_empty() {
            let configuration = match &ctk.configuration {
                Some(c) => ConfigId(c.clone()),
                // MUTANT: absorb a missing configuration into the empty ConfigId "" (anti-corner (II) regresses).
                None if cfg!(feature = "mutant_ct_absorbs_missing_config") => ConfigId(String::new()),
                None => {
                    return ComputeResult::Error(Error::Unsupported {
                        what: "toolchain resolution",
                        detail: format!(
                            "target '{}:{}' requires toolchains {:?} but has no configuration",
                            ctk.package, ctk.name, required_toolchains
                        ),
                    })
                }
            };
            let tc_key = NodeKey::from_key(&ToolchainContextKey::new(
                configuration,
                required_toolchains
                    .iter()
                    .map(|ty| ToolchainTypeReq { toolchain_type: ToolchainType(ty.clone()), mandatory: true })
                    .collect(),
                Vec::new(), // exec constraints: none in v1 (rule exec_compatible_with is deferred)
                None,       // force_exec_platform: the fixed v1 sentinel
                false,      // debug_target: false in v1
            ));
            match ctx.request(&tc_key) {
                Demand::Missing => missing.push(tc_key),
                Demand::Ready(v) => match v.as_any().downcast_ref::<ResolvedToolchainContextValue>() {
                    Some(rctx) => {
                        for ty in &required_toolchains {
                            match rctx.type_to_resolved.get(&ToolchainType(ty.clone())) {
                                Some(info) => toolchains
                                    .push(ResolvedToolchain { toolchain_type: ty.clone(), info: info.clone() }),
                                // Mandatory ⇒ present (the toolchain node fails closed upstream); a hole here
                                // is a broken invariant — typed error, never an empty ctx.toolchains slot.
                                None => {
                                    return ComputeResult::Error(Error::Invalid {
                                        what: "TOOLCHAIN_CONTEXT value".into(),
                                        detail: format!("mandatory toolchain type '{ty}' absent from the resolved context"),
                                    })
                                }
                            }
                        }
                    }
                    None => {
                        return ComputeResult::Error(Error::Invalid {
                            what: "TOOLCHAIN_CONTEXT dep".into(),
                            detail: "not a ResolvedToolchainContextValue".into(),
                        })
                    }
                },
            }
        }

        if !missing.is_empty() {
            return ComputeResult::Missing { recorded_dep_keys: missing };
        }

        // (6) read the rule's .bzl source (for the transient re-eval inside the seam). The rule .bzl is a
        // main-repo-absolute path even for an external target's rule (the overlay loads `//rules/rust:...`),
        // so this resolves against the workspace root — `resolve_source_path` is the uniform read choke point.
        let bzl_host = match resolve_source_path(&self.root, &self.repos, &RootRelativePath(origin.bzl.clone())) {
            Ok(h) => h,
            Err(e) => return ComputeResult::Error(e),
        };
        let source = match self.sys.read(&bzl_host) {
            Ok(b) => match String::from_utf8(b) {
                Ok(s) => s,
                Err(_) => return ComputeResult::Error(Error::Invalid { what: "rule .bzl".into(), detail: "non-utf8".into() }),
            },
            Err(e) => return ComputeResult::Error(Error::Invalid { what: "read rule .bzl".into(), detail: format!("{e:?}") }),
        };

        // (6b) THREAD the rule .bzl's DIRECT `load()`s into evaluate_rule (row-6-adjacent analysis infra). The
        // rule impl (`external/rules_rust/rust/private/rust.bzl`) `load()`s ~20 sibling modules; the seam
        // re-evaluates the source, so each DIRECT load target must be supplied as an already-evaluated
        // `BzlModule`. Each direct load is resolved (in the rule's OWN repo context — row 3) to its exec path,
        // then requested as a BZL_LOAD node (which self-resolves ITS transitive closure) keyed under the load
        // target's OWN repo context. A SELF-CONTAINED rule .bzl (our rust.bzl — no loads) yields an empty
        // `loaded`, byte-identical to before. Restart-driven: an unresolved load node re-queues.
        let rule_repo = repo_context_of(&origin.bzl);
        let load_targets = match self.eval.load_targets(&source) {
            Ok(t) => t,
            Err(e) => return ComputeResult::Error(Error::Invalid { what: "rule .bzl load scan".into(), detail: format!("{e:?}") }),
        };
        let mut loaded_mods: Vec<(String, BzlModule)> = Vec::new();
        let mut load_missing: Vec<NodeKey> = Vec::new();
        for target in &load_targets {
            let resolved = match resolve_load(&self.repos, rule_repo.as_deref(), &RootRelativePath(origin.bzl.clone()), target) {
                Ok(p) => p,
                Err(e) => return ComputeResult::Error(e),
            };
            let load_ctx = repo_context_of(&resolved.0);
            let key = match BzlLoadKey::for_kind_in_context(resolved, LoadKind::Build { is_prelude: false }, load_ctx, self.eval.as_ref()) {
                Ok(k) => NodeKey::from_key(&k),
                Err(e) => return ComputeResult::Error(e),
            };
            match ctx.request(&key) {
                Demand::Missing => load_missing.push(key),
                Demand::Ready(v) => match v.as_any().downcast_ref::<BzlModuleValue>() {
                    Some(m) => loaded_mods.push((target.clone(), m.0.clone())),
                    None => return ComputeResult::Error(Error::Invalid { what: "BZL_LOAD value".into(), detail: format!("load '{target}' of {} was not a BzlModuleValue", origin.bzl) }),
                },
            }
        }
        if !load_missing.is_empty() {
            return ComputeResult::Missing { recorded_dep_keys: load_missing };
        }

        // (7) run the rule impl → providers (+ actions, consumed by the execution phase #5 — ignored for now),
        // with the resolved toolchains threaded in (ctx.toolchains[type]).
        // MUTANT: drop the resolved toolchains → ctx.toolchains is empty → a rule that reads one fails (G4 red).
        let tc_arg: &[ResolvedToolchain] = if cfg!(feature = "mutant_ct_drops_toolchains") { &[] } else { &toolchains };
        // `parent_label` (computed above, repo-aware per D1: `@<repo>//<pkg>:<name>` external, `//<pkg>:<name>`
        // internal) is the ctx.label the rule impl sees (C1 turns it into a Label object) AND the "from" side
        // of the visibility edges enforced above.
        // The analysis re-eval runs in the SAME row-1 env the rule's .bzl was loaded in (phase-env §3).
        let env = EvalEnv::build_bzl_v1();
        match self.eval.evaluate_rule(&env, &source, &origin.bzl, &origin.name, &loaded_mods, &parent_label, &target.attrs, &dep_providers, tc_arg) {
            Ok(result) => ComputeResult::Ready(Arc::new(ConfiguredTarget {
                providers: result.providers,
                actions: result.actions,
                dep_outputs,
                visibility,
            })),
            Err(e) => ComputeResult::Error(Error::Invalid { what: "rule evaluation".into(), detail: format!("{e:?}") }),
        }
    }
}

/// Register `CONFIGURED_TARGET` over `sys`/`root` with the given evaluator. The composition root supplies impls
/// AND the `select_config` (T20 select: the per-configuration constraint set + values the host injects for
/// `select()`/`config_setting` resolution; empty is byte-identical to the pre-select analysis).
pub fn register_analysis_kinds(
    engine: &mut dyn DemandEngine,
    sys: Arc<dyn System>,
    root: HostPath,
    eval: Arc<dyn BzlEvaluator>,
    repos: ExternalRepos,
    select_config: SelectConfig,
) {
    engine.register(
        CONFIGURED_TARGET,
        Box::new(ConfiguredTargetFn::new_with_repos_and_select(sys, root, eval, repos, select_config)),
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use razel_source::ExternalRepo;

    fn ckey(pkg: &str, name: &str, cfg: Option<&str>) -> ConfiguredTargetKey {
        ConfiguredTargetKey {
            package: pkg.into(),
            name: name.into(),
            configuration: cfg.map(|s| s.into()),
            exec_platform: None,
            rule_transition: None,
        }
    }

    #[test]
    fn ct_key_round_trips() {
        let k = ckey("pkg/sub", "lib", Some("opt"));
        assert_eq!(decode_ct_key(&k.encode()).unwrap(), k, "the key must survive encode → decode");
    }

    #[test]
    fn config_dimension_is_in_the_key() {
        // Anti-corner (I): the configuration dimension is part of identity from commit #1 — two targets that
        // differ ONLY in configuration are DISTINCT keys (so adding real configs later is additive, not a re-key).
        let a = ckey("pkg", "t", Some("a"));
        let b = ckey("pkg", "t", Some("b"));
        let none = ckey("pkg", "t", None);
        assert_ne!(a.encode(), b.encode(), "configs 'a' vs 'b' must be distinct keys");
        assert_ne!(a.encode(), none.encode(), "a config vs no config must be distinct keys");
    }

    #[test]
    fn cross_package_visibility_enforced() {
        // C7/D7: same-package edges always visible; cross-package needs `//visibility:public`; a private
        // (default) cross-package dep is a typed error naming both; an unknown form fails closed. RED under
        // `mutant_visibility_ignored` (which allows the private cross-package edge).
        assert!(check_visibility("a", "a", "//a:t", "//a:dep", &[]).is_ok(), "same-package edge is always visible");
        assert!(
            check_visibility("a", "b", "//a:t", "//b:dep", &["//visibility:public".into()]).is_ok(),
            "a public cross-package edge is visible"
        );
        assert!(
            matches!(check_visibility("a", "b", "//a:t", "//b:dep", &[]), Err(Error::Invalid { .. })),
            "a PRIVATE (default) cross-package dep is a typed error — RED under mutant_visibility_ignored"
        );
        assert!(
            check_visibility("a", "b", "//a:t", "//b:dep", &["//visibility:private".into()]).is_err(),
            "an explicitly-private cross-package dep also fails closed"
        );
        assert!(
            matches!(check_visibility("a", "b", "//a:t", "//b:dep", &["//c:__pkg__".into()]), Err(Error::Unsupported { .. })),
            "an unknown visibility form (package group / __pkg__) fails closed — deferred, never silently allowed"
        );
    }

    #[test]
    fn dep_key_threads_parent_config() {
        // Anti-corner (III): the parent's configuration is THREADED into a dependency's key (identity transform
        // now; a real transition slots in here later). `mutant_ct_drops_config` regresses this → test goes red.
        let parent = ckey("pkg", "root", Some("cfg-1"));
        let dep = resolve_dep(&parent, ":leaf", &ExternalRepos::empty()).expect("same-package dep resolves");
        let child = decode_ct_key(dep.canonical()).unwrap();
        assert_eq!(child.package, "pkg");
        assert_eq!(child.name, "leaf");
        assert_eq!(child.configuration, Some("cfg-1".to_string()), "the dependency inherits the parent's configuration");
    }

    #[test]
    fn dep_label_forms_fail_closed() {
        let parent = ckey("pkg", "t", None);
        let none = ExternalRepos::empty();
        assert!(resolve_dep(&parent, ":a", &none).is_ok(), "':name' resolves (same package)");
        assert!(resolve_dep(&parent, "//other:b", &none).is_ok(), "'//pkg:name' resolves (absolute)");
        assert!(resolve_dep(&parent, "bare", &none).is_err(), "a bare name must fail closed");
        // T17 external roots (D1): a DECLARED repo resolves; an UNDECLARED repo stays a typed error — the pinned
        // rejection flips to a positive test that STILL fails closed for undeclared repos (never a fallback).
        assert!(
            resolve_dep(&parent, "@shape//x:y", &none).is_err(),
            "an UNDECLARED repo label must fail closed (no workspace fallback)"
        );
        let declared = ExternalRepos::from_pairs([(
            "shape".to_string(),
            ExternalRepo { root: HostPath::new("/ext/shape"), build_file: Some(RootRelativePath("third-party/shape/BUILD.bazel".to_string())) },
        )]);
        let dep = resolve_dep(&parent, "@shape//x:y", &declared).expect("a DECLARED repo label resolves");
        let ct = decode_ct_key(dep.canonical()).unwrap();
        assert_eq!(ct.package, "@shape//x", "canonical D1 package text carries the repo marker");
        assert_eq!(ct.name, "y");
    }

    #[test]
    fn external_and_internal_same_suffix_packages_are_distinct_cts() {
        // D1 distinct-identity law (guards `mutant_repo_prefix_stripped_from_package`): an external package
        // `@shape//foo` and an internal package `foo` (colliding suffix) must produce DISTINCT CT identities
        // (distinct package strings → distinct encoded keys). Under the mutant the `@shape//` marker is
        // dropped, the two collide, and this goes RED.
        let parent = ckey("razel-core", "root", None);
        let repos = ExternalRepos::from_pairs([(
            "shape".to_string(),
            ExternalRepo { root: HostPath::new("/ext/shape"), build_file: Some(RootRelativePath("third-party/shape/BUILD.bazel".to_string())) },
        )]);
        let ext = decode_ct_key(resolve_dep(&parent, "@shape//foo:t", &repos).unwrap().canonical()).unwrap();
        let int = decode_ct_key(resolve_dep(&parent, "//foo:t", &repos).unwrap().canonical()).unwrap();
        assert_eq!(int.package, "foo", "internal package is the bare pkg-rel");
        assert_ne!(ext.package, int.package, "external and internal same-suffix packages are DISTINCT (not collapsed)");
        assert_ne!(
            ext.encode(),
            int.encode(),
            "distinct CT identities → distinct encoded keys (distinct artifacts); the mutant collapses them"
        );
    }
}
