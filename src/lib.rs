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
    encode_provider_instance, ActionTemplate, BzlEvaluator, BzlValue, DepProviders, EvalEnv, ProviderId,
    ProviderInstance, ResolvedToolchain,
};
use razel_toolchain::{ResolvedToolchainContextValue, ToolchainContextKey, ToolchainType, ToolchainTypeReq};
use razel_core::{Digest, Error, Key, KindId, NodeKey, Value, ValuePolicy};
use razel_engine_api::{ComputeResult, Demand, DemandContext, DemandEngine, NodeFunction};
use razel_ids::{ConfigId, RootRelativePath};
use razel_load::{BzlLoadKey, BzlModuleValue};
use razel_os_api::{HostPath, System};
use razel_package::{Package, PackageKey};
use razel_source::{join_root, FileKey, FileValue};
use std::any::Any;
use std::sync::Arc;

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

/// Resolve a dependency label string to a `CONFIGURED_TARGET` key, threading the PARENT's configuration into
/// the child (an identity transform in v1 — a real rule/configuration transition slots in here later, additive).
/// SPIKE: `":name"` (same package) and `"//pkg:name"` (absolute). Other forms fail closed (never mis-resolved).
fn resolve_dep(parent: &ConfiguredTargetKey, lbl: &str) -> Result<NodeKey, Error> {
    let (package, name) = if let Some(rest) = lbl.strip_prefix("//") {
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
        return Err(Error::Unsupported { what: "dep label form", detail: format!("expected ':name' or '//pkg:name', got '{lbl}'") });
    };
    // MUTANT: dropping the parent's configuration here regresses anti-corner (III) (config not threaded).
    let (configuration, exec_platform, rule_transition) = if cfg!(feature = "mutant_ct_drops_config") {
        (None, None, None)
    } else {
        (parent.configuration.clone(), parent.exec_platform.clone(), parent.rule_transition.clone())
    };
    Ok(NodeKey::from_key(&ConfiguredTargetKey { package, name, configuration, exec_platform, rule_transition }))
}

/// `CONFIGURED_TARGET`: analyze one target — resolve its deps, then run its rule's impl → providers.
pub struct ConfiguredTargetFn {
    sys: Arc<dyn System>,
    root: HostPath,
    eval: Arc<dyn BzlEvaluator>,
}
impl ConfiguredTargetFn {
    pub fn new(sys: Arc<dyn System>, root: HostPath, eval: Arc<dyn BzlEvaluator>) -> Self {
        Self { sys, root, eval }
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
        // (2) the rule origin — a generic target() placeholder has none, and there is no impl to run: fail closed.
        let origin = match &target.origin {
            Some(o) => o.clone(),
            None => return ComputeResult::Error(Error::Unsupported {
                what: "analyze a target with no rule definition",
                detail: format!("//{}:{} was not instantiated by a rule()", ctk.package, ctk.name),
            }),
        };

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
                match resolve_dep(&ctk, &lbl) {
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
                        dep_providers.push(DepProviders { label: dep_labels[i].clone(), providers: ct.providers.clone() });
                        // files-chaining (MUTANT `mutant_chain_drops_dep_files` drops the whole map → a dep's
                        // declared output named as a dependent action input can no longer resolve to its
                        // producer; it falls through to Source, the file is absent on disk, and the build
                        // fails closed — the granular re-run edge is also severed). The dep CT key is the one
                        // we requested (decode is total on our own encode); a duplicate exec-path from two
                        // DISTINCT producers is a typed Conflict (fail-closed, never a silent first-wins).
                        if !cfg!(feature = "mutant_chain_drops_dep_files") {
                            let dep_ct_key = match decode_ct_key(dep_keys[i].canonical()) {
                                Ok(k) => k,
                                Err(e) => return ComputeResult::Error(e),
                            };
                            for (idx, tmpl) in ct.actions.iter().enumerate() {
                                for out in &tmpl.outputs {
                                    if let Some(prev) = dep_outputs.iter().find(|d| &d.exec_path == out) {
                                        if prev.producer_ct != dep_ct_key || prev.action_index != idx as u32 {
                                            return ComputeResult::Error(Error::Conflict {
                                                what: "duplicate dep output".into(),
                                                detail: format!(
                                                    "//{}:{}: dep output '{}' is produced by two distinct dependencies",
                                                    ctk.package, ctk.name, out
                                                ),
                                            });
                                        }
                                        continue;
                                    }
                                    dep_outputs.push(DepOutput {
                                        exec_path: out.clone(),
                                        producer_ct: dep_ct_key.clone(),
                                        action_index: idx as u32,
                                    });
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

        // (6) read the rule's .bzl source (for the transient re-eval inside the seam).
        let source = match self.sys.read(&join_root(&self.root, &RootRelativePath(origin.bzl.clone()))) {
            Ok(b) => match String::from_utf8(b) {
                Ok(s) => s,
                Err(_) => return ComputeResult::Error(Error::Invalid { what: "rule .bzl".into(), detail: "non-utf8".into() }),
            },
            Err(e) => return ComputeResult::Error(Error::Invalid { what: "read rule .bzl".into(), detail: format!("{e:?}") }),
        };

        // (7) run the rule impl → providers (+ actions, consumed by the execution phase #5 — ignored for now),
        // with the resolved toolchains threaded in (ctx.toolchains[type]).
        // MUTANT: drop the resolved toolchains → ctx.toolchains is empty → a rule that reads one fails (G4 red).
        let tc_arg: &[ResolvedToolchain] = if cfg!(feature = "mutant_ct_drops_toolchains") { &[] } else { &toolchains };
        let label = format!("//{}:{}", ctk.package, ctk.name);
        // The analysis re-eval runs in the SAME row-1 env the rule's .bzl was loaded in (phase-env §3).
        let env = EvalEnv::build_bzl_v1();
        match self.eval.evaluate_rule(&env, &source, &origin.bzl, &origin.name, &[], &label, &target.attrs, &dep_providers, tc_arg) {
            Ok(result) => ComputeResult::Ready(Arc::new(ConfiguredTarget {
                providers: result.providers,
                actions: result.actions,
                dep_outputs,
            })),
            Err(e) => ComputeResult::Error(Error::Invalid { what: "rule evaluation".into(), detail: format!("{e:?}") }),
        }
    }
}

/// Register `CONFIGURED_TARGET` over `sys`/`root` with the given evaluator. The composition root supplies impls.
pub fn register_analysis_kinds(
    engine: &mut dyn DemandEngine,
    sys: Arc<dyn System>,
    root: HostPath,
    eval: Arc<dyn BzlEvaluator>,
) {
    engine.register(CONFIGURED_TARGET, Box::new(ConfiguredTargetFn::new(sys, root, eval)));
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn dep_key_threads_parent_config() {
        // Anti-corner (III): the parent's configuration is THREADED into a dependency's key (identity transform
        // now; a real transition slots in here later). `mutant_ct_drops_config` regresses this → test goes red.
        let parent = ckey("pkg", "root", Some("cfg-1"));
        let dep = resolve_dep(&parent, ":leaf").expect("same-package dep resolves");
        let child = decode_ct_key(dep.canonical()).unwrap();
        assert_eq!(child.package, "pkg");
        assert_eq!(child.name, "leaf");
        assert_eq!(child.configuration, Some("cfg-1".to_string()), "the dependency inherits the parent's configuration");
    }

    #[test]
    fn dep_label_forms_fail_closed() {
        let parent = ckey("pkg", "t", None);
        assert!(resolve_dep(&parent, ":a").is_ok(), "':name' resolves (same package)");
        assert!(resolve_dep(&parent, "//other:b").is_ok(), "'//pkg:name' resolves (absolute)");
        assert!(resolve_dep(&parent, "bare").is_err(), "a bare name must fail closed");
        assert!(resolve_dep(&parent, "@repo//x:y").is_err(), "a repo label must fail closed (unsupported)");
    }
}
