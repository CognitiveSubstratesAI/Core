# LangDefPack.jl — reflectable, rule-indexed description of the coarse HE one-step relation.
#
# Adopted from CeTTa's `langdef_pack.{c,h}` + `he_small_step_pack.c`: rules are DATA
# (name, id, profiles, provenance, claim, live), with a content-addressed FNV-1a64 digest over the
# rule *semantics* (claim levels EXCLUDED — "evidence about rules, not rule content"), an env-driven
# disabled mask, a `rule_enabled` predicate, and a `(step-rules …)` reflection atom.
#
# PRIMUS-native (NOT a 1:1 port): pure Julia data + the same FNV recipe (UInt64 wraps mod 2^64 like
# C uint64_t), so the digest is byte-identical to CeTTa's for the same table — a built-in cross-check.
# The rule table is adopted VERBATIM from CeTTa (it describes the shared HE small-step relation, not a
# CeTTa-specific thing); PRIMUS's implementing locations are in comments. Claim levels cite the Lean
# mettaHE theorems that justify each rule of the HE relation PRIMUS's interpreter is conformance-tested
# (234/234) to implement. The disable-to-prove WELDING into `Eval.jl`'s dispatch is a separate
# follow-on (it touches the conformance-critical hot path); this slice is the data + reflection layer.

@enum LangDefRuleId begin
    HES_GROUNDED_DISPATCH = 0
    HES_LEFTMOST_EXPR_CONGRUENCE
    HES_EQUATION_MATCH
    HES_EVAL
    HES_CHAIN
    HES_LET
    HES_LET_STAR
    HES_CASE
    HES_SWITCH
    HES_SWITCH_MINIMAL
    HES_QUOTE_QUIESCENT
    HES_RETURN_QUIESCENT
    HES_EMPTY_QUIESCENT
    HES_ERROR_QUIESCENT
end

struct LangDefRule
    name::String
    rule_id::LangDefRuleId
    profiles::String
    provenance::String   # fine-machine / Lean rules justifying this coarse rule
    claim::String        # epistemic level (excluded from digest)
    live::Bool           # live rules gate an executable branch; non-live = structural metadata
end

# The HE small-step rule table — adopted verbatim from CeTTa he_small_step_pack.c.
# (PRIMUS impl: GroundedDispatch=is_executable/interpret grounded; EquationMatch=interpret_function rule
#  match; Eval/Chain/Let/LetStar/Case/Switch=the special-form dispatch in standard/Eval.jl.)
const HE_SMALL_STEP_RULES = LangDefRule[
    LangDefRule(
        "HES_GroundedDispatch",
        HES_GROUNDED_DISPATCH,
        "he he-extended",
        "M_Expression IE_FuncType IF_* MC_Grounded",
        "rule-sound",
        true
    ),
    LangDefRule(
        "HES_LeftmostExprCongruence",
        HES_LEFTMOST_EXPR_CONGRUENCE,
        "he he-extended",
        "IA_Start_* M_Expression IE_* IF_*",
        "rule-sound-on-fragment",
        true
    ),
    LangDefRule(
        "HES_EquationMatch",
        HES_EQUATION_MATCH,
        "he he-extended",
        "MC_Equation",
        "rule-sound",
        true
    ),
    LangDefRule("HES_Eval", HES_EVAL, "he he-extended", "minimal.eval", "rule-sound", true),
    LangDefRule(
        "HES_Chain",
        HES_CHAIN,
        "he he-extended",
        "minimal.chain (incl. arity error)",
        "rule-sound-on-fragment",
        true
    ),
    LangDefRule(
        "HES_Let",
        HES_LET,
        "he he-extended",
        "minimal.let (chain/unify sugar)",
        "bag-tested-adequate",
        true
    ),
    LangDefRule(
        "HES_LetStar",
        HES_LET_STAR,
        "he he-extended",
        "minimal.let* (nested let sugar)",
        "bag-tested-adequate",
        true
    ),
    LangDefRule(
        "HES_Case",
        HES_CASE,
        "he he-extended",
        "minimal.case (incl. arity error)",
        "bag-tested-adequate",
        true
    ),
    LangDefRule(
        "HES_Switch",
        HES_SWITCH,
        "he he-extended",
        "stdlib.switch (evaluated scrutinee; incl. arity error)",
        "bag-tested-adequate",
        true
    ),
    LangDefRule(
        "HES_SwitchMinimal",
        HES_SWITCH_MINIMAL,
        "he he-extended",
        "stdlib.switch-minimal (structural; incl. arity error)",
        "bag-tested-adequate",
        true
    ),
    LangDefRule(
        "HES_QuoteQuiescent",
        HES_QUOTE_QUIESCENT,
        "he he-extended",
        "M_SymbolOrGrounded (quote surface)",
        "bag-tested-adequate",
        false
    ),
    LangDefRule(
        "HES_ReturnQuiescent",
        HES_RETURN_QUIESCENT,
        "he he-extended",
        "IF_AfterArgs_Call return surface",
        "bag-tested-adequate",
        false
    ),
    LangDefRule(
        "HES_EmptyQuiescent",
        HES_EMPTY_QUIESCENT,
        "he he-extended",
        "M_Empty",
        "bag-tested-adequate",
        false
    ),
    LangDefRule(
        "HES_ErrorQuiescent",
        HES_ERROR_QUIESCENT,
        "he he-extended",
        "M_Error",
        "bag-tested-adequate",
        false
    )
]

struct LangDefPack
    language_id::String
    profile_id::String
    granularity::String
    schema_version::UInt32
    rules::Vector{LangDefRule}
    source_digest::UInt64
    disabled_mask::UInt32
end

# ── FNV-1a64 over the canonical rule-descriptor text (mirrors langdef_pack.c exactly) ──
const _FNV_OFFSET = 0xcbf29ce484222325
const _FNV_PRIME = 0x00000100000001b3
function _fnv_field(h::UInt64, s::AbstractString)::UInt64
    for b in codeunits(s)
        h = (h ⊻ UInt64(b)) * _FNV_PRIME      # UInt64 * wraps mod 2^64 like C uint64_t
    end
    (h ⊻ 0x1f) * _FNV_PRIME                    # field separator (langdef_pack.c)
end
_fnv_u32(h::UInt64, v::Integer)::UInt64 = _fnv_field(h, string(UInt32(v)))

function langdef_digest(language_id, profile_id, granularity, schema_version::Integer,
    rules::Vector{LangDefRule})::UInt64
    h = _FNV_OFFSET
    h = _fnv_field(h, language_id)
    h = _fnv_field(h, profile_id)
    h = _fnv_field(h, granularity)
    h = _fnv_u32(h, schema_version)
    for r in rules                            # claim EXCLUDED (evidence, not content)
        h = _fnv_field(h, r.name)
        h = _fnv_u32(h, Int(r.rule_id))
        h = _fnv_field(h, r.profiles)
        h = _fnv_field(h, r.provenance)
        h = _fnv_field(h, r.live ? "live" : "structural")
    end
    h
end

# ── disabled mask from the env (comma-separated rule names) ──
function langdef_disabled_mask(rules::Vector{LangDefRule};
    env::AbstractString=get(ENV, "CORE_LANGDEF_DISABLED_RULES", ""))::UInt32
    mask = UInt32(0)
    isempty(env) && return mask
    for name in split(env, ',')
        nm = strip(name)
        isempty(nm) && continue
        idx = findfirst(r -> r.name == nm, rules)
        if idx === nothing
            @warn("CORE_LANGDEF_DISABLED_RULES: unknown rule '$nm' (ignored)")
        else
            (mask |= (UInt32(1) << UInt32(Int(rules[idx].rule_id))))
        end
    end
    mask
end

"The HE small-step pack singleton (digest + env disabled-mask computed at first use)."
function he_small_step_pack(;
    env::AbstractString=get(ENV, "CORE_LANGDEF_DISABLED_RULES", "")
)::LangDefPack
    LangDefPack("HE", "he-extended", "small-step", UInt32(2), HE_SMALL_STEP_RULES,
        langdef_digest("HE", "he-extended", "small-step", 2, HE_SMALL_STEP_RULES),
        langdef_disabled_mask(HE_SMALL_STEP_RULES; env=env))
end

"""True iff the rule is live AND not disabled. (When welded into Eval.jl, covered branches must
be reachable ONLY through this check so disabling cannot be compensated by a legacy path.)"""
function langdef_rule_enabled(pack::LangDefPack, rule_id::LangDefRuleId)::Bool
    (pack.disabled_mask & (UInt32(1) << UInt32(Int(rule_id)))) != 0 && return false
    for r in pack.rules
        r.rule_id == rule_id && return r.live
    end
    false
end

"""Reflection: the rule table as an s-expression string (mirrors CeTTa's step-rules atom):
`(step-rules HE small-step "fnv1a64:<hex>" (schema N) (rules (<name> <claim>)…) (disabled <name>…))`."""
function langdef_step_rules_atom(pack::LangDefPack)::String
    digest = "fnv1a64:" * string(pack.source_digest; base=16, pad=16)
    rules = join(["($(r.name) $(r.claim))" for r in pack.rules], " ")
    dis = [
        r.name for r in pack.rules
        if (pack.disabled_mask & (UInt32(1) << UInt32(Int(r.rule_id)))) != 0
    ]
    disabled = isempty(dis) ? "(disabled)" : "(disabled $(join(dis, " ")))"  # CeTTa: empty ⇒ (disabled)
    "(step-rules $(pack.language_id) $(pack.granularity) \"$digest\" " *
    "(schema $(pack.schema_version)) (rules $rules) $disabled)"
end

# ── weld the table into the interpreter ──────────────────────────────────────────────────────
#
# This table is the SINGLE SOURCE for which rule names exist and which are live. Before this,
# `Eval.rule_enabled` reimplemented the predicate as `!(name in disabled)` and never read the
# table at all — so an unknown/mistyped name read as ENABLED and a `live = false` rule still ran.
#
# The injection runs HERE rather than the interpreter importing the table because Eval.jl is
# included first (MeTTaCore.jl:62 vs :69) and is deliberately self-contained: it declares the
# injection point, this file fills it, and the dependency stays one-directional.
Eval._langdef_register!((r.name, r.live) for r in HE_SMALL_STEP_RULES)
