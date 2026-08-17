# tabling/Options.jl — ONE declaration surface. SWI's `table_options/3`.
#
# Ports `boot/tabling.pl:1291-1335` verbatim in structure: every `:- table p/1 as OPTION` goes
# through one dispatcher into one options record.
#
# ─── WHY THIS EXISTS: THE CONFIG PRINCIPLE (roadmap 0b, user-stated 2026-08-17) ───────────────────
#   "in SLG there may be different options — we will port them, but in config we will only config
#    what is suitable and working for us."
#
# If CONFIG is the mechanism that decides what is live, it cannot be five different shapes. Ours had
# drifted to exactly that — two env vars, `table_subsumptive!`, `table_mode!`, `restraint!` — where
# upstream has ONE entry point for twelve options. This is the convergence, done at five options
# because each of 7.7/7.8/7.11.1-2 adds two or three more.
#
# ─── THE DISTINCTION THIS FILE EXISTS TO MAKE ────────────────────────────────────────────────────
# An option is in one of THREE states, and they must be told apart:
#
#   HONOURED  — ported, live, config turns it on.
#   REFUSED   — a REAL SWI option we cannot honour yet. It is DECLARABLE and THROWS with the reason
#               and the roadmap item. NOT silently accepted, NOT absent.
#   UNKNOWN   — not an SWI option at all ⇒ `domain_error(table_option, Opt)`, as upstream.
#
# 🔴 REFUSED-WITH-A-REASON IS THE WHOLE POINT. A no-op that looks like it works is the failure mode
# this port has paid for most often: `subgoal_abstract(3)` appearing to apply while doing nothing is
# worse than its absence, because absence gets noticed. `restraint!` already worked this way; this
# generalises it to every option.
#
# ⚠️ ENGINE-LEVEL CHOICES DO NOT BELONG HERE. Resumption-vs-recomputation and the trie read path are
# GLOBAL, not per-predicate, and stay env-level (`CORE_TABLING_RECOMPUTE`, `CORE_TABLING_TRIE_READ`).
# Upstream draws the same line: `$tbl_*` Prolog flags for engine behaviour, table options for
# predicates.

"""Per-predicate table options — upstream's options dict (`boot/tabling.pl:1291-1335`).

Field names and defaults follow upstream's dict keys so a reader can compare directly:
`mode` · `incremental` · `opaque` · `monotonic` · `lazy` · `dynamic` · `tshared` · plus the
restraints, which upstream keeps in the same dict via `restraint/4`."""
mutable struct TableOptions
    mode::Symbol                 # :variant (default) | :subsumptive
    incremental::Bool
    opaque::Bool
    monotonic::Bool
    lazy::Bool
    dynamic::Bool
    tshared::Union{Bool,Nothing} # shared/private; `nothing` = unspecified, as upstream's absent key
    max_answers::Int             # NO_RESTRAINT when unset
    subgoal_abstract::Int
    answer_abstract::Int
end
TableOptions() = TableOptions(:variant, false, false, false, false, false, nothing,
                              NO_RESTRAINT, NO_RESTRAINT, NO_RESTRAINT)

"""Options we cannot honour yet: option ⇒ (roadmap item, why).

Declarable and REFUSED, never silently accepted. Each names the item that would make it honourable,
so a reader learns what is missing rather than that something is."""
const _REFUSED_OPTIONS = Dict{Symbol,Tuple{String,String}}(
    :incremental      => ("§7.7",     "needs the IDG (idg_add_edge / falsecount) — no dependency graph yet"),
    :opaque           => ("§7.7",     "the paired inverse of `incremental`; meaningless without it"),
    :monotonic        => ("§7.8",     "needs the same dependency graph, monotone-update variant"),
    :lazy             => ("§7.8",     "the eager/lazy propagation split of monotonic tabling"),
    :dynamic          => ("§7.4",     "tabling for impure/dynamic predicates — interaction rules unbuilt"),
    :shared           => ("§7.9",     "needs a THREADING model; MettaJam is the intended first consumer"),
    :private          => ("§7.9",     "the paired inverse of `shared`; meaningless without it"),
    # 🔴 THIS REASON WAS WRONG UNTIL 2026-08-17 — it said "abstraction over TRIE TERMS at a depth —
    # trie walk not built", i.e. that the ANSWER TRIE was the prerequisite. It is not.
    # `start_abstract_tabling/3` (boot/tabling.pl:466-517) says the design outright: *"This is a merge
    # between variant and subsumptive tabling… If the goal is abstracted we must solve the more
    # general goal and use answers from the abstract table."* Subgoal abstraction rides on SUBSUMPTIVE
    # TABLING — which we HAVE (§7.5) — plus `size_abstract` in the VARIANT trie lookup, which is eight
    # lines inside the existing insert walk (pl-trie.c:829-884), not a new pass.
    # ⇒ §7.11.1 IS BUILDABLE NOW. Kept refused only because it is unbuilt, not because it is blocked.
    :subgoal_abstract => ("§7.11.1",  "BUILDABLE NOW — needs `size_abstract` in the variant-trie " *
                                      "lookup + the §7.5 subsumptive path we already have; unbuilt, " *
                                      "not blocked"),
    # ⚠️ AND THIS ONE IS GENUINELY BLOCKED, FOR A REASON I HAD NOT FOUND. The mechanism needs only the
    # trie — but its only SOUND action does not. `answer_abstract` OVER-approximates (it generalises
    # an answer, so the table claims more than was derived), and `bounded_rationality` compensates by
    # calling `add_radial_restraint()` → `system:(radial_restraint :- tnot(radial_restraint))`
    # (boot/tabling.pl:2317) — an intentionally UNDEFINED predicate whose whole job is to push onto
    # the DELAY LIST, making every abstracted answer conditional in WFS. Without delay lists the only
    # remaining action is `fail`, which UNDER-approximates and is unsound in the other direction for
    # negation. So this waits on delay lists (roadmap 1.0c), and its sibling above does not.
    :answer_abstract  => ("§7.11.2",  "needs DELAY LISTS — it over-approximates, and its only sound " *
                                      "action (bounded_rationality) makes the answer conditional via " *
                                      "radial_restraint; `fail` under-approximates instead"),
)

_refuse(opt::Symbol) = begin
    (item, why) = _REFUSED_OPTIONS[opt]
    throw(ArgumentError("table option `$(opt)` is a REAL SWI option we cannot honour yet ($(item)): " *
                        "$(why). Refused rather than silently accepted — an option that appears to " *
                        "apply and does not is worse than one that is missing. " *
                        "See Core/docs/TABLING_ROADMAP.md."))
end

"""
    table_options!(o, spec) -> TableOptions

`table_options/3` (`boot/tabling.pl:1291`). Apply one option spec to `o`, in place.

`spec` is a `Symbol` (`:subsumptive`, `:variant`, …) or an `Expr`-like pair for the parameterised
ones, given as `opt => n` (`:max_answers => 1000`) — Julia's analogue of upstream's `max_answers(N)`.

⚠️ `incremental` AND `opaque` ARE PAIRED AND MUTUALLY EXCLUSIVE upstream: it sets BOTH keys for
either option — `put_dict(#{incremental:true,opaque:false})` — so declaring one CLEARS the other.
Setting just the named field would leave a predicate both incremental and opaque, which upstream
cannot represent.

🔴 …AND THIS FILE DOES NOT IMPLEMENT THAT PAIRING. Corrected 2026-08-17: the text above used to
claim it was "kept even though both are currently refused", which is false — `_refuse(spec)` is
reached FIRST, so neither `TableOptions.incremental` nor `.opaque` is ever written by either option.
Harmless while both are refused, and precisely the note that would mislead whoever un-refuses them,
which is why it is stated as a TODO rather than as behaviour: un-refusing either one must set BOTH
fields in the same assignment.
"""
function table_options!(o::TableOptions, spec)::TableOptions
    if spec isa Symbol
        if spec === :subsumptive;  o.mode = :subsumptive
        elseif spec === :variant;  o.mode = :variant
        elseif haskey(_REFUSED_OPTIONS, spec); _refuse(spec)
        else
            throw(ArgumentError("domain_error(table_option, $(spec)) — known: " *
                  join(sort(String[String(k) for k in
                       (:subsumptive, :variant, keys(_REFUSED_OPTIONS)...)]), ", ") *
                  ", max_answers => N, subgoal_abstract => N, answer_abstract => N"))
        end
    elseif spec isa Pair{Symbol,<:Integer}
        (opt, n) = spec
        if opt === :max_answers
            # `restraint/4`: a NEGATIVE value REMOVES the restraint rather than storing it.
            o.max_answers = n < 0 ? NO_RESTRAINT : Int(n)
        elseif opt === :subgoal_abstract || opt === :answer_abstract
            _refuse(opt)
        else
            throw(ArgumentError("domain_error(table_option, $(opt)($(n)))"))
        end
    else
        throw(ArgumentError("domain_error(table_option, $(spec)) — expected a Symbol or `opt => N`"))
    end
    o
end

"""
    parse_table_options(specs) -> TableOptions

Upstream's `(A,B)` conjunction clause: fold every spec into one record, left to right.
"""
function parse_table_options(specs)::TableOptions
    o = TableOptions()
    for sp in specs; table_options!(o, sp); end
    o
end

const _TABLE_OPTIONS = Dict{Symbol,TableOptions}()
table_options_for(head::Symbol)::TableOptions = get(() -> TableOptions(), _TABLE_OPTIONS, head)

"""
    table_as!(head, specs...)

THE declaration entry point — `:- table head as spec, spec, …`.

Applies the parsed options to the live registries, so this is the ONE place that knows how an option
reaches the engine: `mode` to the subsumptive set, `max_answers` to the restraint registry, and the
head itself to `_TABLED_HEADS`.

    table_as!(:p)                                  # plain variant tabling
    table_as!(:p, :subsumptive)                    # §7.5
    table_as!(:p, :subsumptive, :max_answers => 1000)
    table_as!(:p, :incremental)                    # THROWS, naming §7.7 and why
"""
function table_as!(head::Symbol, specs...)
    o = parse_table_options(specs)                 # throws BEFORE any registry is touched
    _TABLE_OPTIONS[head] = o
    table!(head)
    o.mode === :subsumptive ? table_subsumptive!(head) : untable_subsumptive!(head)
    restraint!(head, :max_answers, o.max_answers)
    o
end

"Drop a head's options along with its declaration — called by `untable!`."
clear_table_options!(head::Symbol) = (delete!(_TABLE_OPTIONS, head); nothing)
clear_all_table_options!() = (empty!(_TABLE_OPTIONS); nothing)
