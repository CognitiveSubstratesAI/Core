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
    tshared::Union{Bool, Nothing} # shared/private; `nothing` = unspecified, as upstream's absent key
    max_answers::Int             # NO_RESTRAINT when unset
    subgoal_abstract::Int
    answer_abstract::Int
end
TableOptions() = TableOptions(:variant, false, false, false, false, false, nothing,
    NO_RESTRAINT, NO_RESTRAINT, NO_RESTRAINT)

"""Options we cannot honour yet: option ⇒ (roadmap item, why).

Declarable and REFUSED, never silently accepted. Each names the item that would make it honourable,
so a reader learns what is missing rather than that something is."""
const _REFUSED_OPTIONS = Dict{Symbol, Tuple{String, String}}(
    # ✅ `:incremental` / `:opaque` ARE NO LONGER HERE — honoured since 2026-08-28. Their old reason
    #    ("needs the IDG — no dependency graph yet") had been FALSE since 2026-08-18: `tabling/IDG.jl`
    #    has `idg_add_edge!`, `idg_changed!` and a real `falsecount` count. The reason outlived the gap.
    # ⚠️ `:monotonic` REMAINS REFUSED, and its old reason was wrong too — `tabling/Monotonic.jl` (228
    #    lines, 8 functions incl. `mono_assert_dep!` / `mono_propagate_assert!` / `mono_drain_queue!`)
    #    exists. What is actually missing is the WRAPPER SIDE: upstream's `'$set_table_wrappers'`
    #    (boot/tabling.pl:1544) installs `wrap_monotonic` on the DYNAMIC predicate, and we have no
    #    monotonic equivalent of `_INCREMENTAL_HEADS` nor a `mon_assert_dep` call path from add-atom.
    :monotonic => ("§7.8", "Monotonic.jl exists; the `wrap_monotonic` DYNAMIC-side hook does not"),
    :lazy => ("§7.8", "the eager/lazy propagation split of monotonic tabling"),
    :dynamic =>
        ("§7.4", "tabling for impure/dynamic predicates — interaction rules unbuilt"),
    :shared => ("§7.9", "needs a THREADING model; MettaJam is the intended first consumer"),
    :private => ("§7.9", "the paired inverse of `shared`; meaningless without it")
    # ✅ `:subgoal_abstract` IS NO LONGER HERE — §7.11.1 is BUILT (`tabling/Abstract.jl`, 2026-08-17).
    # Its refusal reason had been wrong AND load-bearing: it said the option needed "abstraction over
    # TRIE TERMS at a depth — trie walk not built", i.e. that the answer trie was the prerequisite.
    # It never was. `start_abstract_tabling/3` states the design outright (boot/tabling.pl:469-472):
    # *"This is a merge between variant and subsumptive tabling… If the goal is abstracted we must
    # solve the more general goal and use answers from the abstract table."* It rides on SUBSUMPTIVE
    # TABLING (§7.5, already built) plus `size_abstract`, which is a budget threaded through the walk
    # — not a new pass. A refusal reason carried forward unexamined kept it out of reach for weeks.
    # ✅ `:answer_abstract` IS NO LONGER HERE EITHER — §7.11.2 is BUILT (`tabling/Abstract.jl`,
    # 2026-08-18). Its reason was RE-CHECKED rather than assumed, and it was HALF right in the half
    # that mattered. Delay lists landed the day after it was written (`tabling/Delays.jl`) — but they
    # were never the whole blocker: our delay-carrying value `Grounded(WFSBottom(dnf))` HAS NO VALUE,
    # so substituting it for the generalised answer would discard the generalisation, which IS the
    # feature. Upstream does not put the condition on the value either — `delay_info` hangs off the
    # TRIE NODE (`pl-tabling.h:179-184`), and `AnswerTrie.jl`'s own `TrieNode` comment already named
    # `answer_abstract` as one of the two features waiting on exactly that. One named FIELD short,
    # not one subsystem short. `[[feedback_capability_claims_expire_retest_the_premise]]`
)

_refuse(opt::Symbol) = begin
    (item, why) = _REFUSED_OPTIONS[opt]
    throw(
        ArgumentError(
            "table option `$(opt)` is a REAL SWI option we cannot honour yet ($(item)): " *
            "$(why). Refused rather than silently accepted — an option that appears to " *
            "apply and does not is worse than one that is missing. " *
            "See Core/docs/TABLING_ROADMAP.md."
        )
    )
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
        if spec === :subsumptive
            o.mode = :subsumptive
        elseif spec === :variant
            o.mode = :variant
        # 🔴 BOTH FIELDS, ONE ASSIGNMENT — upstream writes the pair for EITHER option:
        #   table_options(incremental, …) :- put_dict(#{incremental:true,  opaque:false}, …)  :1304
        #   table_options(opaque,      …) :- put_dict(#{incremental:false, opaque:true },  …)  :1312
        # Setting only the named field would leave a predicate both incremental and opaque, a state
        # upstream cannot represent — and `'$set_table_wrappers'` (:1544) tests them SEPARATELY
        # (`incremental,1` AND `\+ opaque,1`), so a stale `opaque` would silently suppress wrapping.
        # This is the TODO written into this file's own docstring on 2026-08-17.
        elseif spec === :incremental
            o.incremental = true
            o.opaque = false
        elseif spec === :opaque
            o.incremental = false
            o.opaque = true
        elseif haskey(_REFUSED_OPTIONS, spec)
            _refuse(spec)
        else
            throw(
                ArgumentError(
                    "domain_error(table_option, $(spec)) — known: " *
                    join(
                        sort(
                            String[
                                String(k) for k in
                                (:subsumptive, :variant, keys(_REFUSED_OPTIONS)...)
                            ]
                        ), ", ") *
                    ", max_answers => N, subgoal_abstract => N, answer_abstract => N"
                )
            )
        end
    elseif spec isa Pair{Symbol, <:Integer}
        (opt, n) = spec
        if opt === :max_answers
            # `restraint/4`: a NEGATIVE value REMOVES the restraint rather than storing it.
            o.max_answers = n < 0 ? NO_RESTRAINT : Int(n)
        elseif opt === :subgoal_abstract
            # §7.11.1 — same negative-removes convention as `max_answers` (`restraint/4`).
            o.subgoal_abstract = n < 0 ? NO_RESTRAINT : Int(n)
        elseif opt === :answer_abstract
            # §7.11.2 — same negative-removes convention as `max_answers` (`restraint/4`).
            o.answer_abstract = n < 0 ? NO_RESTRAINT : Int(n)
        else
            throw(ArgumentError("domain_error(table_option, $(opt)($(n)))"))
        end
    else
        throw(
            ArgumentError(
                "domain_error(table_option, $(spec)) — expected a Symbol or `opt => N`"
            )
        )
    end
    o
end

"""
    parse_table_options(specs) -> TableOptions

Upstream's `(A,B)` conjunction clause: fold every spec into one record, left to right.
"""
function parse_table_options(specs)::TableOptions
    o = TableOptions()
    for sp in specs
        table_options!(o, sp)
    end
    o
end

const _TABLE_OPTIONS = Dict{Symbol, TableOptions}()
table_options_for(head::Symbol)::TableOptions =
    get(() -> TableOptions(), _TABLE_OPTIONS, head)

"""
    table_as!(head, specs...)

THE declaration entry point — `:- table head as spec, spec, …`.

Applies the parsed options to the live registries, so this is the ONE place that knows how an option
reaches the engine: `mode` to the subsumptive set, `max_answers` to the restraint registry, and the
head itself to `_TABLED_HEADS`.

    table_as!(:p)                                  # plain variant tabling
    table_as!(:p, :subsumptive)                    # §7.5
    table_as!(:p, :subsumptive, :max_answers => 1000)
    table_as!(:p, :subgoal_abstract => 2)          # §7.11.1 — bound the table SET, not each table
    table_as!(:p, :incremental)                    # THROWS, naming §7.7 and why
"""
function table_as!(head::Symbol, specs...)
    o = parse_table_options(specs)                 # throws BEFORE any registry is touched
    _TABLE_OPTIONS[head] = o
    table!(head)
    o.mode === :subsumptive ? table_subsumptive!(head) : untable_subsumptive!(head)
    # ── '$set_table_wrappers' (boot/tabling.pl:1544) ────────────────────────────────────────────
    # Upstream wraps a predicate iff it is incremental AND NOT opaque — the two attributes are read
    # SEPARATELY, which is why the paired assignment above matters. `opaque` is the OFF switch.
    if o.incremental && !o.opaque
        push!(_INCREMENTAL_HEADS, head)
        _IDG_RECORD[] = true        # the bookkeeping must actually run, or the declaration is inert
    else
        delete!(_INCREMENTAL_HEADS, head)
    end
    restraint!(head, :max_answers, o.max_answers)
    subgoal_abstract!(head, o.subgoal_abstract)    # §7.11.1
    answer_abstract!(head, o.answer_abstract)      # §7.11.2
    o
end

"Drop a head's options along with its declaration — called by `untable!`."
clear_table_options!(head::Symbol) = (delete!(_TABLE_OPTIONS, head); nothing)
clear_all_table_options!() = (empty!(_TABLE_OPTIONS); nothing)
