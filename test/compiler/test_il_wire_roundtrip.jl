# ============================================================================================
# THE WIRE PROPERTY: `parse(il_text(a)) == a` over RANDOMLY GENERATED atoms.
#
# Fig-2 makes MeTTa-IL the DISTRIBUTED artifact, so the clause text is not a debug view — it is the
# thing another backend receives. Nothing until now checked that an atom survives it. The three
# wrong-answer classes this session opened with (`Space`, `StateCell`, grounded strings) were all this
# defect, each found one at a time by a corpus script that happened to exercise it.
#
# WHY RANDOMIZED AND NOT A CASE LIST. A case list only contains the losses someone already thought of;
# that is exactly how the grounded-string case survived — `test_emit_il.jl` proved atom ⇒ TEXT for
# every node in the corpus and passed throughout, because both sides shared the same lossy `show`.
#
# CROSS-CHECKED AGAINST THE OTHER IMPLEMENTATIONS (see test/oracle/mettaref/README.md):
#   * `dev-zone/jetta` gets faithfulness structurally — `SAtomSerializer` writes a TYPE TAG per atom
#     kind, with TAG_GROUNDED_STRING distinct from TAG_SYMBOL, so its round-trip cannot confuse them.
#   * `dev-zone/mettail-rust` keeps a typed AST and settles for the WEAKER property — its proptest
#     asserts display IDEMPOTENCE, not equality, and excludes variables and binders outright
#     ("moniker's Var equality semantics differ from structural equality after round-trip").
#   * Our `Var` round-trips exactly, so we are not forced into their exclusion, and our text form has
#     no type tags, so we are not handed JeTTa's guarantee either. The property is therefore BOTH
#     achievable and load-bearing here — which is why it is worth asserting rather than assuming.
#
# THE LOSSY SET IS ENUMERATED, NOT DISCOVERED AT RUNTIME. Values that provably cannot survive a textual
# encoding (a live `Space`, a `StateCell`) are excluded from generation and listed below. That list is
# the same one `CompileLane._unroundtrippable` refuses to compile; if the two ever disagree, one of
# them is wrong, and the last assertion in this file is what says so.
# ============================================================================================

using Test
using Random
using MeTTaCore
const _WR_V = MeTTaCore.Eval
const _WR_SM = MeTTaCore.StandardMeTTa
const _WR_IL = MeTTaCore.CompilerEmitIL

# Symbol alphabet deliberately includes names that COLLIDE with grounded operators (`+`, `if`) and
# minimal-MeTTa keywords (`chain`, `return`). A reader resolves a bare word through TOKEN_REGISTRY, so
# if a plain symbol can be spelled the same way as an operator the wire form is ambiguous — and the
# emitter does emit user symbols verbatim. Generating them is how that gets measured instead of assumed.
const _WR_SYMS = String["foo", "Bar", "f", "a", "+", "if", "chain", "return", "Nil", "empty-thing"]
const _WR_VARS = String["x", "y", "acc", "_ignored"]
const _WR_STRS = String["", "abc", "with space", "has\"quote", "(parens)", "42",
                        "back\\slash", "both\"\\mixed", "new\nline", "tab\there", "\U1F600"]

"Generate a random atom drawn only from kinds the emitter can put on the wire."
function _wr_gen(rng::Random.AbstractRNG, depth::Int)::_WR_SM.Atom
    leaf = depth <= 0 || rand(rng) < 0.55
    if leaf
        k = rand(rng, 1:6)
        k == 1 && return _WR_SM.Sym(rand(rng, _WR_SYMS))
        k == 2 && return _WR_SM.Var(rand(rng, _WR_VARS))
        k == 3 && return _WR_SM.Grounded(rand(rng, -1000:1000))
        k == 4 && return _WR_SM.Grounded(rand(rng, _WR_STRS))
        k == 5 && return _WR_SM.Grounded(round(rand(rng) * 200 - 100; digits = 3))
        return _WR_SM.Grounded(rand(rng, Bool))
    end
    n = rand(rng, 0:3)
    _WR_SM.Expression(_WR_SM.Atom[_wr_gen(rng, depth - 1) for _ in 1:n])
end

"Read wire text back the way a consumer would: a fresh space, stdlib loaded, no `bind!` tokens."
function _wr_parse(text::AbstractString)::Union{_WR_SM.Atom, Nothing}
    sp = _WR_V.Space(); _WR_V.load_core_stdlib!(sp)
    toks = _WR_V.tokenize(String(text)); i = Ref(1)
    isempty(toks) && return nothing
    a = _WR_V.parse_from(toks, i, sp.tokens)
    i[] <= length(toks) && return nothing      # trailing tokens: the text did not denote ONE atom
    a
end

# THE KNOWN-LOSS LEDGER. Each entry is a class the wire form provably cannot carry, with the reason
# and, where one exists, the upstream authority. The test asserts the observed losses are EXACTLY this
# set: a new class fails (a regression), and a class that stops appearing ALSO fails, so a fix cannot
# land silently and the ledger cannot rot. Same discipline as the LeaTTa oracle's MISSING_OP ledger.
# `"unparseable"` WAS a third entry here: a string containing `"` could not be read back. FIXED
# 2026-08-12 — the loss was on the WRITE side only. `Eval.tokenize` had decoded `\n \r \t \" \\ \'`
# all along (citing hyperon `text.rs:550-573`); `il_text` and `render` simply never ESCAPED, so
# `back\\slash` came back `backslash` — silently corrupted, not rejected. Both producers now share
# `CompilerEmit._escape_il_string`, and the generator alphabet above was widened to the characters that
# were being eaten. This is what the two-sided ledger is for: the entry could not be quietly deleted,
# its disappearance had to fail the test first.
const _WR_KNOWN = Dict{String, String}(
    "kind changed: Grounded → Sym" =>
        "Grounded{Bool}: `il_text` writes `true`/`false` and the reader has no boolean case " *
        "(`Eval.parse_atom`, Eval.jl:2602-2610), so it returns Sym. MeTTa's own convention is that " *
        "booleans are the SYMBOLS True/False — `Sym(\"True\")` round-trips fine — so a " *
        "Grounded{Bool} can only have entered a space from a grounded op returning a Julia Bool. " *
        "🔴 `CompileLane._unroundtrippable` EXPLICITLY ALLOWS `v isa Bool`, which is wrong for the " *
        "wire: it will compile a definition whose clause text cannot be read back.",
    "kind changed: Sym → Grounded" =>
        "A plain symbol spelled like a registered operator (`+`) is resolved to " *
        "`Grounded{Operation}` on read, because `parse_atom` consults TOKEN_REGISTRY for every bare " *
        "word. INHERENT to an untagged text format — `dev-zone/jetta` avoids it structurally by " *
        "writing TAG_SYMBOL vs a grounded tag (`runtime/space/SAtomSerializer.kt`). Not fixable " *
        "without tagging the wire form or escaping operator-shaped symbols.",
)

@testset "MeTTa-IL wire form — parse(il_text(a)) == a over generated atoms" begin
    rng = Random.MersenneTwister(0x11ce)
    total = 0
    failures = Dict{String, Vector{Tuple{String, String}}}()
    for _ in 1:4000
        a = _wr_gen(rng, 3)
        total += 1
        txt = _WR_IL.il_text(a)
        back = try _wr_parse(txt) catch e; nothing end
        back == a && continue
        cls = if back === nothing
            "unparseable"
        elseif typeof(back) != typeof(a)
            "kind changed: $(nameof(typeof(a))) → $(nameof(typeof(back)))"
        elseif a isa _WR_SM.Grounded
            "grounded value changed: $(typeof((a::_WR_SM.Grounded).value))"
        else
            "structure changed: $(nameof(typeof(a)))"
        end
        bucket = get!(failures, cls, Tuple{String, String}[])
        length(bucket) < 3 && push!(bucket, (txt, string(back)))
    end

    # An Expression fails whenever any LEAF inside it does, so it reports as its own class and tells
    # us nothing new. Attribute it away: an expression loss is only a finding if some leaf class is
    # not already known — otherwise it is the same defect seen through a container.
    haskey(failures, "structure changed: Expression") && !isempty(intersect(keys(failures), keys(_WR_KNOWN))) &&
        delete!(failures, "structure changed: Expression")

    println("\n  ── wire round-trip over $total generated atoms ──")
    for (cls, examples) in sort(collect(failures); by = first)
        known = haskey(_WR_KNOWN, cls)
        println("     $(known ? "•" : "✗") $cls$(known ? "  [known]" : "  ← NEW")")
        for (txt, back) in examples
            println("         text $(repr(first(txt, 58)))  →  $(first(back, 58))")
        end
    end

    @test total == 4000                                    # anti-vacuity: atoms were generated
    # (1) No loss class outside the ledger.
    unexpected = setdiff(keys(failures), keys(_WR_KNOWN))
    for u in unexpected
        @info "NEW WIRE LOSS CLASS — the IL text cannot carry this and nothing said so" class=u
    end
    @test isempty(unexpected)
    # (2) Every ledgered class is STILL observed. If one disappears the generator stopped reaching it
    #     or the defect was fixed; either way the ledger is now lying and must be updated deliberately.
    missing_now = setdiff(keys(_WR_KNOWN), keys(failures))
    for m in missing_now
        @info "LEDGERED LOSS NO LONGER OBSERVED — fixed, or the generator stopped reaching it" class=m
    end
    @test isempty(missing_now)
end

@testset "the wire ledger and CompileLane._unroundtrippable must agree" begin
    # `_unroundtrippable` exists to refuse what the text form cannot carry. The property test found two
    # things it let through. ONE IS NOW CLOSED, and not by tightening the guard: strings containing `"`
    # or `\\` were lost on the WRITE side only, so escaping both producers fixed it and the guard's
    # permissive `v isa AbstractString` became correct rather than wrong. The other remains.
    sp = _WR_V.Space(); _WR_V.load_core_stdlib!(sp)
    # `CompileLane.jl` is `include`d straight into `MeTTaCore` (MeTTaCore.jl:164), not a submodule —
    # unlike `CompilerEmitIL`. Guessing the qualified name is what produced two false "DECLINED"
    # diagnoses earlier in this session, so it is resolved from the include site.
    unr = MeTTaCore._unroundtrippable

    # 🟢 CLOSED. This previously asserted the HOLE — "the guard permits Grounded{Bool} and it is lost".
    # The guard now names it. Note what made that cheap: while the verdict DECLINED a definition,
    # adding a case cost compiled coverage, so every addition was a trade. Since the split
    # (2026-08-12) the verdict only ANNOTATES the wire form, so naming a real lossy case costs nothing
    # and there is no longer a reason to leave one out.
    @test unr(_WR_SM.Atom[_WR_SM.Grounded(true)], sp) !== nothing                      # guard names it …
    @test occursin("bool", lowercase(String(unr(_WR_SM.Atom[_WR_SM.Grounded(true)], sp))))
    @test _wr_parse(_WR_IL.il_text(_WR_SM.Grounded(true))) != _WR_SM.Grounded(true)    # … and it IS lost
    # The loss itself is unchanged and still ledgered above — this asserts the guard AGREES with the
    # ledger, which is the whole point of this testset.
    # CLOSED: quoted and backslashed strings now round-trip, so the guard permitting them is right.
    for s in ("has\"quote", "back\\slash", "both\"\\mixed")
        @test unr(_WR_SM.Atom[_WR_SM.Grounded(s)], sp) === nothing
        @test _wr_parse(_WR_IL.il_text(_WR_SM.Grounded(s))) == _WR_SM.Grounded(s)
    end
    # 🔴 THE BOOL HOLE IS NOT FIXED HERE ON PURPOSE. Since `2105f9d` the LANE no longer round-trips
    # through text, so the guard now answers the wrong question: lane-loadability (nothing to check —
    # atoms flow directly) has been conflated with wire-faithfulness (still needed, demonstrably
    # incomplete). Splitting the two changes what the lane compiles, so it is its own change with its
    # own corpus measurement.
end

@testset "string escapes decode as upstream hyperon decodes them" begin
    # Conformance for the lexer change made alongside the escaping fix. Authority:
    # hyperon-experimental `lib/src/metta/text.rs:534-600` (`parse_string`, `parse_2_digit_radix_char`,
    # `parse_unicode_sequence`). Note `\u` is BRACED there — `\u{41}`, not `\u0041` — which this pins,
    # because the first probe written for it assumed the unbraced form and would have "verified" a
    # format upstream does not accept.
    for (src, want) in (("\"a\\\"b\"", "a\"b"), ("\"a\\\\b\"", "a\\b"),
                        ("\"a\\nb\"", "a\nb"), ("\"a\\tb\"", "a\tb"), ("\"a\\rb\"", "a\rb"),
                        ("\"\\x41\"", "A"), ("\"\\u{1F600}\"", "\U1F600"))
        got = _wr_parse(src)
        @test got isa _WR_SM.Grounded && String((got::_WR_SM.Grounded).value) == want
    end
    # DELIBERATE DIVERGENCE, pinned so it stays a decision: upstream raises "Invalid escape sequence"
    # for an unknown or malformed escape; we drop the backslash and keep the character. Rejecting input
    # Core currently accepts needs its own corpus pass.
    for (src, want) in (("\"\\q\"", "q"), ("\"\\xZZ\"", "xZZ"), ("\"\\u0041\"", "u0041"))
        got = _wr_parse(src)
        @test got isa _WR_SM.Grounded && String((got::_WR_SM.Grounded).value) == want
    end
end
