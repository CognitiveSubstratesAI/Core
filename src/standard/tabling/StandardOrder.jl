# tabling/StandardOrder.jl — Prolog's STANDARD ORDER OF TERMS.
#
# ─── WHY THIS IS IN THE TABLING SUBFOLDER ────────────────────────────────────────────────────────
# It is not decoration: SWI's mode-directed tabling aggregates with `min/3` and `max/3`, and those
# are defined on `@<` / `@>` — the standard order — NOT on numeric comparison
# (`boot/tabling.pl:1529-1530`):
#
#     min(S0, S1, S) :- (S0 @< S1 -> S = S0 ; S = S1).
#     max(S0, S1, S) :- (S0 @> S1 -> S = S0 ; S = S1).
#
# So `min`/`max` are total over ARBITRARY terms upstream, not just numbers. Implementing them with
# `<` would be a silent semantic narrowing that passes every numeric test and diverges the moment a
# lattice aggregates symbols or compounds. `Aggregation.jl` depends on this file for exactly that.
#
# `capability_search.sh "standard order" "term order" "compare atoms"` → ZERO hits before this file,
# so this is a genuine absence rather than a rename.
#
# ─── PORTED 1:1 FROM `src/pl-prims.c:1783-1798` (`compareStandard`) ──────────────────────────────
#     Var @< AttVar @< Number @< String @< Atom @< Term
#     Atom:    alphabetically
#     Strings: alphabetically
#     number:  value
#     Term:    arity / alphabetically / recursive
#
# Two upstream details that are easy to lose and are kept here deliberately:
#   * ON EQUAL NUMERIC VALUE, FLOAT SORTS BEFORE INTEGER (`pl-prims.c:1777` — on CMP_EQUAL it returns
#     LESS when the left tag is TAG_FLOAT). So `1.0 @< 1` is TRUE. Not an accident of representation.
#   * COMPOUNDS COMPARE ON ARITY FIRST, name second. `f(z) @< g(a,b)` because 1 < 2, even though
#     'f' @< 'g' would also give that answer — the arity test is what decides, and a name-first
#     implementation disagrees on `h(a,b) @< f(z)`.
#
# We have no AttVar, so the rank ladder collapses to four positions. `Grounded{T}` splits by its
# payload: real numbers rank as Number, strings as String, and any OTHER grounded payload is ranked
# after strings but before Sym — see `std_rank`.
#
# ─── UPSTREAM TRACE ──────────────────────────────────────────────────────────────────────────────
# Names here follow swipl-devel so a reader can grep upstream directly. Ours ← theirs:
#
#   compare_standard   ←  compareStandard          src/pl-prims.c:1783   (and Prolog `compare/3`)
#   std_rank           ←  the tag ladder           src/pl-prims.c:1788
#   standard_lt        ←  `@</2`                   used by min/3, boot/tabling.pl:1529
#   standard_gt        ←  `@>/2`                   used by max/3, boot/tabling.pl:1530

"NaN test that does not allocate a closure — see the note in `compare_standard`."
_is_nan(v)::Bool = v isa AbstractFloat && isnan(v)

"Rank of an atom in the standard order. Lower sorts first. `pl-prims.c:1788`'s ladder."
function std_rank(a::Atom)::Int
    a isa Var        && return 0
    if a isa Grounded
        v = a.value
        v isa Real           && return 1    # Number
        v isa AbstractString && return 2    # String
        return 3                            # other grounded payloads: after String, before Atom
    end
    a isa Sym        && return 4            # Atom (Prolog "atom" = our Sym)
    a isa Expression && return 5            # Term (compound)
    return 6
end

"""
    compare_standard(x, y) -> Int

Prolog `compare/3` as -1 / 0 / 1. Ported from `compareStandard` (`pl-prims.c:1783`).

Total and antisymmetric over every `Atom` we can construct, which is what `min`/`max` aggregation
requires — an aggregation that can throw on an unexpected payload would abort a completing table.
"""
function compare_standard(x::Atom, y::Atom)::Int
    rx, ry = std_rank(x), std_rank(y)
    rx != ry && return rx < ry ? -1 : 1

    if x isa Var                      # OldVar < NewVar; upstream calls this "not reliable" but it
        xv, yv = x::Var, y::Var       # must be a total order, so key on (name, id) which we have.
        xv.name != yv.name && return xv.name < yv.name ? -1 : 1
        return xv.id == yv.id ? 0 : (xv.id < yv.id ? -1 : 1)

    elseif x isa Grounded && y isa Grounded
        xv, yv = (x::Grounded).value, (y::Grounded).value
        if xv isa Real && yv isa Real
            # NaN sorts lowest, mirroring pl-prims.c:1765-1768 before any value comparison.
            # ⚠️ `_is_nan` is TOP-LEVEL, not an inner closure. As `isnanv(v) = …` inside this function
            # JET reported three runtime dispatches on it — an inner closure is captured and boxed.
            _is_nan(xv) && return _is_nan(yv) ? 0 : -1
            _is_nan(yv) && return 1
            xv < yv && return -1
            xv > yv && return 1
            # EQUAL VALUE ⇒ Float BEFORE Integer (pl-prims.c:1777).
            xf, yf = xv isa AbstractFloat, yv isa AbstractFloat
            xf == yf && return 0
            return xf ? -1 : 1
        end
        sx, sy = string(xv), string(yv)
        return sx == sy ? 0 : (sx < sy ? -1 : 1)

    elseif x isa Sym
        xn, yn = string((x::Sym).name), string((y::Sym).name)
        return xn == yn ? 0 : (xn < yn ? -1 : 1)

    elseif x isa Expression
        xc, yc = (x::Expression).children, (y::Expression).children
        # ARITY FIRST (pl-prims.c:1794 "arity / alphabetically / recursive").
        length(xc) != length(yc) && return length(xc) < length(yc) ? -1 : 1
        isempty(xc) && return 0
        # then NAME (the head), then args recursively — the head is children[1] for us.
        for i in eachindex(xc)
            c = compare_standard(xc[i], yc[i])
            c != 0 && return c
        end
        return 0
    end
    0
end

"`@<` — strictly precedes in the standard order (`boot/tabling.pl:1529` uses this for `min/3`)."
standard_lt(x::Atom, y::Atom)::Bool = compare_standard(x, y) < 0
"`@>` — strictly follows in the standard order (`boot/tabling.pl:1530` uses this for `max/3`)."
standard_gt(x::Atom, y::Atom)::Bool = compare_standard(x, y) > 0
