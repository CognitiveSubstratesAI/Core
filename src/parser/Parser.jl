# Parser.jl: S-expression parser for MeTTa
#
# Converts MeTTa source strings to Julia nested arrays
# Example: "(+ 1 2)" → [:+, 1, 2]

export parse_metta, parse_sexpr, metta_string, @metta_str

# ============================================================================
# Tokenizer
# ============================================================================


function tokenize(source::AbstractString)::Vector{String}
    tokens = String[]
    chars = collect(source)  # Convert to character array for safe indexing
    i = 1
    n = length(chars)
    
    while i <= n
        c = chars[i]
        
        # Skip whitespace
        if isspace(c)
            i += 1
            continue
        end
        
        # Comments (;)
        if c == ';'
            while i <= n && chars[i] != '\n'
                i += 1
            end
            continue
        end
        
        # Parentheses
        if c == '(' || c == ')'
            push!(tokens, string(c))
            i += 1
            continue
        end
        
        # Strings — `"` at HEAD position opens a string. Internal `"` inside
        # a non-string atom (e.g. fo"o) is handled by the atom branch below.
        if c == '"'
            j = i + 1
            while j <= n && chars[j] != '"'
                if chars[j] == '\\' && j + 1 <= n
                    j += 2
                else
                    j += 1
                end
            end
            # ROBUSTNESS: detect unterminated string before slicing past end.
            # Per parser invariant: a parser should never throw a BoundsError;
            # it should produce a parse error on malformed input.
            j > n && error("Unterminated string literal starting at char $i")
            push!(tokens, String(chars[i:j]))
            i = j + 1
            continue
        end

        # Variables ($x)
        if c == '$'
            j = i + 1
            while j <= n && !isspace(chars[j]) && chars[j] ∉ ('(', ')')
                j += 1
            end
            push!(tokens, String(chars[i:j-1]))
            i = j
            continue
        end

        # Atoms/numbers/symbols (including Unicode).
        # Per EBNF: WORD ::= (CHAR | '#'), {CHAR | '"' | '#'} — `"` is permitted
        # in symbol BODIES (after the head), just not as the head (the head-`"`
        # case opens a string and is handled above). So the body-exclusion set
        # is {'(', ')'} (terminators) plus whitespace, NOT `"`.
        j = i
        while j <= n && !isspace(chars[j]) && chars[j] ∉ ('(', ')')
            j += 1
        end
        push!(tokens, String(chars[i:j-1]))
        i = j
    end

    return tokens
end

# ============================================================================
# Parser
# ============================================================================


function parse_atom(token::String)
    # Variable — stored as Symbol with $ prefix (Core convention)
    if startswith(token, "\$")
        return Symbol(token)   # e.g. Symbol("\$x")
    end
    
    # String literal — use prevind for Unicode-safe end-trim
    if startswith(token, "\"") && endswith(token, "\"")
        inner = token[2 : prevind(token, lastindex(token))]
        return unescape_string(inner)
    end
    
    # Number (Integer or Float)
    num = tryparse(Int, token)
    if num !== nothing
        return num
    end
    num = tryparse(Float64, token)
    if num !== nothing
        return num
    end
    
    # Boolean
    if token == "true" || token == "True"
        return true
    elseif token == "false" || token == "False"
        return false
    end
    
    # Symbol
    return Symbol(token)
end


"""
lift_to_term(x) — identity for Core (plain Julia values, no MeTTaTerm).
Kept for API compatibility with code that calls it; returns x unchanged.
"""
lift_to_term(x) = x

"""
parse_tokens(tokens, i) — recursive descent, returns plain Julia values.
Symbols, Numbers, Bools, Vectors — no MeTTaTerm dependency.
"""
function parse_tokens(tokens::Vector{String}, i::Int)
    i > length(tokens) && error("Unexpected end of input")
    token = tokens[i]

    if token == "("
        elements = Any[]
        i += 1
        while i <= length(tokens) && tokens[i] != ")"
            elem, i = parse_tokens(tokens, i)
            push!(elements, elem)
        end
        i > length(tokens) && error("Missing closing parenthesis")
        return elements, i + 1
    elseif token == ")"
        error("Unexpected closing parenthesis")
    else
        return parse_atom(token), i + 1
    end
end


function parse_sexpr(source::AbstractString)
    tokens = tokenize(source)
    if isempty(tokens)
        return nothing
    end
    expr, _ = parse_tokens(tokens, 1)
    return expr
end


"""
parse_metta(source) → Vector{Any}

Parse a MeTTa source string into a list of Julia values.
Lines starting with `!` are wrapped as `[:!, expr]` (execution directive).
Returns plain Julia: Symbol, Vector{Any}, Number, Bool, String.
"""
function parse_metta(source::AbstractString) :: Vector{Any}
    tokens = tokenize(source)
    # Split `!`-prefixed tokens so the `!` directive fires uniformly:
    #   !42          → ["!", "42"]
    #   !$x          → ["!", "$x"]
    #   !bare-symbol → ["!", "bare-symbol"]
    # The previous behavior merged `!` into the following atom, so only
    # `!(...)` (parens-broken) triggered the directive. The HE-artifact case
    # of `!name`-as-symbol is no longer preserved — per the spec note that
    # form is "not a strong requirement." If a literal symbol starting with
    # `!` is needed, write it explicitly via construction or a string.
    expanded = String[]
    for tok in tokens
        if length(tok) >= 2 && tok[1] == '!' && tok != "!"
            push!(expanded, "!")
            push!(expanded, tok[2:end])
        else
            push!(expanded, tok)
        end
    end
    tokens = expanded

    exprs  = Any[]
    i = 1
    while i <= length(tokens)
        if tokens[i] == "!"
            i += 1
            i > length(tokens) && error("Unexpected end of input after '!'")
            expr, i = parse_tokens(tokens, i)
            push!(exprs, Any[:!, expr])
        else
            expr, i = parse_tokens(tokens, i)
            push!(exprs, expr)
        end
    end
    exprs
end

"""
metta_string(x) → String

Convert a parsed MeTTa value back to an S-expression string.
"""
function metta_string(x) :: String
    x isa Symbol  && return string(x)   # includes $var symbols
    x isa Vector  && return "($(join(metta_string.(x), " ")))"
    x isa Bool    && return x ? "True" : "False"
    x isa String  && return "\"$x\""
    string(x)
end

"""
    metta"..."  →  String

Non-interpolating MeTTa source literal.  MeTTa's dollar-variable syntax
collides with Julia's string interpolation, so MeTTa source embedded in
Julia code must use this macro (or `raw"..."`) to survive verbatim:

    program = metta\"\"\"
    (exec 0 (, (A \$x \$y) (B \$y \$z)) (, (Result \$x \$z)))
    \"\"\"

Equivalent to `raw"..."` — exists so MeTTa-bearing strings are
self-documenting at the call site.  Use everywhere MeTTa source is
embedded in Julia (tests, REPL helpers, generated programs).
"""
macro metta_str(s); s; end
