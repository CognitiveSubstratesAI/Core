using MeTTaCore
const MC = MeTTaCore
const IV = MC.Eval; const IF = MC.CompilerFrontend
const IA = MC.CompilerANormal; const IE = MC.CompilerEmit
_parse(sp, t) = begin
    toks = IV.tokenize(t); i = Ref(1); out = MC.StandardMeTTa.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1); i[] > length(toks) && break
        push!(out, IV.parse_from(toks, i, sp.tokens))
    end
    out
end
root = normpath(joinpath(dirname(pathof(MeTTaCore)), ".."))
dir  = joinpath(root, "test", "standard", "conformance")
files = sort([joinpath(dir, f) for f in readdir(dir) if endswith(f, ".metta")])

# WHY the DECLINE REASON and not the count: the count says how much is missing, the reason says what
# to build. Emit.jl records a reason per declined clause precisely so this is answerable.
hist = Dict{String,Int}(); emitted = 0; declined = 0
for f in files
    sp = IV.Space(); IV.load_core_stdlib!(sp)
    cls = try IA.translate_program(IF.lower_program(_parse(sp, read(f, String)))) catch; continue end
    r = try IE.emit_program(cls) catch; continue end
    global emitted += r.emitted
    # `Emit.emit_program`'s `declined` is a Vector{ANClause} with NO reason attached — unlike
    # EmitIL's, which carries (name, reason) tuples. `decline_reason`/`decline_histogram` is the
    # attribution surface, and it recomputes the decline rather than reading a recorded one.
    for (why, n) in IE.decline_histogram(r.declined)
        global declined += n
        hist[String(why)] = get(hist, String(why), 0) + n
    end
end
println("="^76)
println("WHY Emit.jl DECLINES — 26-script conformance corpus")
println("="^76)
println("emitted=$emitted  declined=$declined  (", round(100*emitted/max(1,emitted+declined), digits=1), "% emitted)")
println("-"^76)
for (k, v) in sort(collect(hist); by = last, rev = true)
    println(rpad(first(k, 52), 54), lpad(v, 5), "  ", lpad(round(100v/max(1,declined), digits=1), 5), "%")
end
println("="^76)
println("Top row = the fragment that buys the most coverage next. Build against THAT, not the total.")
