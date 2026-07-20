# tools/warm_session.jl — PERSISTENT warm MeTTaCore session with Revise hot-reload + a file-command
# loop (mirrors FabricPC's). Loads MeTTaCore ONCE; evaluates snippets on demand by watching
# `.warm/seq`, running `.warm/in.jl`, writing stdout/stderr to `.warm/out.txt`, echoing the seq into
# `.warm/done`. Round-trips are warm (<1s). Revise hot-reloads src/ edits between snippets — AND,
# because MorkSupercompiler is a PATH-dep of Core, edits to its src/ (e.g. SCPipeline.jl) hot-reload
# too. So iterating on Core OR the supercompiler needs NO cold restart.
#
# Start (persistent):  systemd-run --user --unit=core-warm --working-directory=$PWD \
#                          $(which julia) --project=. tools/warm_session.jl
# Drive it:            tools/warm_send.sh <snippet.jl>
# Revise MUST load before MeTTaCore so it tracks both packages' src/ files for hot-reload.
try
    using Revise
catch
    @warn "Revise unavailable — src edits will NOT hot-reload"
end
using MeTTaCore
import MorkSupercompiler   # ensure Revise tracks the path-dep's src/ (SCPipeline.jl etc.)

const DIR  = abspath(joinpath(@__DIR__, "..", ".warm"))
mkpath(DIR)
const INF  = joinpath(DIR, "in.jl")
const OUTF = joinpath(DIR, "out.txt")
const SEQF = joinpath(DIR, "seq")
const DONE = joinpath(DIR, "done")
function _serve()
    rm(INF; force = true); rm(DONE; force = true)
    write(joinpath(DIR, "ready"), "1")
    println("WARM SESSION READY (MeTTaCore + MorkSupercompiler loaded)")
    seen = ""
    while true
        if isfile(SEQF) && isfile(INF)
            n = strip(read(SEQF, String))
            if n != seen && !isempty(n)
                seen = n
                code = read(INF, String)
                # Revise FIRST, and surface failures LOUDLY. A bare `catch; end` here was the
                # swallow-revise-errors bug (feedback_warm_harness_swallows_revise_errors): a failed
                # revision drains the queue, throws, gets swallowed, and the session silently runs
                # STALE code — a silent-wrong-answer machine. `throw=true` + REFUSE to run the snippet
                # on failure, so a stale result can never masquerade as a fresh one.
                revise_fail = nothing
                if isdefined(Main, :Revise)
                    try
                        Base.invokelatest(Main.Revise.revise; throw = true)
                    catch e
                        revise_fail = (e, catch_backtrace())
                    end
                end
                open(OUTF, "w") do io
                    redirect_stdout(io) do
                        redirect_stderr(io) do
                            if revise_fail !== nothing
                                println(io, "REVISE FAILED — refusing to run this snippet (session would be STALE):")
                                showerror(io, revise_fail[1], revise_fail[2])
                                println(io)
                            else
                                try
                                    Base.include_string(Main, code)
                                catch e
                                    showerror(io, e, catch_backtrace())
                                    println(io)
                                end
                            end
                        end
                    end
                end
                write(DONE, n)
            end
        end
        sleep(0.15)
    end
end

_serve()
