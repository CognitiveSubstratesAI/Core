# ActPC-Geom — Wasserstein natural gradient as a LEARNING preconditioner (general J≠I form).
# Goes beyond the transport toy: does the Wasserstein natural gradient LEARN a structured
# categorical model better than Euclidean / Fisher when the output support has metric structure?
#
# Task: input x → categorical over K ORDINAL bins; target = a Gaussian bump centered at a
# location that varies smoothly with x. Model: logits = W·[x,1] (W ∈ R^{K×2}); p = softmax.
# The output support is ordinal (a line) with ground metric ω (bin adjacency). Getting the
# bump LOCATION approximately right (nearby bins) should be "almost right" — exactly where
# Wasserstein geometry helps: it TRANSPORTS the predicted bump toward the target location,
# while Euclidean grows/shrinks bins independently (slow to shift a mislocated bump).
using LinearAlgebra, Random, Printf, Statistics

softmax(z) = (e=exp.(z .- maximum(z)); e ./ sum(e))
smjac(p) = Diagonal(p) .- p * p'
function meas_laplacian(p, ω)
    K = length(p)
    W = [i == j ? 0.0 : ω[i, j]*(p[i]+p[j]) for i in 1:K, j in 1:K]
    Diagonal(vec(sum(W; dims=2))) - W
end

function make_data(rng; n=40, K=11)
    X = range(-2.0, 2.0; length=n) |> collect
    bump(c) = (d=[exp(-((k-c)^2)/(2*1.0^2)) for k in 1:K]; d ./ sum(d))
    centers = [1 + (K-1) * (1/(1+exp(-x))) for x in X]   # smooth location ∈ [1,K]
    T = reduce(vcat, transpose.(bump.(centers)))          # (n,K) target bumps
    X, T, centers
end

# one optimizer epoch over the data; `mode` ∈ :euclid, :fisher, :wasser. Returns updated W + mean F.
function epoch!(W, X, T, ω; mode=:euclid, η=0.3, λ=1e-2, fdiag=nothing)
    K = size(T, 2)
    gW = zeros(size(W))
    Ftot = 0.0
    for i in eachindex(X)
        feat = [X[i], 1.0]
        p = softmax(W * feat)
        tgt = @view T[i, :]
        Ftot += 0.5 * sum((p .- tgt) .^ 2)
        glog = smjac(p) * (p .- tgt)                     # ∂F/∂logits
        if mode == :wasser
            J = smjac(p)                                  # ∂p/∂logits (J for the logit→p map)
            G = J' * pinv(meas_laplacian(p, ω)) * J       # AG41 metric in logit coords
            glog = (G + λ * I) \ glog                     # AG42 preconditioning (damped)
        end
        gW .+= glog * feat'                               # ∂/∂W
    end
    gW ./= length(X)
    if mode == :fisher
        fdiag .= 0.9 .* fdiag .+ 0.1 .* gW .^ 2           # Fisher-diagonal (FabricPC baseline)
        gW = gW ./ (sqrt.(fdiag) .+ 1e-3)
    end
    W .-= η .* gW
    return Ftot / length(X)
end

function run(; seed=0, epochs=200, K=11)
    rng = MersenneTwister(seed)
    X, T, centers = make_data(rng; K=K)
    ω = [exp(-(i-j)^2 / 2.0) for i in 1:K, j in 1:K]
    pred_center(W) =
        mean(abs(argmax(softmax(W*[X[i], 1.0])) - centers[i]) for i in eachindex(X))
    res = Dict{Symbol, Any}()
    for mode in (:euclid, :fisher, :wasser)
        W = 0.1 .* randn(MersenneTwister(99), K, 2)
        fdiag = zeros(K, 2)
        Ftraj = Float64[]
        for e in 1:epochs
            push!(Ftraj, epoch!(W, X, T, ω; mode=mode, fdiag=fdiag))
        end
        res[mode] = (Ffinal=Ftraj[end], F20=Ftraj[20], center_err=pred_center(W))
    end
    res
end

open("/tmp/jlmark", "w") do io
    for sd in 0:2
        r = run(; seed=sd)
        @printf(io,
            "seed %d  | F@20:  E=%.4f F=%.4f W=%.4f  | F_final: E=%.4f F=%.4f W=%.4f  | center-err(bins): E=%.2f F=%.2f W=%.2f\n",
            sd, r[:euclid].F20, r[:fisher].F20, r[:wasser].F20,
            r[:euclid].Ffinal, r[:fisher].Ffinal, r[:wasser].Ffinal,
            r[:euclid].center_err, r[:fisher].center_err, r[:wasser].center_err)
    end
    println(io, ">>>WNAT DONE")
end
