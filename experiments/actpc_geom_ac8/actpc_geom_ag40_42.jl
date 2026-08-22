# ActPC-Geom AG40–42 — Wasserstein natural gradient (paper §3; spec actpc_geom_spec.md).
# UNBUILT EVERYWHERE. Core equations:
#   AG40  L(p)_ij = ω_ij(p_i+p_j), i≠j   (measure-dependent graph Laplacian, PSD D−W form)
#   AG41  G(ξ)    = Jᵀ L(p(ξ))† J         (Wasserstein metric tensor)
#   AG42  ξ ← ξ − η G⁻¹ ∇_ξ F             (natural-gradient step on the Wasserstein manifold)
# Demonstrated in the canonical instantiation ξ = p (identity parameterization, J = I) ⇒
# G = L†, G⁻¹ = L, so the update is  p ← p − η·L(p)·∇_p F  — the measure-weighted graph
# Laplacian applied to the gradient, which is exactly the discrete optimal-transport FLUX:
# (L∇F)_i = Σ_j ω_ij(p_i+p_j)(∇F_i − ∇F_j) routes mass along graph edges.
#
# GATE — the defining Wasserstein property: minimizing an energy that moves mass across a
# ground-metric graph, the Wasserstein natural gradient TRANSPORTS mass through intermediate
# support points (optimal-transport flow), whereas the Euclidean gradient TELEPORTS it.
#   GEO-1: converges + L PSD (valid metric).  GEO-2: Wasserstein routes mass through the
#   middle; Euclidean does not.
using LinearAlgebra, Printf

# AG40: measure-dependent Laplacian L = D − W, W_ij = ω_ij(p_i+p_j) (i≠j). PSD, null = 1.
function meas_laplacian(p, ω)
    K = length(p)
    W = [i == j ? 0.0 : ω[i, j] * (p[i] + p[j]) for i in 1:K, j in 1:K]
    return Diagonal(vec(sum(W; dims=2))) - W
end
gradF_p(p, tgt) = p .- tgt                                   # ∂/∂p of ½‖p−tgt‖²
project_simplex(p) = (q=max.(p, 0.0); q ./ sum(q))         # keep on the probability simplex

# AG42 with ξ=p, J=I, G⁻¹=L:  p ← p − η·L(p)·∇F  (the optimal-transport flux). L PSD ⇒ F↓.
function step_wasserstein(p, tgt, ω; η=0.5)
    L = meas_laplacian(p, ω)
    return project_simplex(p .- η .* (L * gradF_p(p, tgt))), L
end
step_euclid(p, tgt; η=0.5) = project_simplex(p .- η .* gradF_p(p, tgt))  # ignores the ground metric

function run(; K=9, steps=300)
    ω = [exp(-(i - j)^2 / 2.0) for i in 1:K, j in 1:K]       # LOCAL ground metric (line graph)
    p0 = project_simplex([i == 1 ? 1.0 : 1e-4 for i in 1:K]) # start: mass at point 1
    tgt = project_simplex([i == K ? 1.0 : 1e-4 for i in 1:K])# target: mass at point K
    mid = (1 + K) ÷ 2

    psd_ok = true
    midw = Float64[]
    mide = Float64[]
    Fw = Float64[]
    Fe = Float64[]
    pw = copy(p0)
    pe = copy(p0)
    for t in 1:steps
        pw, L = step_wasserstein(pw, tgt, ω)
        psd_ok &= (minimum(eigvals(Symmetric(0.5 * (L + L')))) > -1e-8)   # L PSD
        pe = step_euclid(pe, tgt)
        push!(midw, sum(@view pw[(mid - 1):(mid + 1)]))
        push!(mide, sum(@view pe[(mid - 1):(mid + 1)]))
        push!(Fw, 0.5sum((pw .- tgt) .^ 2))
        push!(Fe, 0.5sum((pe .- tgt) .^ 2))
    end
    return (; midw, mide, Fw, Fe, psd_ok, pw, pe)
end

# 2D-grid variant: ground metric = exp(−grid-dist²); transport must route across cells.
function run_grid(; g=4, steps=300)
    K = g * g
    pos = [((k-1)%g, (k-1)÷g) for k in 1:K]
    ω = [
        exp(-((pos[i][1]-pos[j][1])^2 + (pos[i][2]-pos[j][2])^2)/2.0) for i in 1:K, j in 1:K
    ]
    p0 = project_simplex([k == 1 ? 1.0 : 1e-4 for k in 1:K])      # corner (0,0)
    tgt = project_simplex([k == K ? 1.0 : 1e-4 for k in 1:K])     # opposite corner
    center = findall(k -> pos[k][1] in (g÷2-1, g÷2) && pos[k][2] in (g÷2-1, g÷2), 1:K)
    pw = copy(p0)
    pe = copy(p0)
    midw = 0.0
    mide = 0.0
    for _ in 1:steps
        pw, _ = step_wasserstein(pw, tgt, ω)
        pe = step_euclid(pe, tgt)
        midw = max(midw, sum(pw[center]))
        mide = max(mide, sum(pe[center]))
    end
    (; midw, mide, Fw=0.5sum((pw .- tgt) .^ 2), Fe=0.5sum((pe .- tgt) .^ 2))
end

open("/tmp/jlmark", "w") do io
    allpass = true
    for K in (5, 9, 13)
        r = run(; K=K)
        g2 = maximum(r.midw) > 0.03 && maximum(r.midw) > 5 * (maximum(r.mide) + 1e-6)
        g1 = r.Fw[end] < 0.05 && r.psd_ok
        allpass &= (g1 && g2)
        @printf(io,
            "line K=%2d: Fw→%.4f PSD=%s | mid-mass Wass %.3f vs Euclid %.3f | GEO-1=%s GEO-2=%s\n",
            K, r.Fw[end], r.psd_ok, maximum(r.midw), maximum(r.mide), g1, g2)
    end
    rg = run_grid()
    g2g = rg.midw > 0.03 && rg.midw > 5 * (rg.mide + 1e-6)
    @printf(io,
        "GRID 4x4: Fw→%.4f | center-mass Wass %.3f vs Euclid %.3f | transport-across-grid=%s\n",
        rg.Fw, rg.midw, rg.mide, g2g)
    @printf(
        io,
        "ALL CONFIGS: GEO-1 (converge+PSD) & GEO-2 (transport≫teleport) = %s\n",
        allpass && g2g
    )
    println(io, ">>>GEOM DONE")
end
