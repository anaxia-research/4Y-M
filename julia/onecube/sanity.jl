# Numerical sanity checks (Float64, pseudo-random sampling). These are NOT proofs.
using LinearAlgebra, Random

sanity(name, msg) = println("  [sanity] ", rpad(name, 10), msg)

# ---------------------------------------------------------------------------
# Lemma W: minimum of Φ on SU(2)^3 by multistart local search.
function phi(q::AbstractVector)
    a = zeros(3); b = zeros(3, 3)
    for k in 1:3
        v = q[4k-3:4k]; v = v / norm(v)
        a[k] = v[1]; b[k, :] = v[2:4]
    end
    g(i, j) = dot(b[i, :], b[j, :])
    d = det(b)
    s = a[1] * a[2] * a[3] - a[1] * g(2, 3) - a[2] * g(1, 3) - a[3] * g(1, 2)
    A = sum(abs2, a)
    S = g(1, 2)^2 + g(1, 3)^2 + g(2, 3)^2
    A + 4 / 3 * (a[1]^2 * a[2]^2 + a[1]^2 * a[3]^2 + a[2]^2 * a[3]^2) + 4 / 3 * S + s^2 + d^2
end

function nelder_mead(f, x0; step = 0.3, iters = 4000, tol = 1e-15)
    n = length(x0)
    P = [copy(x0) for _ in 1:n+1]
    for i in 1:n; P[i+1][i] += step; end
    F = f.(P)
    for _ in 1:iters
        p = sortperm(F); P = P[p]; F = F[p]
        F[end] - F[1] < tol && break
        c = sum(P[1:n]) / n
        xr = c + (c - P[end]); fr = f(xr)
        if fr < F[1]
            xe = c + 2(c - P[end]); fe = f(xe)
            (P[end], F[end]) = fe < fr ? (xe, fe) : (xr, fr)
        elseif fr < F[n]
            P[end], F[end] = xr, fr
        else
            xc = c + 0.5(P[end] - c); fc = f(xc)
            if fc < F[end]
                P[end], F[end] = xc, fc
            else
                for i in 2:n+1; P[i] = P[1] + 0.5(P[i] - P[1]); F[i] = f(P[i]); end
            end
        end
    end
    i = argmin(F); P[i], F[i]
end

function sanity_phi(; starts = 400)
    rng = MersenneTwister(1)
    best = Inf; rawmin = Inf
    for _ in 1:20000
        rawmin = min(rawmin, phi(randn(rng, 12)))
    end
    for _ in 1:starts
        x, fx = nelder_mead(phi, randn(rng, 12))
        x, fx = nelder_mead(phi, x; step = 1e-3)
        best = min(best, fx)
    end
    sanity("Lemma W", "min Φ over 20000 random points = $(round(rawmin, digits=6)); " *
           "after $starts local searches = $(best) (source value ≈ 1.000000005; exact infimum 1)")
end

# ---------------------------------------------------------------------------
# Free gluon X_G(T)/(N²-1) on the (2T)^3 × T torus and its continuum limit.
function XG(T)
    L = 2T; s = 0.0
    for n1 in 0:L-1, n2 in 0:L-1, n3 in 0:L-1
        (n1, n2, n3) == (0, 0, 0) && continue
        sh = sqrt(sin(π * n1 / L)^2 + sin(π * n2 / L)^2 + sin(π * n3 / L)^2)
        ω = 2asinh(sh)
        s += -2log1p(-exp(-T * ω))
    end
    s
end
function XGcont(R = 40)
    s = 0.0
    for n1 in -R:R, n2 in -R:R, n3 in -R:R
        (n1, n2, n3) == (0, 0, 0) && continue
        s += -2log1p(-exp(-π * sqrt(n1^2 + n2^2 + n3^2)))
    end
    s
end
function sanity_XG()
    vals = [(T, XG(T)) for T in (3, 4, 6, 8)]
    sanity("X_G", join(["T=$T: $(round(v, digits=4))" for (T, v) in vals], ", ") *
           " (source 2.2063, 1.6520, 1.2187, 1.1015); limit $(round(XGcont(), digits=6)) (source 0.984703), per N²-1")
end

# ---------------------------------------------------------------------------
# W3 R4: finite-difference Hessian of the twisted SU(2) action at a twist eater.
const σ1 = ComplexF64[0 1; 1 0]; const σ2 = ComplexF64[0 -im; im 0]; const σ3 = ComplexF64[1 0; 0 -1]
const I2 = Matrix{ComplexF64}(I, 2, 2)
su2exp(x) = (r = norm(x); r == 0 ? I2 : cos(r) * I2 + im * sin(r) / r * (x[1]σ1 + x[2]σ2 + x[3]σ3))
randsu2(rng) = (v = randn(rng, 4); v /= norm(v); v[1] * I2 + im * (v[2]σ1 + v[3]σ2 + v[4]σ3))

function hess_rank(dims, k; twisted = true, rng = MersenneTwister(2), h = 1e-4)
    sites = vec(collect(Iterators.product((0:d-1 for d in dims)...)))
    idx = Dict(s => i for (i, s) in enumerate(sites))
    nV = length(sites); nE = 4nV
    sh(x, μ) = ntuple(i -> i == μ ? mod(x[i] + 1, dims[i]) : x[i], 4)
    link(x, μ) = 4(idx[x] - 1) + μ
    U = Vector{Matrix{ComplexF64}}(undef, nE)
    θ = rand(rng, 4) .* 2 .+ 0.5
    for x in sites, μ in 1:4
        if twisted
            M = I2
            if μ <= 3 && k[μ] == 1 && x[μ] == dims[μ] - 1; M = im * σ1; end
            if μ == 4 && x[4] == dims[4] - 1; M = im * σ3; end
            U[link(x, μ)] = M
        else
            U[link(x, μ)] = su2exp([0, 0, θ[μ] / dims[μ]])
        end
    end
    g = Dict(x => randsu2(rng) for x in sites)        # random gauge transformation
    for x in sites, μ in 1:4
        U[link(x, μ)] = g[x] * U[link(x, μ)] * g[sh(x, μ)]'
    end
    plaqs = Tuple{Int,Int,Int,Int,Float64}[]
    for x in sites, μ in 1:4, ν in μ+1:4
        η = (twisted && ν == 4 && μ <= 3 && k[μ] == 1 && x[μ] == dims[μ] - 1 && x[4] == dims[4] - 1) ? -1.0 : 1.0
        push!(plaqs, (link(x, μ), link(sh(x, μ), ν), link(sh(x, ν), μ), link(x, ν), η))
    end
    function S(X)
        V = [su2exp(X[3l-2:3l]) * U[l] for l in 1:nE]
        tot = 0.0
        for (a, b, c, d, η) in plaqs
            tot += 1 - 0.5η * real(tr(V[a] * V[b] * V[c]' * V[d]'))
        end
        tot
    end
    n = 3nE; H = zeros(n, n); e = zeros(n)
    S0 = S(e)
    Sp = zeros(n); Sm = zeros(n)
    for i in 1:n
        e[i] = h; Sp[i] = S(e); e[i] = -h; Sm[i] = S(e); e[i] = 0
        H[i, i] = (Sp[i] - 2S0 + Sm[i]) / h^2
    end
    Threads.@threads for i in 1:n
        ee = zeros(n)
        for j in i+1:n
            ee[i] = h; ee[j] = h; spp = S(ee); ee[j] = -h; spm = S(ee)
            ee[i] = -h; smm = S(ee); ee[j] = h; smp = S(ee); ee[i] = 0; ee[j] = 0
            H[i, j] = H[j, i] = (spp - spm - smp + smm) / (4h^2)
        end
    end
    λ = eigvals(Symmetric(H))
    pos = filter(>(1e-3), λ)
    (count(>(1e-3), λ), nV, minimum(pos), maximum(abs.(filter(x -> abs(x) <= 1e-3, λ))), S0)
end

function sanity_hessian()
    for (dims, k, tw) in (((2, 2, 2, 2), (1, 0, 0), true), ((2, 2, 2, 2), (1, 1, 1), true),
                          ((2, 2, 2, 2), (0, 0, 0), false))
        r, nV, mp, kz, S0 = hess_rank(dims, k; twisted = tw)
        lab = tw ? "twist eater k=$k" : "untwisted abelian flat point"
        exp_ = tw ? 9nV : 9nV - 3
        sanity("W3 R4", "$(join(dims, "×")), $lab: S=$(round(S0, sigdigits=2)), Hessian rank $r " *
               "(expected $exp_), smallest positive eigenvalue $(round(mp, digits=3)), |kernel| ≤ $(round(kz, sigdigits=2))")
    end
end

# ---------------------------------------------------------------------------
# Model A (X1): site-reflection Gram matrix, summability, log Z − e_N n^4.
function dft4(f::Array{Float64,4})
    n = size(f, 1)
    W = [cis(2π * j * k / n) for j in 0:n-1, k in 0:n-1]
    g = complex(f)
    for d in 1:4
        g = mapslices(v -> W * v, g; dims = d)
    end
    g
end
function covariance(n, ma, c)
    D = zeros(n, n, n, n)
    for I in CartesianIndices(D)
        kk = Tuple(I) .- 1
        D[I] = ma^2 + sum(c[ν]^2 * (2sin(π * kk[ν] / n))^2 for ν in 1:4)
    end
    real.(dft4(1 ./ D)) ./ n^4
end
function gram_min(n, ma, c, ν)
    C = covariance(n, ma, c)
    half = [x for x in Iterators.product(0:n-1, 0:n-1, 0:n-1, 0:n-1) if x[ν] <= n ÷ 2]
    refl(x) = ntuple(i -> i == ν ? mod(-x[i], n) : x[i], 4)
    M = [C[CartesianIndex(mod.(refl(x) .- y, n) .+ 1)] for x in half, y in half]
    λ = eigvals(Symmetric(M))
    minimum(λ), length(half)
end
function sanity_modelA()
    worst = Inf
    for n in (4, 6), c0 in (sqrt(2.0), 0.5), ν in 1:4
        λmin, _ = gram_min(n, 0.5, (c0, 1.0, 1.0, 1.0), ν)
        worst = min(worst, λmin)
    end
    sanity("Model A", "site-reflection Gram matrices [C(ϑx-y)] on 4⁴ and 6⁴, c₀ ∈ {√2, 1/2}, ma = 1/2, " *
           "all four directions: smallest eigenvalue $(worst) (source: ≥ -1.1e-15)")
    # summability: Σ_{k∈Z^8} (1+|k|_∞)^{m k0 - s}, m = 2, k0 = 1
    for s in 10:13
        tot = 1.0
        for j in 1:20000
            tot += Float64((2Int128(j) + 1)^8 - (2Int128(j) - 1)^8) * (1.0 + j)^(2 - s)
        end
        sanity("X1 sum", "s=$s: partial sum to |k|_∞ = 2·10⁴ is $(round(tot, digits=3)) " *
               "(source 15065, 280.8, 37.69, 9.993 for s = 10..13)")
    end
    # log Z − e_N n^4, four copies, m = 1, c^2 = 2, L_p = 1
    c = sqrt(2.0)
    for N in (4, 8, 16, 24)
        n = N; ma = 1 / N
        tot = 0.0
        Icache = Dict{Any,Float64}()
        for μ in 1:4
            cs = ntuple(ν -> ν == μ ? c : 1.0, 4)
            c0 = cs[1]; ci = cs[2:4]
            sD = 0.0
            for I in CartesianIndices((n, n, n, n))
                kk = Tuple(I) .- 1
                sD += log(ma^2 + sum(cs[ν]^2 * (2sin(π * kk[ν] / n))^2 for ν in 1:4))
            end
            # ∫ ω d³k/(2π)³, cosh ω = 1 + A/(2c₀²), by the periodic trapezoid rule (M points per axis,
            # error exponentially small in M·ma) using the symmetry k_i ↦ -k_i
            key = (c0, sort(collect(ci)))
            Iω = get!(Icache, key) do
                M = 30N; h = M ÷ 2
                wt(j) = (j == 0 || j == h) ? 1.0 : 2.0
                sv = [(2sin(π * j / M))^2 for j in 0:h]
                part = zeros(Threads.nthreads())
                Threads.@threads for j1 in 0:h
                    acc = 0.0
                    for j2 in 0:h, j3 in 0:h
                        A = ma^2 + ci[1]^2 * sv[j1+1] + ci[2]^2 * sv[j2+1] + ci[3]^2 * sv[j3+1]
                        acc += wt(j1) * wt(j2) * wt(j3) * 2asinh(sqrt(A) / (2c0))
                    end
                    part[Threads.threadid()] += acc
                end
                sum(part) / M^3
            end
            tot += 0.5 * (n^4 * (Iω + 2log(c0)) - sD)
        end
        sanity("Model A", "L_p = 1, N = $N: log Z - e_N n⁴ = $(round(tot, digits=3)) (source 5.28, 4.53, 4.39, 4.37 for N = 4, 8, 16, 24)")
    end
end

# ---------------------------------------------------------------------------
# W7 Prop 6: the two-state system and the rings.
function sanity_W7()
    xc = 1 / 4159.5
    for N in (10, 100, 1000)
        t = 1.0; T = floor(Int, N * t)
        X2 = log1p(exp(-8.0 * T^4 / N^5))
        r = exp(-1.0 / N)                          # Δ = 1
        Xr = 8.0 * T^3 * log1p(r^T)
        sanity("W7 P6", "N=$N, T=⌊N⌋: two-state X = $(round(X2, digits=6)) (→ log 2 = 0.693147 > x_c ≈ $(round(xc, sigdigits=4))), " *
               "rings X = $(round(Xr, sigdigits=6)) (→ ∞)")
    end
    # PSTS structure: Z(s, M) = Tr T_s^M and the inequality D(2M) ≤ D(M)^2 of (E2)
    q = exp(-1e-3); V = 8
    ok = true
    for M in 2:20
        Ts = Diagonal([1.0, q^V])
        ok &= isapprox(tr(Ts^M), 1 + q^(V * M); rtol = 1e-12)
        D(M) = q^(V * M)
        ok &= D(2M) <= D(M)^2 * (1 + 1e-12)
    end
    sanity("W7 P6", "two-state system: Z = Tr diag(1, q^V)^M = 1 + q^{VM} and D(2M) ≤ D(M)² for M = 2..20: $(ok)")
end

# ---------------------------------------------------------------------------
# L Thm A model: Monte Carlo of Tr K and Tr K² (SU(2), 1×1×T torus in 2+1 D).
besselI1(x) = sum((x / 2)^(2k + 1) / (factorial(big(k)) * factorial(big(k + 1))) for k in 0:60) |> Float64

function mc_trK(β, T, nsamp; seed = 3)
    Nn = 2 / β * besselI1(β)
    nt = Threads.nthreads()
    sums = zeros(nt); sums2 = zeros(nt)
    chunk = cld(nsamp, nt)
    Threads.@threads for t in 1:nt
        rng = MersenneTwister(seed + t)
        s = 0.0; s2 = 0.0
        for _ in 1:chunk
            U1 = [randsu2(rng) for _ in 1:T]; U2 = [randsu2(rng) for _ in 1:T]
            V = [randsu2(rng) for _ in 1:T]
            lw = 0.0
            for τ in 1:T
                τ1 = mod1(τ + 1, T)
                lw += β / 2 * real(tr(U1[τ] * U2[τ] * U1[τ]' * U2[τ]'))
                lw += β / 2 * real(tr(U1[τ] * V[τ] * U1[τ1]' * V[τ]'))
                lw += β / 2 * real(tr(U2[τ] * V[τ] * U2[τ1]' * V[τ]'))
            end
            w = exp(lw) / Nn^(2T)
            s += w; s2 += w^2
        end
        sums[t] = s; sums2[t] = s2
    end
    n = chunk * nt
    m = sum(sums) / n
    m, sqrt((sum(sums2) / n - m^2) / n)
end
function sanity_LThmA(; nsamp = 2_000_000)
    for (β, ref1, ref2) in ((1.0, 2.778247, 2.525462), (2.0, 10.01709, 13.8185))
        m1, e1 = mc_trK(β, 1, nsamp)
        m2, e2 = mc_trK(β, 2, nsamp)
        sanity("L Thm A", "β=$β: MC Tr K = $(round(m1, digits=4)) ± $(round(e1, digits=4)) (exact-matrix value $ref1), " *
               "Tr K² = $(round(m2, digits=4)) ± $(round(e2, digits=4)) ($ref2); $nsamp samples")
    end
end

function run_sanity()
    println("\n== Numerical sanity checks (floating point; not proofs) ==")
    println("  threads: ", Threads.nthreads())
    for f in (sanity_phi, sanity_XG, sanity_hessian, sanity_modelA, sanity_W7, sanity_LThmA)
        t = @elapsed f()
        println("    (", f, ": ", round(t, digits=1), " s)")
    end
end
