# The interval / transcendental constants J1–J12 (J13 is not used by the paper).
# Decimal numbers d"..." are the exact rationals they spell.

E(x) = exp(iv(x))
L(x) = log(iv(x))

function J1()
    println("\n== J1: fixed point of f(x) = (e^{64x} - 1)^2 ==")
    f(x) = expm1(64 * iv(x))^2
    claim("J1", "4160 f(1/4160) < 0.99991", 4160 * f(big(1) // 4160), :lt, d"0.99991")
    claim("J1", "4159 f(1/4159) > 1.00014", 4159 * f(big(1) // 4159), :gt, d"1.00014")
    claim("J1", "f(1/4160) < 1/4160 (as 4160 f(1/4160) < 1)", 4160 * f(big(1) // 4160), :lt, big(1) // 1)
    claim("J1", "f(1/4159) > 1/4159 (as 4159 f(1/4159) > 1)", 4159 * f(big(1) // 4159), :gt, big(1) // 1)
    claim("J1", "e^{1/4159} < 2", E(big(1) // 4159), :lt, big(2) // 1)
end

function J2()
    println("\n== J2: the ascent constants, u = 32/63, θ = 127/126 ==")
    u = big(32) // 63; θ = big(127) // 126
    x = iv(big(1) // 8192)
    for i in 0:5
        v = expm1(64 * x)
        claim("J2", "v_$i = e^{64 x_$i} - 1 ≤ θ^{-1} u^{2^$i}/64 (paper form)", v, :le, u^(2^i) / (64θ))
        claim("J2", "v_$i ≤ u^{2^$i}/64 (PLAN form)", v, :le, u^(2^i) / 64)
        x = v^2
    end
    claim("J2", "log(63/32) > 0.67725", L(big(63) // 32), :gt, d"0.67725")
    claimq("J2", "0.67725 > 0.677", d"0.67725", :gt, d"0.677")
    claim("J2", "e^{0.677} < 63/32", E(d"0.677"), :lt, big(63) // 32)
    claim("J2", "e^{0.67725} < 1.96846", E(d"0.67725"), :lt, d"1.96846")
    claimq("J2", "u^8 < 1/128", u^8, :lt, big(1) // 128)
    claimq("J2", "u^8 < 0.00444", u^8, :lt, d"0.00444")
    claimq("J2", "θ^{-1} u/64 = 1/127", u / (64θ), :ge, big(1) // 127)
    claimq("J2", "64/127^2 < 1/252", big(64) // 127^2, :lt, big(1) // 252)
    claimq("J2", "252/251 ≤ θ", big(252) // 251, :le, θ)
end

function J3()
    println("\n== J3: 13 log 2 and the excitation thresholds ==")
    l2 = L(2)
    claim("J3", "13 log 2 > 9.0109", 13 * l2, :gt, d"9.0109")
    claim("J3", "13 log 2 < 9.011", 13 * l2, :lt, d"9.011")
    t1 = -log(expm1(iv(big(1) // 8192)))
    claim("J3", "-log(e^{1/8192} - 1) > 9.0108", t1, :gt, d"9.0108")
    claim("J3", "-log(e^{1/8192} - 1) < 9.01086 (value 9.01085...)", t1, :lt, d"9.01086")
    claim("J3", "-log(e^{1/8192} - 1) < 13 log 2 (difference > 0)", 13 * l2 - t1, :gt, big(0) // 1)
    claim("J3", "14 log 2 > 9.70406052", 14 * l2, :gt, d"9.70406052")
    claim("J3", "14 log 2 < 9.70406053", 14 * l2, :lt, d"9.70406053")
    t2 = -log(expm1(iv(big(1) // 2^14)))
    claim("J3", "-log(e^{2^-14} - 1) > 9.70403", t2, :gt, d"9.70403")
    claim("J3", "-log(e^{2^-14} - 1) < 9.70404", t2, :lt, d"9.70404")
    claim("J3", "13 log 2 - 2^-13 > 9.0107", 13 * l2 - big(1) // 8192, :gt, d"9.0107")
    claim("J3", "e^{2^-13} - 1 ≤ 2^-13 (1 + 2^-13)", expm1(iv(big(1) // 8192)), :le, (big(1) // 8192) * (1 + big(1) // 8192))
    claimq("J3", "2^-13 (1 + 2^-13) < 1/8191", (big(1) // 8192) * (1 + big(1) // 8192), :lt, big(1) // 8191)
    claimq("J3", "2^-12 (1 + 2^-13) < 1/4095", (big(1) // 4096) * (1 + big(1) // 8192), :lt, big(1) // 4095)
    claim("J3", "8192 e^{-9.01} > 1", 8192 * E(-d"9.01"), :gt, big(1) // 1)
    claim("J3", "e^{9.0109} < 8191.9", E(d"9.0109"), :lt, d"8191.9")
    claim("J3", "e^{9.011} > 8192.7", E(d"9.011"), :gt, d"8192.7")
    claim("J3", "e^{9.01} < 8184.6", E(d"9.01"), :lt, d"8184.6")
end

function J4()
    println("\n== J4: free-gluon reference constants ==")
    em = exp(-PI)
    claim("J4", "e^{-π} > 0.04321", em, :gt, d"0.04321")
    claim("J4", "12 e^{-π} > 0.51856 (> 0.518 > 4248/8192)", 12 * em, :gt, d"0.51856")
    claim("J4", "24 e^{-π} > 1.03713 (> 4249/4097)", 24 * em, :gt, d"1.03713")
    claim("J4", "12·8192 e^{-π} > 4248", 12 * 8192 * em, :gt, big(4248) // 1)
    claim("J4", "24·4097 e^{-π} > 4249", 24 * 4097 * em, :gt, big(4249) // 1)
    claim("J4", "e^{3.141593} < 23.1408", E(d"3.141593"), :lt, d"23.1408")
    claim("J4", "e^{π} < 23.1408", exp(PI), :lt, d"23.1408")
    claimq("J4", "23.1408 < 98304/4248", d"23.1408", :lt, big(98304) // 4248)
    claimq("J4", "98328/23.1408 > 4249.1", 98328 / d"23.1408", :gt, d"4249.1")
    claim("J4", "e^{2π} < 535.5", exp(2 * PI), :lt, d"535.5")
    claim("J4", "12 e^{-2π} > 0.02240", 12 * exp(-2 * PI), :gt, d"0.02240")
    claimq("J4", "0.0223 > 2^-13", d"0.0223", :gt, big(1) // 8192)
    claim("J4", "9.01/(2π) > 1.43", d"9.01" / (2 * PI), :gt, d"1.43")
    y = exp(-2 * PI)
    claim("J4", "log(1 + e^{-2π}) > 1.8656e-3", log1p(y), :gt, d"1.8656e-3")
    claim("J4", "log(1 + e^{-2π}) > 15/8192", log1p(y), :gt, big(15) // 8192)
    claim("J4", "e^{-2π} > 1.86e-3", y, :gt, d"1.86e-3")
    claim("J4", "e^{9.0108 - π} > 353.9", exp(iv(d"9.0108") - PI), :gt, d"353.9")
    claim("J4", "e^{9.0108} > 8191", E(d"9.0108"), :gt, big(8191) // 1)
    s3 = sqrt(iv(3))
    claim("J4", "log(2+√3) - 0.76√3 ≥ 0", log(2 + s3) - d"0.76" * s3, :ge, big(0) // 1)
    claim("J4", "e^{1.31637} < 3.72986", E(d"1.31637"), :lt, d"3.72986")
    claim("J4", "2 + √3 > 3.72986", 2 + s3, :gt, d"3.72986")
    claim("J4", "0.76√3 < 1.31637", d"0.76" * s3, :lt, d"1.31637")
    b = d"1.52" / s3
    C = 2 / (1 - exp(-iv(d"1.52"))) * (((1 + exp(-b)) / (1 - exp(-b)))^3 - 1)
    claim("J4", "count constant C ≤ 33.88 (value 33.8745...)", C, :le, d"33.88")
    claim("J4", "count constant C < 33.878", C, :lt, d"33.878")
    claim("J4", "count constant C < 34", C, :lt, big(34) // 1)
    claim("J4", "count constant C ≤ 33.8746 (PLAN value 33.8745)", C, :le, d"33.8746")
    claim("J4", "count constant C > 33.8745", C, :gt, d"33.8745")
    claim("J4", "e^{1.52} > 4.5722", E(d"1.52"), :gt, d"4.5722")
    claim("J4", "e^{0.87757} > 2.405", E(d"0.87757"), :gt, d"2.405")
    claim("J4", "b = 1.52/√3 > 0.87757", b, :gt, d"0.87757")
    claimq("J4", "certificate value 2/(1-1/4.5722)[((1+1/2.405)/(1-1/2.405))^3-1] < 33.878",
        2 / (1 - 1 / d"4.5722") * (((1 + 1 / d"2.405") / (1 - 1 / d"2.405"))^3 - 1), :lt, d"33.878")
    claim("J4", "12 log 2 > 8.3176", 12 * L(2), :gt, d"8.3176")
    claim("J4", "e^{2.0794} < 7.9997", E(d"2.0794"), :lt, d"7.9997")
    claim("J4", "2π < 6.283186", 2 * PI, :lt, d"6.283186")
    claimq("J4", "8.3176 > 8.317 > 6.283186", d"8.317", :gt, d"6.283186")
    claimq("J4", "1.43·6.283186 < 8.986", d"1.43" * d"6.283186", :lt, d"8.986")
    # f(k) = -log(1 - e^{-2π/k}) (2k/(k-1))^6 ≥ 81 for k > 1
    g1(k) = -log(1 - exp(-2 * PI / iv(k)))      # increasing in k
    g2(k) = (2 * iv(k) / (iv(k) - 1))^6         # decreasing in k
    ok = true; worst = big(Inf)
    a = big(5) // 4
    while a < 20
        bb = a + big(1) // 500
        lo = g1(a) * g2(bb)
        worst = min(worst, lo.lo); ok &= lo.lo >= 81
        a = bb
    end
    check("J4", "f(k) ≥ 81 on [1.25, 20] (grid 1/500, factors at opposite ends)", ok,
        "smallest lower bound $(Float64(worst))")
    claim("J4", "k ≥ 20: -log(1 - e^{-2π/20}) > 1.31", g1(20), :gt, d"1.31")
    claimq("J4", "64·1.31 > 83.8", 64 * d"1.31", :gt, d"83.8")
    claim("J4", "k ≤ 1.25: e^{-2π} > 1.86e-3 and 10^6·1.86e-3 ≥ 81", 10^6 * y, :ge, big(81) // 1)
end

function J5()
    println("\n== J5: base-scale and abelian constants ==")
    D = expm1(iv(big(1) // (5 * 96^3)))
    claim("J5", "D = e^{1/(5·96^3)} - 1 ≤ 2.2606e-7", D, :le, d"2.2606e-7")
    claim("J5", "D ≥ 2.26056155e-7 (PLAN value 2.2605616e-7, rounded)", D, :ge, d"2.26056155e-7")
    claim("J5", "D < 2.26056165e-7 (PLAN value 2.2605616e-7, rounded)", D, :lt, d"2.26056165e-7")
    claim("J5", "log(1/D) ≥ 15.3024", -log(D), :ge, d"15.3024")
    claim("J5", "1 - e^{-1} ≥ 0.632", 1 - E(-1), :ge, d"0.632")
    eps(b) = 12 / iv(b) * (log(iv(b)) + d"5.42")
    claim("J5", "ε(6·10^6) < 4.2055e-5", eps(6 * 10^6), :lt, d"4.2055e-5")
    claim("J5", "ε(6·10^6) < 4.89126e-5 (PLAN)", eps(6 * 10^6), :lt, d"4.89126e-5")
    claimq("J5", "ε_0 = 0.632^3/(56·9.6^2) > 4.8912e-5", d"0.632"^3 / (56 * d"9.6"^2), :gt, d"4.8912e-5")
    claimq("J5", "ε_0 < 4.89126e-5 (value 4.8912599...e-5, displayed as 4.8913e-5)", d"0.632"^3 / (56 * d"9.6"^2), :lt, d"4.89126e-5")
    claimq("J5", "0.632·15.30 ≥ 9.6", d"0.632" * d"15.30", :ge, d"9.6")
    claimq("J5", "9.6/0.632 < 15.19", d"9.6" / d"0.632", :lt, d"15.19")
    claim("J5", "D e^{1/4} ≤ 2.903e-7", D * E(big(1) // 4), :le, d"2.903e-7")
    claim("J5", "log(1.5 - 1.4515e-7) ≥ 0.405465", L(d"1.5" - d"1.4515e-7"), :ge, d"0.405465")
    claim("J5", "log 1.5 > 0.40546510", L(big(3) // 2), :gt, d"0.40546510")
    claimq("J5", "d/(1.5-d) < 9.677e-8, d = 1.4515e-7", d"1.4515e-7" / (d"1.5" - d"1.4515e-7"), :lt, d"9.677e-8")
    claimq("J5", "0.405465/70.4 > 0.0057594", d"0.405465" / d"70.4", :gt, d"0.0057594")
    claimq("J5", "0.2754^4 < 0.0057525", d"0.2754"^4, :lt, d"0.0057525")
    claimq("J5", "0.405465/70.4 > 0.2754^4", d"0.405465" / d"70.4", :gt, d"0.2754"^4)
    # Correct the former source sentence T_0 >= 116.7 (no consumer in the
    # paper). It is false. Certify the unique root on [100,130] instead;
    # see CORRECTIONS.md. Here K > 0 and h'(T)=3T^2-7.65K/T^2.
    β = 10^9
    K = iv(β) / (d"21.97" * (log(iv(2β)) + d"5.42"))
    h(T) = iv(T)^3 - (1 - d"7.65" / iv(T)) * K
    claim("J5", "K > 0 (root equation coefficient)", K, :gt, big(0)//1)
    claim("J5", "h(100) < 0 (left root bracket)", h(100), :lt, big(0)//1)
    claim("J5", "h(130) > 0 (right root bracket)", h(130), :gt, big(0)//1)
    # For every T in [100,130], T^2 >= 100^2, so this is a lower bound on h'(T).
    derivative_floor = 3 * iv(100)^2 - d"7.65" * K / iv(100)^2
    claim("J5", "h'(T) >= 3*100^2 - 7.65K/100^2 > 0 on [100,130]",
        derivative_floor, :gt, big(0)//1)
    claim("J5", "h(116.5888) < 0 (corrected strict lower bracket)",
        h(d"116.5888"), :lt, big(0)//1)
    claim("J5", "h(116.5889) > 0 (corrected strict upper bracket)",
        h(d"116.5889"), :gt, big(0)//1)
    lo, hi = big(100) // 1, big(130) // 1
    for _ in 1:60
        m = (lo + hi) / 2
        hm = h(m)
        if hm.hi < 0; lo = m elseif hm.lo > 0; hi = m else break end
    end
    # The root lies between lo and hi, not in the single-point interval iv(hi).
    root = Iv(iv(lo).lo, iv(hi).hi)
    claim("J5", "corrected beta=10^9 root: T_0 > 116.5888", root, :gt, d"116.5888")
    claim("J5", "corrected beta=10^9 root: T_0 < 116.5889", root, :lt, d"116.5889")
    claim("J5", "counterexample to former T_0 >= 116.7: T_0 < 116.7",
        root, :lt, d"116.7")
    println("      root T_0 ∈ [$(Float64(lo)), $(Float64(hi))]")
    # thm:SUN-gap row (no identifier)
    claimq("J5x", "(1 - 0.58^2/6)^2 > 0.94^2", (1 - d"0.58"^2 / 6)^2, :gt, d"0.94"^2)
    c2inv = 3 * sqrt(iv(2)) * PI / d"0.94"^3
    claim("J5x", "1/c_2 = 3√2 π/0.94^3 < 16.0475", c2inv, :lt, d"16.0475")
    claimq("J5x", "certificate 3·1.41422·3.1416/0.94^3 < 16.0475", 3 * d"1.41422" * d"3.1416" / d"0.94"^3, :lt, d"16.0475")
    claim("J5x", "(2/3) log 16.05 < 1.8505", (big(2) // 3) * L(d"16.05"), :lt, d"1.8505")
    claim("J5x", "log 8 < 2.0795", L(8), :lt, d"2.0795")
    claim("J5x", "1 + (2/3) log(1/c_2) + log 8 < 4.931", 1 + (big(2) // 3) * log(c2inv) + L(8), :lt, d"4.931")
    # one-cube SU(2) form row (no identifier)
    claimq("J5x", "0.632·9.0107 > 5.69", d"0.632" * d"9.0107", :gt, d"5.69")
    claimq("J5x", "64·3/320 < 5.69", 64 * big(3) // 320, :lt, d"5.69")
    claimq("J5x", "64·3/(32·16) = 0.375 < 0.632", 64 * big(3) // (32 * 16), :lt, d"0.632")
    claim("J5x", "e^{10.39} < 32533 (< 2^15)", E(d"10.39"), :lt, big(32533) // 1)
    claim("J5x", "e^{3.27} > 26.31 (> 26.22)", E(d"3.27"), :gt, d"26.31")
    claimq("J5x", "8/17805312 < 1/4097", big(8) // 17805312, :lt, big(1) // 4097)
    claim("J5x", "e^9 < 8103.1 (< 8191)", E(9), :lt, d"8103.1")
end

function J6()
    println("\n== J6: g_c^4 = 1024√3 ==")
    gc2 = 32 * sqrt(sqrt(iv(3)))            # g_c^2 = 32·3^{1/4}
    claim("J6", "4/g_c^2 > 0.09497 (g_c^4 = 1024√3)", 4 / gc2, :gt, d"0.09497")
    claimq("J6", "rational form: (4/0.09497)^4 > 1024^2·3", (4 / d"0.09497")^4, :gt, 1024^2 * big(3) // 1)
    println("      g_c^2 κ/8 > 5.26: κ is not defined in the paper (row without consumer); not checked")
end

function J7()
    println("\n== J7: two-dimensional SU(2) constants ==")
    Θlo(x) = 1 + exp(-3 * iv(x) / 8)
    Θhi(x) = 1 + exp(-3 * iv(x) / 8) + exp(-iv(x)) / (1 - exp(-iv(x) / 2))
    ψlo(x) = 2 * log(Θlo(x)) - log(Θhi(2x))
    ψhi(x) = 2 * log(Θhi(x)) - log(Θlo(2x))
    claim("J7", "ψ_cont(23.872) > 2.5892e-4", ψlo(d"23.872"), :gt, d"2.5892e-4")
    claimq("J7", "2.5892e-4 > 1/3864 > 2.5873e-4", d"2.5892e-4", :gt, big(1) // 3864)
    claimq("J7", "1/3864 > 2.5873e-4", big(1) // 3864, :gt, d"2.5873e-4")
    claim("J7", "ψ_cont(23.874) < 2.5873e-4", ψhi(d"23.874"), :lt, d"2.5873e-4")
    # sharper bracket of κ_c from the full theta series (tail bounded geometrically)
    function Θfull(x)
        s = iv(0)
        for n in 1:6
            s = s + exp(-iv(n^2 - 1) * iv(x) / 8)
        end
        # tail n ≥ 7: (n^2-1)/8 ≥ 6 + (n-7) for n ≥ 7
        s + Iv(BigFloat(0), (exp(-6 * iv(x)) / (1 - exp(-iv(x)))).hi)
    end
    ψf(x) = 2 * log(Θfull(x)) - log(Θfull(2x))
    lo, hi = d"23.872", d"23.874"
    for _ in 1:40
        m = (lo + hi) / 2
        v = ψf(m) - big(1) // 3864
        if v.lo > 0; lo = m elseif v.hi < 0; hi = m else break end
    end
    println("      κ_c ∈ [$(Float64(lo/2)), $(Float64(hi/2))] (full theta series)")
    claimq("J7", "√(3κ_c/8) > 2.1156 via 3·11.936/8 > 2.1156^2", 3 * d"11.936" / 8, :gt, d"2.1156"^2)
    claimq("J7", "√(3κ_c/8) < 2.1158 via 3·11.937/8 < 2.1158^2", 3 * d"11.937" / 8, :lt, d"2.1158"^2)
    claim("J7", "e^9 > 7729", E(9), :gt, big(7729) // 1)
    claim("J7", "log 7729 < 8.953", L(7729), :lt, d"8.953")
    claim("J7", "log 7700 > 8.948", L(7700), :gt, d"8.948")
    claimq("J7", "2/7700 - 2/7700^2 > 1/3864", big(2) // 7700 - big(2) // 7700^2, :gt, big(1) // 3864)
    claimq("J7", "15398·3864 = 59497872 > 7700^2", 15398 * big(3864) // 1, :gt, 7700^big(2) // 1)
    claimq("J7", "(4/3)·8.953 < 11.9374", (big(4) // 3) * d"8.953", :lt, d"11.9374")
    claimq("J7", "(4/3)·8.948 > 11.9306", (big(4) // 3) * d"8.948", :gt, d"11.9306")
    claimq("J7", "2T_0/(161·48 T_0) = 1/3864", big(2) // (161 * 48), :ge, big(1) // 3864)
    for (d, θinv, target, dl) in ((4, 2225664, d"15.3087", d"30.6"), (3, 92736, d"12.1306", d"24.2"),
                                  (2, 3864, d"8.9522", d"17.9"))
        θ = big(1) // θinv
        claimq("J7", "θ_$d = 1/(161·24^$(d-1)) = 1/$θinv", big(1) // (161 * 24^(d - 1)), :ge, θ)
        q = (θ + θ^2) / (2 - θ - θ^2)
        claim("J7", "d=$d: log(1/q) ≥ $(Float64(target)) for q = (θ+θ²)/(2-θ-θ²)", -log(iv(q)), :ge, target)
        claim("J7", "d=$d: δℓ = 2 log(1/q) ≥ $(Float64(dl))", -2 * log(iv(q)), :ge, dl)
    end
    claim("J7", "(13/8)·17805312·e^{-π√3} ≥ 125381", (big(13) // 8) * 17805312 * exp(-PI * sqrt(iv(3))), :ge, big(125381) // 1)
    claim("J7", "370944·e^{-π√2} ≥ 4363", 370944 * exp(-PI * sqrt(iv(2))), :ge, big(4363) // 1)
    claimq("J7", "370944 = 161·48^2", 161 * 48^big(2) // 1, :ge, big(370944) // 1)
end

κfun(z) = max(12 + 4z + 2z^2, 6 + 12z)

function J8()
    println("\n== J8: strong coupling and the certified triples ==")
    a = atanh(iv(big(1) // 18))
    claim("J8", "artanh(1/18) > 0.0556128", a, :gt, d"0.0556128")
    claim("J8", "artanh(1/18) < 0.0556129", a, :lt, d"0.0556129")
    K = 96 * 161 * 48^3
    general = [(big(1) // 1000, big(15) // 1, 12, d"0.5220"), (big(1) // 100, big(5) // 1, 20, d"0.8200"),
               (big(1) // 50, big(3) // 1, 32, d"0.8399"), (big(1) // 25, big(3) // 2, 100, d"0.9595"),
               (big(1) // 20, big(7) // 6, 316, d"0.9992"), (big(11) // 200, big(203) // 200, 3914, d"0.9989")]
    su2 = [(big(1) // 10, big(27) // 10, 40, d"0.96"), (big(3) // 20, big(5) // 3, 82, d"0.975"),
           (big(1) // 5, big(23) // 20, 342, d"0.99"), (big(11) // 50, big(203) // 200, 4188, d"0.9999")]
    datum(T, z, Lv) = (1 + big(2) // T)^2 <= z && (T + 1)^4 <= Lv * z^T
    for (G, rows) in (("any G", general), ("SU(2)", su2))
        for (β, z, Ts, θtab) in rows
            if G == "any G"
                θiv = tanh(iv(β)) * κfun(z)
                claim("J8", "$G β=$β z=$z: θ = tanh(β)κ(z) ≤ $(Float64(θtab)) (table)", θiv, :le, θtab)
                # shortest decimal upper bound of θ with which the datum holds at T_*
                θup = θtab
                for nd in 3:40
                    c = short_up(θiv.hi, nd)
                    if datum(Ts, z, (1 - c) / (K * β * z))
                        θup = c; break
                    end
                end
                claim("J8", "$G β=$β z=$z: θ ≤ $(Float64(θup)) (bound used for the datum at T_*)", θiv, :le, θup)
                datum(Ts, z, (1 - θtab) / (K * β * z)) ||
                    println("      NOTE: the 4-digit table bound θ ≤ $(Float64(θtab)) is too weak to certify T_* = $Ts; θ ≤ $(Float64(θup)) is used (exact θ = $(Float64(mid(θiv))))")
                θdn = short_dn(θiv.lo, 30)
            else
                θ = β * κfun(z) / 4
                claimq("J8", "$G β=$β z=$z: θ = βκ(z)/4 = $(Float64(θtab))", θ, :le, θtab)
                claimq("J8", "$G β=$β z=$z: θ ≥ table value", θ, :ge, θtab)
                θup = θ; θdn = θ
            end
            Lup = (1 - θdn) / (K * β * z)       # largest possible L (for failures)
            Ldn = (1 - θup) / (K * β * z)       # smallest possible L (for the datum)
            okT = iseven(Ts) && Ts >= 4 && datum(Ts, z, Ldn)
            least = all(T -> !datum(T, z, Lup), 4:2:Ts-2)
            check("J8", "$G β=$β z=$z: T_*=$Ts even, (1+2/T_*)^2 ≤ z, (T_*+1)^4 ≤ L z^{T_*}", okT, "θ<1: $(θup < 1)")
            check("J8", "$G β=$β z=$z: T_*=$Ts is the least even integer satisfying both", least)
        end
    end
    # (β, z) = (1/1000, 15): T^4 z^{-2⌊T/2⌋} ≤ L at T = 10, fails at T = 11
    β, z = big(1) // 1000, big(15) // 1
    θiv = tanh(iv(β)) * κfun(z)
    Ldn = (1 - d"0.5220") / (K * β * z)
    Lup = (1 - short_dn(θiv.lo, 30)) / (K * β * z)
    check("J8", "(1/1000, 15): T^4 z^{-2⌊T/2⌋} ≤ L at T = 10", 10^4 * z^(-10) <= Ldn)
    check("J8", "(1/1000, 15): T^4 z^{-2⌊T/2⌋} > L at T = 11", 11^4 * z^(-10) > Lup)
end

function J9()
    println("\n== J9: large-N_c table of T_* ==")
    K0 = 4255469568
    table = Dict((2, big(1) // 480) => 25, (2, big(1) // 192) => 41, (2, big(1) // 96) => 81, (2, big(1) // 64) => 199,
                 (3, big(1) // 480) => 27, (3, big(1) // 192) => 43, (3, big(1) // 96) => 83, (3, big(1) // 64) => 205,
                 (10, big(1) // 480) => 29, (10, big(1) // 192) => 45, (10, big(1) // 96) => 89, (10, big(1) // 64) => 219,
                 (10^6, big(1) // 480) => 47, (10^6, big(1) // 192) => 77, (10^6, big(1) // 96) => 147, (10^6, big(1) // 64) => 351)
    for N in (2, 3, 10, 10^6), β in (big(1) // 480, big(1) // 192, big(1) // 96, big(1) // 64)
        α = 36β / (1 - 12β)
        lastfail = 4
        for T in 5:5999
            h = (T - 3) ÷ 2
            if !(K0 * big(N)^2 * β * big(T)^4 * α^h <= h + 1)
                lastfail = T
            end
        end
        Ts = lastfail + 1
        ℓ = -log(iv(α))
        formula = 8 + 4 / ℓ * max(iv(0), log(iv(4 * K0 * big(N)^2 * β)) + 3 * log(12 / (exp(iv(1)) * ℓ)))
        check("J9", "N_c=$N β=$β: least T_* = $(table[(N, β)]) (exact, 5 ≤ T < 6000)", Ts == table[(N, β)],
            "computed $Ts; formula T_*(β,N_c) ≤ $(round(Float64(formula.hi), digits=2)) < 601: $(formula.hi < 601)")
    end
end

function J10()
    println("\n== J10: flux constants (X4) ==")
    claim("J10", "e^{10.80} < 49020.81", E(d"10.80"), :lt, d"49020.81")
    claim("J10", "e^{10.81} > 49513.4", E(d"10.81"), :gt, d"49513.4")
    claimq("J10", "49020.81 < 49155 < 49513.4", d"49020.81", :lt, big(49155) // 1)
    claimq("J10", "49155 < 49513.4", big(49155) // 1, :lt, d"49513.4")
    claim("J10", "(1/2) log 49155 > 5.40", L(49155) / 2, :gt, d"5.40")
    claim("J10", "(1/2) log 49155 < 5.41", L(49155) / 2, :lt, d"5.41")
    w = 2 / sqrt(sqrt(iv(49155)))
    claim("J10", "2·49155^{-1/4} > 0.1342", w, :gt, d"0.1342")
    claim("J10", "2·49155^{-1/4} < 0.1344", w, :lt, d"0.1344")
    claimq("J10", "(2/0.1344)^4 < 49037", (2 / d"0.1344")^4, :lt, big(49037) // 1)
    claimq("J10", "(2/0.1342)^4 > 49329", (2 / d"0.1342")^4, :gt, big(49329) // 1)
    claimq("J10", "2/49153 < 4.07e-5", big(2) // 49153, :lt, d"4.07e-5")
    claimq("J10", "3/49152 = 1/16384", big(3) // 49152, :ge, big(1) // 16384)
    t = big(2) // 49155
    claim("J10", "1 - t ≥ e^{-t/(1-t)} at t = 2/49155 (difference ≥ 0)", (1 - iv(t)) - exp(-iv(t / (1 - t))), :ge, big(0) // 1)
    claimq("J10", "49155/8192 > 6.00036", big(49155) // 8192, :gt, d"6.00036")
    claimq("J10", "49155/8192 < 6.00037", big(49155) // 8192, :lt, d"6.00037")
end

function J11()
    println("\n== J11: universal steps and the one-directionality witness (X3) ==")
    claim("J11", "216 log(9/8) > 25.43", 216 * L(big(9) // 8), :gt, d"25.43")
    claim("J11", "216 log(9/8) < 25.46", 216 * L(big(9) // 8), :lt, d"25.46")
    function Λ(q)
        y = expm1(iv(q) / 216)
        y.hi < 1 || error("m(y) = 1 branch only")
        1728 * log1p(y^2)
    end
    claim("J11", "Λ(24) < 23.71", Λ(24), :lt, d"23.71")
    claim("J11", "Λ(26) > 28", Λ(26), :gt, big(28) // 1)
    claim("J11", "e^{14.38} < 1.7586e6", E(d"14.38"), :lt, d"1.7586e6")
    claimq("J11", "1.7586e6 < 1769471", d"1.7586e6", :lt, big(1769471) // 1)
    claim("J11", "e^{1/1769472} - 1 ≤ 1/1769471", expm1(iv(big(1) // 1769472)), :le, big(1) // 1769471)
    claim("J11", "(e^{1/8192} - 1) e^{9.0108} < 1", expm1(iv(big(1) // 8192)) * E(d"9.0108"), :lt, big(1) // 1)
    ρ = big(1) // 1769473
    claim("J11", "216 log(1+ρ) < 1/8192, ρ = 1/1769473", 216 * log1p(iv(ρ)), :lt, big(1) // 8192)
    claim("J11", "432 log(1+ρ) - 216 log(1+ρ²) > 1/4097", 432 * log1p(iv(ρ)) - 216 * log1p(iv(ρ^2)), :gt, big(1) // 4097)
end

function J12()
    println("\n== J12: double check of L4 and the comparisons of 8.9 ==")
    s = 16 * expm1(iv(big(1) // 8192))^2 + 8 * expm1(iv(big(16) // 8192))^2 + 4 * expm1(iv(big(32) // 8192))^2 +
        2 * expm1(iv(big(64) // 8192))^2
    claim("J12", "Σ 2^{k}(e^{2^{4-k}·.../8192}-1)^2 (the L4 sum with exponentials) < 2.1640e-4", s, :lt, d"2.1640e-4")
    claim("J12", "same sum < 2.17e-4", s, :lt, d"2.17e-4")
    for k in (1, 16, 32, 64)
        claim("J12", "e^{$k/8192} - 1 ≤ $k/(8192-$k)", expm1(iv(k // 8192)), :le, k // (8192 - k))
    end
    claimq("J12", "1/(161·13824) < 2/81", big(1) // (161 * 13824), :lt, big(2) // 81)
    claim("J12", "2/81 < 24 e^{-π}", 24 * exp(-PI), :gt, big(2) // 81)
end

function Jextra()
    println("\n== Unlabelled rows of the certificate table (checked for completeness) ==")
    claim("A", "e^{6.4} < 601.85", E(d"6.4"), :lt, d"601.85")
    claim("A", "e^{8.71} > 6063", E(d"8.71"), :gt, big(6063) // 1)
    claimq("A", "10·600.85 = 6008.5 < 6063", 10 * d"600.85", :lt, big(6063) // 1)
    claim("A", "2/√8192 + 1/8192 < 0.0223", 2 / sqrt(iv(8192)) + big(1) // 8192, :lt, d"0.0223")
    claimq("A", "1/2048 < 4.8829e-4 < 4.9186e-4 < (0.0223 - 1/8192)^2", big(1) // 2048, :lt, d"4.8829e-4")
    claimq("A", "4.9186e-4 < (0.0223 - 1/8192)^2", d"4.9186e-4", :lt, (d"0.0223" - big(1) // 8192)^2)
    # η_0 and u (row of cor:certified-triples)
    xp = d"0.00311048"
    t = 1 - exp(-iv(xp))
    claim("A", "(1 - 2t + 2t^2) e^{1/161} < 1 - 7e-8 at x_+ = 0.00311048", (1 - 2t + 2 * t^2) * E(big(1) // 161), :lt, 1 - d"7e-8")
    claimq("A", "η_0 < (128/27)·0.00311048 < 0.014746", (big(128) // 27) * xp, :lt, d"0.014746")
    claim("A", "e^{0.014746} - 1 < 0.01485526", expm1(iv(d"0.014746")), :lt, d"0.01485526")
    claimq("A", "u < 32·0.01485526^2/0.014746 < 0.478891", 32 * d"0.01485526"^2 / d"0.014746", :lt, d"0.478891")
    claimq("A", "(4095·32)^{-2} < 5.9e-11", big(1) // (4095 * 32)^2, :lt, d"5.9e-11")
    # large-N row
    claim("A", "48π√(5/2) < 239", 48 * PI * sqrt(iv(big(5) // 2)), :lt, big(239) // 1)
    claim("A", "4π√(5/2) < 19.87", 4 * PI * sqrt(iv(big(5) // 2)), :lt, d"19.87")
    # heat-kernel U(1) row
    claim("A", "8 e^{-π} - 0.3072 > 0.0385", 8 * exp(-PI) - d"0.3072", :gt, d"0.0385")
    claimq("A", "8/23.1408 > 0.345709", 8 / d"23.1408", :gt, d"0.345709")
    claim("A", "π^2/(32 log 15) < 0.114", PI^2 / (32 * L(15)), :lt, d"0.114")
    claim("A", "e^{2.708} < 14.9993", E(d"2.708"), :lt, d"14.9993")
    claimq("A", "0.3072 = 192·0.2^4", 192 * d"0.2"^4, :ge, d"0.3072")
    claimq("A", "0.0385 > 1/4097 > 8/(161·48^3)", d"0.0385", :gt, big(1) // 4097)
    claimq("A", "16/(40·96^3) < 4.6e-7", big(16) // (40 * 96^3), :lt, d"4.6e-7")
    claimq("A", "8/17805312 < 4.5e-7", big(8) // 17805312, :lt, d"4.5e-7")
    # no-convexity row
    claim("A", "(π/2)(16 + 0.72 log 4) < 26.71", PI / 2 * (16 + d"0.72" * L(4)), :lt, d"26.71")
    claim("A", "(π/2)·1.44 < 2.27", PI / 2 * d"1.44", :lt, d"2.27")
    claim("A", "(2π - 0.2)^2/8 ≥ 4.61", (2 * PI - d"0.2")^2 / 8, :ge, d"4.61")
    claimq("A", "1.93499/(1 + 0.0238) ≥ 1.89", d"1.93499" / (1 + d"0.0238"), :ge, d"1.89")
    claim("A", "21·0.1·e^{-46} < 1e-19", 21 * d"0.1" * E(-46), :lt, d"1e-19")
    # Bakry–Émery rows
    claimq("A", "135^2·3 = 54675 < 240^2 (135√3/8 < 30)", 135^2 * big(3) // 1, :lt, 240^big(2) // 1)
    claimq("A", "432 < 441 (12√3 < 21)", big(432) // 1, :lt, big(441) // 1)
    claim("A", "9 + √17 > 38/3", 9 + sqrt(iv(17)), :gt, big(38) // 3)
    claimq("A", "14.5/13.9723 < 1.0378", d"14.5" / d"13.9723", :lt, d"1.0378")
    claimq("A", "14.5/13.9471 < 1.0397", d"14.5" / d"13.9471", :lt, d"1.0397")
    claimq("A", "1728·525483/16378696 < 55.45", 1728 * big(525483) // 16378696, :lt, d"55.45")
    claimq("A", "1728·543521/16161106 < 58.12", 1728 * big(543521) // 16161106, :lt, d"58.12")
    # finite-rank and trivialising-map rows
    claimq("A", "12·3·161·144^3 = 17306763264", 12 * 3 * 161 * big(144)^big(3) // 1, :ge, big(17306763264) // 1)
    claimq("A", "1/(72·161·144^3) < 2.8891e-11", big(1) // (72 * 161 * big(144)^3), :lt, d"2.8891e-11")
    e8(c) = 12 * (log(iv(c)) + d"5.42") / iv(c)
    claim("A", "ε_8(18085) < 1/99", e8(18085), :lt, big(1) // 99)
    claim("A", "ε_8(18084) > 1/99", e8(18084), :gt, big(1) // 99)
    claim("A", "window failure: log 4 < 2", L(4), :lt, big(2) // 1)
end

function run_jchecks()
    J1(); J2(); J3(); J4(); J5(); J6(); J7(); J8(); J9(); J10(); J11(); J12(); Jextra()
end
