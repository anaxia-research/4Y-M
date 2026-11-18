# Regression checks of the generic interval arithmetic, using exact rational
# comparisons with the binary floating-point endpoints. No external packages.
using Test

if !isdefined(@__MODULE__, :Iv)
    include(joinpath(@__DIR__, "intervals.jl"))
end

exact_endpoint(x::BigFloat) = Rational{BigInt}(x)
encloses(x::Iv, q::Rational) = exact_endpoint(x.lo) <= q <= exact_endpoint(x.hi)

@testset "Directed rational interval construction" begin
    p = big(2)^300
    q = (p + 1) // (p + 2)
    cases = [q, inv(q), -q, -inv(q), big(0)//1, big(1)//3,
             -big(1)//3, (big(2)^700 + 37)//(big(3)^500 + 19)]
    for value in cases
        @test encloses(iv(value), value)
    end
    @test iv(q).lo < 1
    @test iv(inv(q)).hi > 1
end

@testset "Interval arithmetic with rounded rational inputs" begin
    p = big(2)^300
    cases = [(p + 1)//(p + 2), (p + 2)//(p + 1),
             -(p + 1)//(p + 2), -(p + 2)//(p + 1)]
    for a in cases, b in cases
        @test encloses(iv(a) + iv(b), a + b)
        @test encloses(iv(a) - iv(b), a - b)
        @test encloses(iv(a) * iv(b), a * b)
        @test encloses(iv(a) / iv(b), a / b)
    end
    @test_throws ErrorException inv(Iv(BigFloat(-1), BigFloat(1)))
end
