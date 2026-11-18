# Run all one-cube checks: the rigorous enclosures J1–J12 (and the unlabelled
# certificate rows), export the rational enclosures to Lean, then run the
# numerical sanity checks (floating point, not proofs).
#   julia julia/onecube/run_all.jl            (all)
#   julia julia/onecube/run_all.jl --no-sanity

include(joinpath(@__DIR__, "intervals.jl"))
include(joinpath(@__DIR__, "test_intervals.jl"))
include(joinpath(@__DIR__, "framework.jl"))
include(joinpath(@__DIR__, "jchecks.jl"))

println("One-cube checks. Julia ", VERSION, ", BigFloat precision ", precision(BigFloat), " bits")
println("None of these checks proves the continuum limit, the one-cube bound or the mass gap.")
run_jchecks()
lean_path = normpath(joinpath(@__DIR__, "..", "..", "YangMills", "OneCube", "Enclosures.lean"))
npass = count(r -> r.pass, RESULTS); nfail = length(RESULTS) - npass
println("\nRigorous checks: $npass PASS, $nfail FAIL")
for r in RESULTS
    r.pass || println("  FAIL  ", r.id, "  ", r.label)
end
if nfail != 0
    error("$nfail rigorous check(s) failed; Lean enclosure export was not written")
end
write_lean(lean_path)
println("Exported $(count(startswith("theorem"), LEANLINES)) rational inequalities to YangMills/OneCube/Enclosures.lean")

if !("--no-sanity" in ARGS)
    include(joinpath(@__DIR__, "sanity.jl"))
    run_sanity()
end
