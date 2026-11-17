# Run all one-cube checks: the rigorous enclosures J1–J20 (and the unlabelled
# certificate rows), export the rational enclosures to Lean, then run the
# numerical sanity checks (floating point, not proofs).
#   julia julia/onecube/run_all.jl            (all)
#   julia julia/onecube/run_all.jl --no-sanity

include(joinpath(@__DIR__, "intervals.jl"))
include(joinpath(@__DIR__, "framework.jl"))
include(joinpath(@__DIR__, "jchecks.jl"))
include(joinpath(@__DIR__, "jchecks2.jl"))

println("One-cube checks. Julia ", VERSION, ", BigFloat precision ", precision(BigFloat), " bits")
println("None of these checks proves the continuum limit, the one-cube bound or the mass gap.")
run_jchecks()
J13(); J14(); J15(); J16(); J17(); J18(); J19(); J20()
lean_path = normpath(joinpath(@__DIR__, "..", "..", "YangMills", "OneCube", "Enclosures.lean"))
write_lean(lean_path)
npass = count(r -> r.pass, RESULTS); nfail = length(RESULTS) - npass
println("\nRigorous checks: $npass PASS, $nfail FAIL")
for r in RESULTS
    r.pass || println("  FAIL  ", r.id, "  ", r.label)
end
println("Exported $(count(startswith("theorem"), LEANLINES)) rational inequalities to YangMills/OneCube/Enclosures.lean")

if !("--no-sanity" in ARGS)
    include(joinpath(@__DIR__, "sanity.jl"))
    run_sanity()
end
