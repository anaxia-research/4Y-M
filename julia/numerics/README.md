# SU(2) Monte Carlo test of the one-cube bound

Floating-point numerics, not proofs. They estimate log Zcal_{L^3}(T0) at T0 = L/2 for
four-dimensional SU(2) Wilson lattice gauge theory and compare it with 1/8192.

- `su2mc.jl`: heatbath + overrelaxation on L^3 x Lt; per time slice, spatial plaquettes,
  1x2 rectangles and spatial Polyakov loops at APE smearing levels 0, 5, 12, 25.
  `julia -t 4 su2mc.jl beta L Lt ntherm nmeas nskip seed outfile` (the seed is written in the file header).
- `analyse.jl`: GEVP effective energies of the A1++, E++ and torelon channels with jackknife errors,
  then the free-boson Fock-space estimate of log Zcal from these levels (lattice dispersion).
  `julia analyse.jl data/b2.3_L12_T16.dat 20`
- `run_all.sh`: the production runs (resumable). Data files are not stored in the repository.
