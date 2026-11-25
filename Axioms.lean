import YangMills
import Lean

/-!
# Axiom audit

`lake env lean Axioms.lean` checks every theorem whose name lies in the
`YangMills` namespace, including private and auxiliary ones. It fails if any of
them depends on an axiom other than `propext`, `Classical.choice` and
`Quot.sound`; this also excludes `sorryAx` and `Lean.ofReduceBool`. It then
prints the axioms of the main results individually.
-/

open Lean Elab Command

/-- Collect every theorem in the `YangMills` namespace and check its axioms. -/
elab "#audit_yang_mills" : command => do
  let env ← getEnv
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc n info =>
    match info with
    | .thmInfo _ => if (`YangMills).isPrefixOf (privateToUserName n) then acc.push n else acc
    | _ => acc
  if names.isEmpty then
    throwError "no theorem in the YangMills namespace"
  let mut bad : Array MessageData := #[]
  for n in names do
    let axs ← collectAxioms n
    let extra := axs.filter (fun a => !standard.contains a)
    unless extra.isEmpty do
      bad := bad.push m!"{n}: {extra}"
  unless bad.isEmpty do
    throwError m!"theorems with non-standard axioms:\n{MessageData.joinSep bad.toList "\n"}"
  logInfo m!"{names.size} theorems in the YangMills namespace checked: each depends at most on propext, Classical.choice and Quot.sound."

#audit_yang_mills

/-! ## Main results -/

#print axioms YangMills.nogo_no_gapped_limit
#print axioms YangMills.limit_ratio_le
#print axioms YangMills.holleyStroock_poincare
#print axioms YangMills.holleyStroock_entropy
#print axioms YangMills.window_entered
#print axioms YangMills.wilsonAction_osc_le
#print axioms YangMills.cube_bianchi
#print axioms YangMills.corrAction_var_per_volume_unbounded
#print axioms YangMills.StrongCoupling.wilson_threshold_d4
#print axioms YangMills.StrongCoupling.gap_d4
#print axioms YangMills.StrongCoupling.zonal_final
#print axioms YangMills.StrongCoupling.GaugeFix.twelve_neighbours
#print axioms YangMills.StrongCoupling.BlockGauge.invisible_classes
#print axioms YangMills.StrongCoupling.StarThreshold.sevenSys_unique
#print axioms YangMills.StrongCoupling.StarThreshold.lam_lt_one_iff_beta
#print axioms YangMills.StrongCoupling.StarThreshold.svalues
#print axioms YangMills.StrongCoupling.StarThreshold.half_of_large
#print axioms YangMills.StrongCoupling.StarThreshold.gap_constant
#print axioms YangMills.StrongCoupling.StarThreshold.uniform_numbers_7_20
#print axioms YangMills.GapFree.ascent_decay
#print axioms YangMills.GapFree.log_gap_constant
#print axioms YangMills.GapFree.fixed_point_bracket
#print axioms YangMills.OneCube.Chebyshev.prod_identity
#print axioms YangMills.OneCube.Fourier.L10
#print axioms YangMills.OneCube.Haar.L12_S
#print axioms YangMills.OneCube.Counting.L13
#print axioms YangMills.CentreTwists.twist_ratio_bounds
#print axioms YangMills.CentreTwists.datum_twist
#print axioms YangMills.CentreTwists.peierls_threshold_2127
#print axioms YangMills.CentreTwists.peierls_threshold_2495
#print axioms YangMills.CentreTwists.twistEater_commutator
#print axioms YangMills.CentreTwists.abelian_slice_cost
#print axioms YangMills.TwoSources.holder_sector
#print axioms YangMills.TwoSources.compensation_sector
#print axioms YangMills.TwoSources.compensation_final
#print axioms YangMills.TwoSources.logconvex_sum
#print axioms YangMills.TwoSources.chi_orth
#print axioms YangMills.TwoSources.fourier_inversion
#print axioms YangMills.TwoSources.flux_small
#print axioms YangMills.TwoSources.flux_zero_large
#print axioms YangMills.TwoSources.twist_of_Ftw
#print axioms YangMills.TwoSources.trace_sandwich
#print axioms YangMills.TwoSources.sheet_expansion
#print axioms YangMills.TwoSources.datum_flux_log
#print axioms YangMills.QuasiLeeYang.cayley_re_neg_iff
#print axioms YangMills.QuasiLeeYang.vieta_norm
#print axioms YangMills.QuasiLeeYang.stack_on_line
#print axioms YangMills.QuasiLeeYang.vortex_pos
#print axioms YangMills.QuasiLeeYang.standing_wave_poly
#print axioms YangMills.QuasiLeeYang.knot_invariance
#print axioms YangMills.QuasiLeeYang.knot_independent
#print axioms YangMills.QuasiLeeYang.area_bound
#print axioms YangMills.QuasiLeeYang.theoremA_tail
#print axioms YangMills.QuasiLeeYang.fluxCrit_values
#print axioms YangMills.QuasiLeeYang.theoremA_domain
#print axioms YangMills.QuasiLeeYang.theoremB
#print axioms YangMills.QuasiLeeYang.theoremB_zstar
#print axioms YangMills.QuasiLeeYang.eps_rKP
#print axioms YangMills.QuasiLeeYang.disc_consistency
#print axioms YangMills.QuasiLeeYang.critical_width
#print axioms YangMills.QuasiLeeYang.KN_threshold
#print axioms YangMills.QuasiLeeYang.coef_tail
#print axioms YangMills.QuasiLeeYang.zstar_implies_HZ
#print axioms YangMills.QuasiLeeYang.halfplane_model
#print axioms YangMills.QuasiLeeYang.stagger_plaquette_odd
#print axioms YangMills.QuasiLeeYang.plus_arith
#print axioms YangMills.QuasiLeeYang.critflux_width
#print axioms YangMills.QuasiLeeYang.strip_cos_lower
#print axioms YangMills.QuasiLeeYang.strip_optimal
#print axioms YangMills.QuasiLeeYang.heat_strip
#print axioms YangMills.QuasiLeeYang.jensen_constant
#print axioms YangMills.Ledger.matched_mem
#print axioms YangMills.Ledger.orbit_chain
#print axioms YangMills.Ledger.ledger_bound
#print axioms YangMills.Ledger.ladder_length
#print axioms YangMills.Ledger.ladder_size
#print axioms YangMills.Ledger.step_scaling_defect
