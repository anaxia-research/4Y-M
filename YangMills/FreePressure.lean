import Mathlib

/-!
# The free pressure on one box (Proposition `ly:prop:freepressure`)

For the free gluons on the spatial cube of side `2T` with time extent `T`,
the twelve lowest real modes per colour have lattice energy
`ω = 2 arsinh (sin (π/(2T))) ≤ π/T`, so `T ω ≤ π`. Each such mode contributes
`-log (1 - e^{-Tω})` to the pressure, and the 78 colour-invariant two-mode
states contribute `log (1 + 78 e^{-2π})` on the invariant subspace.

* `omega_le`: `2 arsinh (sin (π/(2T))) ≤ π/T`.
* `gap_le`: if `E₁ ≤ ω` then `2T E₁ ≤ 2π`.
* `mode_ge`: `e^{-π} ≤ -log (1 - e^{-t})` for `0 < t ≤ π`.
* `free_pressure_ge`: 36 such modes give `X ≥ 36 e^{-π}`.
* `free_pressure_gt`: hence `X > 1/2`.
* `singlet_pressure_gt`: `log (1 + 78 e^{-s}) ≤ X` with `s ≤ 2π` gives `X > 1/50`.
* `free_violates`, `singlet_violates`: both exceed `x_* = 3.4865·10⁻⁵`.

The numerical constants here are weaker than those printed in the paper
(`1.590` and `0.1359`) but already exceed `x_*` by factors above `10⁴` and
`500`.
-/

open Real

namespace YangMills.FreePressure

/-- The lowest mode energy: `2 arsinh (sin (π/(2T))) ≤ π/T` for `T > 0`. -/
theorem omega_le (T : ℝ) (hT : 0 < T) :
    2 * Real.arsinh (Real.sin (π / (2 * T))) ≤ π / T := by
  have hy : 0 ≤ π / (2 * T) := by positivity
  have hs : Real.sin (π / (2 * T)) ≤ π / (2 * T) := Real.sin_le hy
  have ha : Real.arsinh (Real.sin (π / (2 * T))) ≤ π / (2 * T) := by
    have h1 : Real.arsinh (Real.sin (π / (2 * T))) ≤ Real.arsinh (π / (2 * T)) :=
      Real.arsinh_le_arsinh.mpr hs
    have h2 : Real.arsinh (π / (2 * T)) ≤ π / (2 * T) := by
      rw [← Real.sinh_le_sinh, Real.sinh_arsinh]
      exact Real.self_le_sinh_iff.mpr hy
    linarith
  have : π / (2 * T) * 2 = π / T := by field_simp
  linarith

/-- The first excitation energy of the free box: `E₁ ≤ ω ≤ π/T` gives
`2T E₁ ≤ 2π`. -/
theorem gap_le (T E₁ : ℝ) (hT : 0 < T)
    (hE : E₁ ≤ 2 * Real.arsinh (Real.sin (π / (2 * T)))) : 2 * T * E₁ ≤ 2 * π := by
  have h := (hE.trans (omega_le T hT))
  have : 2 * T * (π / T) = 2 * π := by field_simp
  nlinarith

/-- One low mode: `e^{-π} ≤ -log (1 - e^{-t})` for `0 < t ≤ π`. -/
theorem mode_ge (t : ℝ) (ht : 0 < t) (htπ : t ≤ π) :
    Real.exp (-π) ≤ -Real.log (1 - Real.exp (-t)) := by
  have hu : Real.exp (-t) < 1 := by
    have := Real.exp_lt_exp.mpr (show -t < 0 by linarith)
    rwa [Real.exp_zero] at this
  have hpos : 0 < 1 - Real.exp (-t) := by linarith
  have hlog : Real.log (1 - Real.exp (-t)) ≤ (1 - Real.exp (-t)) - 1 :=
    Real.log_le_sub_one_of_pos hpos
  have hmono : Real.exp (-π) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- `e^π < e^4 < 55`. -/
theorem exp_pi_lt : Real.exp π < 55 := by
  have h1 : Real.exp π < Real.exp 4 := Real.exp_lt_exp.mpr (by linarith [Real.pi_lt_four])
  have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h4 : 0 < Real.exp 1 := Real.exp_pos 1
  have h5 : Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := by
    gcongr
  have : (2.7182818286 : ℝ) ^ 4 < 55 := by norm_num
  linarith

/-- `e^{-π} > 1/55`. -/
theorem exp_neg_pi_gt : (1 : ℝ) / 55 < Real.exp (-π) := by
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (Real.exp_pos π) exp_pi_lt

/-- **The free pressure.** If the pressure is at least the sum of the
contributions of 36 modes with `0 < t_i ≤ π`, it is at least `36 e^{-π}`. -/
theorem free_pressure_ge (X : ℝ) (t : Fin 36 → ℝ) (ht : ∀ i, 0 < t i)
    (htπ : ∀ i, t i ≤ π)
    (hX : ∑ i, -Real.log (1 - Real.exp (-t i)) ≤ X) : 36 * Real.exp (-π) ≤ X := by
  have : ∑ _i : Fin 36, Real.exp (-π) ≤ ∑ i, -Real.log (1 - Real.exp (-t i)) :=
    Finset.sum_le_sum fun i _ => mode_ge (t i) (ht i) (htπ i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  linarith

/-- The free pressure exceeds `1/2`. -/
theorem free_pressure_gt (X : ℝ) (t : Fin 36 → ℝ) (ht : ∀ i, 0 < t i)
    (htπ : ∀ i, t i ≤ π)
    (hX : ∑ i, -Real.log (1 - Real.exp (-t i)) ≤ X) : 1 / 2 < X := by
  have := free_pressure_ge X t ht htπ hX
  have := exp_neg_pi_gt
  linarith

/-- **The colour-invariant pressure.** `log (1 + 78 e^{-s}) ≤ X` with
`s ≤ 2π` gives `X > 1/50`. -/
theorem singlet_pressure_gt (X s : ℝ) (hs : s ≤ 2 * π)
    (hX : Real.log (1 + 78 * Real.exp (-s)) ≤ X) : 1 / 50 < X := by
  have he : Real.exp (-(2 * π)) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(2 * π)) = Real.exp (-π) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hp := exp_neg_pi_gt
  have hsq : (1 / 55 : ℝ) ^ 2 < Real.exp (-π) ^ 2 := by gcongr
  set u := 78 * Real.exp (-s) with hu
  have hu1 : 78 / 3025 < u := by
    rw [hu]; nlinarith
  have hupos : 0 < u := by linarith
  -- log (1 + u) ≥ u / (1 + u)
  have hlog : u / (1 + u) ≤ Real.log (1 + u) := by
    have h1 : 0 < 1 + u := by linarith
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
    rw [Real.log_inv] at this
    have hi : (1 + u)⁻¹ - 1 = -(u / (1 + u)) := by field_simp; ring
    linarith
  have hmono : (78 / 3025 : ℝ) / (1 + 78 / 3025) < u / (1 + u) := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have : (1 / 50 : ℝ) < (78 / 3025 : ℝ) / (1 + 78 / 3025) := by norm_num
  linarith

/-- `x_* ≤ 3.4865·10⁻⁵`, the threshold of `(P)`. -/
noncomputable def xstar : ℝ := 3.4865e-5

/-- The free gluons violate `(P)` on every box. -/
theorem free_violates (X : ℝ) (t : Fin 36 → ℝ) (ht : ∀ i, 0 < t i)
    (htπ : ∀ i, t i ≤ π)
    (hX : ∑ i, -Real.log (1 - Real.exp (-t i)) ≤ X) : 10000 * xstar < X := by
  have := free_pressure_gt X t ht htπ hX
  unfold xstar; norm_num at this ⊢; linarith

/-- The colour-invariant free states violate `(P)` on every box. -/
theorem singlet_violates (X s : ℝ) (hs : s ≤ 2 * π)
    (hX : Real.log (1 + 78 * Real.exp (-s)) ≤ X) : 500 * xstar < X := by
  have := singlet_pressure_gt X s hs hX
  unfold xstar; norm_num at this ⊢; linarith

end YangMills.FreePressure
