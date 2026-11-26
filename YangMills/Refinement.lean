import Mathlib
import YangMills.FreePressure

/-!
# Refinement does not create the gap (Remark `ly:rem:refine`)

The bound `(P)`, `X ≤ x_*`, forces a large first excitation energy on the box,
while the smooth (free-field) limit of the short-distance modes has a small
one. This file checks the three quantitative facts of the remark.

* `trace_log_nonneg`: `log Σ μ_k^T ≥ 0` when the top eigenvalue is `1` and all
  are nonnegative; positivity already holds at every spacing.
* `small_pressure_gap`: if `log (1 + e^{-t}) ≤ X`, then
  `e^{-t} ≤ X (1 + e^{-t})`, so a small pressure forces a small `e^{-t}`.
* `pressure_forces`: under `(P)` with `x_* ≤ 1/28684`, `e^{-t} < 1/28000`.
* `free_short`: the free bound `t ≤ π` (that is `2T E₁ ≤ 2π`, with `t = T E₁`)
  is incompatible with `(P)`.
* `free_gap_short`: the lattice free energy `E₁ ≤ 2 arsinh (sin (π/(2T)))`
  is incompatible with `(P)` on every box.
* `singlet_short`: `4π < 12.57 < 20.5`, the colour-singlet comparison.
-/

open Real

namespace YangMills.Refinement

/-- **Positivity of the log-trace.** If `μ i₀ = 1` and every `μ i ≥ 0`, then
`log (Σ μ_i^T) ≥ 0`. -/
theorem trace_log_nonneg {ι : Type*} (s : Finset ι) (μ : ι → ℝ) (T : ℕ)
    (i₀ : ι) (hi₀ : i₀ ∈ s) (h1 : μ i₀ = 1) (hpos : ∀ i ∈ s, 0 ≤ μ i) :
    0 ≤ Real.log (∑ i ∈ s, μ i ^ T) := by
  apply Real.log_nonneg
  have : μ i₀ ^ T ≤ ∑ i ∈ s, μ i ^ T :=
    Finset.single_le_sum (f := fun i => μ i ^ T)
      (fun i hi => pow_nonneg (hpos i hi) T) hi₀
  rw [h1, one_pow] at this
  exact this

/-- **A small pressure forces a small Boltzmann factor.** If
`log (1 + e^{-t}) ≤ X`, then `e^{-t} ≤ X (1 + e^{-t})`. -/
theorem small_pressure_gap (t X : ℝ) (h : Real.log (1 + Real.exp (-t)) ≤ X) :
    Real.exp (-t) ≤ X * (1 + Real.exp (-t)) := by
  set y := Real.exp (-t) with hy
  have hypos : 0 < y := Real.exp_pos _
  have h1 : 0 < 1 + y := by linarith
  -- `log (1 + y) ≥ y / (1 + y)`
  have hl : y / (1 + y) ≤ Real.log (1 + y) := by
    have := Real.one_sub_inv_le_log_of_pos h1
    have e : 1 - (1 + y)⁻¹ = y / (1 + y) := by field_simp; ring
    linarith
  have h2 : y / (1 + y) ≤ X := hl.trans h
  rw [div_le_iff₀ h1] at h2
  linarith

/-- **Under `(P)` the Boltzmann factor is tiny.** If `log (1 + e^{-t}) ≤ X` and
`X ≤ 1/28684`, then `e^{-t} < 1/28000`. -/
theorem pressure_forces (t X : ℝ) (h : Real.log (1 + Real.exp (-t)) ≤ X)
    (hX : X ≤ 1 / 28684) : Real.exp (-t) < 1 / 28000 := by
  have hk := small_pressure_gap t X h
  set y := Real.exp (-t)
  have hypos : 0 < y := Real.exp_pos _
  have hX0 : 0 ≤ X := by
    have : 0 ≤ Real.log (1 + y) := Real.log_nonneg (by linarith)
    linarith
  -- `y (1 - X) ≤ X`
  have h3 : y * (1 - X) ≤ X := by nlinarith
  have h4 : (1 : ℝ) - X ≥ 28683 / 28684 := by linarith
  have h5 : y * (28683 / 28684) ≤ X := by nlinarith
  have h6 : y ≤ X * (28684 / 28683) := by nlinarith
  have h7 : X * (28684 / 28683) ≤ 1 / 28683 := by
    have := mul_le_mul_of_nonneg_right hX (by norm_num : (0 : ℝ) ≤ 28684 / 28683)
    norm_num at this ⊢; linarith
  have : (1 : ℝ) / 28683 < 1 / 28000 := by norm_num
  linarith

/-- **The free value is too small.** The free bound `t ≤ π` (that is,
`2T E₁ ≤ 2π` with `t = T E₁`) is incompatible with `(P)`:
`(P)` forces `e^{-t} < 1/28000`, while `t ≤ π` gives `e^{-t} > 1/55`. -/
theorem free_short (t X : ℝ) (h : Real.log (1 + Real.exp (-t)) ≤ X)
    (hX : X ≤ 1 / 28684) (ht : t ≤ π) : False := by
  have h1 := pressure_forces t X h hX
  have h2 : Real.exp (-π) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  have h3 := YangMills.FreePressure.exp_neg_pi_gt
  have : (1 : ℝ) / 28000 < 1 / 55 := by norm_num
  linarith

/-- **Free gluons fail `(P)` on every box.** If the first excitation energy is
the free lattice value, `E₁ ≤ 2 arsinh (sin (π/(2T)))`, then the pressure
bound `log (1 + e^{-T E₁}) ≤ X ≤ 1/28684` cannot hold. -/
theorem free_gap_short (T E₁ X : ℝ) (hT : 0 < T)
    (hE : E₁ ≤ 2 * Real.arsinh (Real.sin (π / (2 * T))))
    (h : Real.log (1 + Real.exp (-(T * E₁))) ≤ X) (hX : X ≤ 1 / 28684) : False := by
  have hg := YangMills.FreePressure.gap_le T E₁ hT hE
  have ht : T * E₁ ≤ π := by nlinarith
  exact free_short (T * E₁) X h hX ht

/-- **The colour-singlet comparison.** `4π < 12.57 < 20.5`. -/
theorem singlet_short : 4 * π < 12.57 ∧ (12.57 : ℝ) < 20.5 := by
  have := Real.pi_lt_d4
  refine ⟨?_, by norm_num⟩
  linarith

end YangMills.Refinement
