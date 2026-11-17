import Mathlib
import YangMills.OneCube.Transcendental

/-!
# L19: constants of the step-scaling deduction and of the `ℤ/2` lemma

Section 5 of "The Yang–Mills Mass Gap Reduces to One Cube at Weak Coupling":
the choice of the odd integer in Proposition 5.9, the seed and target sizes, the
asymptotic-freedom slope for `SU(2)`, and the constants of Lemma 5.7
(`Γ ≤ 2.3·10⁻¹⁵` at `β' = 4`, `T = 3`, and `log 8 - 7Γ > 2.07`).
None of these statements proves the one-cube bound or the mass gap.
-/

namespace YangMills.OneCube.StepScaling

open Real

/-- Proposition 5.9, choice of `q`: if `x(1 - r) ≥ 4` and `q ≥ x - 2`, then `q ≥ x r + 2`. -/
theorem odd_choice {x r q : ℝ} (hx : 4 ≤ x * (1 - r)) (hq : x - 2 ≤ q) : x * r + 2 ≤ q := by
  nlinarith

/-- Proposition 5.9: the chosen `q` is at least `3` as soon as `x r + 2 > 2` and `q` is an odd integer. -/
theorem q_ge_three {q : ℕ} (hodd : Odd q) (h : 2 < (q : ℝ)) : 3 ≤ q := by
  have : 2 < q := by exact_mod_cast h
  obtain ⟨k, rfl⟩ := hodd; omega

/-- The coupling window: `β₁ ≤ β_N - κ log q ≤ β₁ + δ` when `x e^{-δ/κ} ≤ q ≤ x`,
written for the logarithms. -/
theorem window {β β₁ κ δ lq lx : ℝ} (hκ : 0 < κ) (hlx : lx = (β - β₁) / κ)
    (hlo : lx - δ / κ ≤ lq) (hhi : lq ≤ lx) :
    β₁ ≤ β - κ * lq ∧ β - κ * lq ≤ β₁ + δ := by
  have h1 : κ * lx = β - β₁ := by rw [hlx]; field_simp
  constructor
  · nlinarith
  · have : κ * (lx - δ / κ) = β - β₁ - δ := by rw [mul_sub, h1]; field_simp
    nlinarith

/-- Seed tolerance below the datum tolerance, and the size of the transported cube. -/
theorem seed_tolerance : (1 : ℚ) / 2225664 < 1 / 4097 := by norm_num

theorem transported_side {q : ℕ} (h : 3 ≤ q) : 1026 ≤ 342 * q ∧ 948 ≤ 316 * q := by omega

/-- The `SU(2)` asymptotic-freedom slope `11/(3π²)` lies in `(0.37151, 0.371531)`. -/
theorem kappaAF_su2 : 0.37151 < 11 / (3 * π ^ 2) ∧ 11 / (3 * π ^ 2) < 0.371531 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  have hp : 0 < π ^ 2 := by positivity
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- `e⁸ ≥ 2978`. -/
theorem exp8 : (2978 : ℝ) ≤ exp 8 :=
  (by norm_num : (2978 : ℝ) ≤ (2.718 : ℝ) ^ 8).trans (exp_dn 8 (2.718 : ℝ))

/-- Lemma 5.7 at `β' = 4`, `T = 3`: with `q = 400 e^{-8}`,
`48 T⁴ e^{-2β'} q^{2T²-1}/(1-q) ≤ 2.3·10⁻¹⁵`. -/
theorem gamma_bound :
    48 * 3 ^ 4 * exp (-8) * (400 * exp (-8)) ^ (2 * 3 ^ 2 - 1) / (1 - 400 * exp (-8))
      ≤ (23 : ℝ) / 10 ^ 16 := by
  have hE0 : 0 < exp (-8 : ℝ) := exp_pos _
  have hE : exp (-8 : ℝ) ≤ 1 / 2978 := by
    rw [exp_neg, inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) exp8
  have hq : 400 * exp (-8 : ℝ) ≤ 400 / 2978 := by linarith
  have hden : (0 : ℝ) < 1 - 400 / 2978 := by norm_num
  calc 48 * 3 ^ 4 * exp (-8) * (400 * exp (-8)) ^ (2 * 3 ^ 2 - 1) / (1 - 400 * exp (-8))
      ≤ 48 * 3 ^ 4 * (1 / 2978) * (400 / 2978) ^ (2 * 3 ^ 2 - 1) / (1 - 400 / 2978) := by
        gcongr
    _ ≤ 23 / 10 ^ 16 := by norm_num

/-- Lemma 5.7: `log 8 - log(1 + 7Γ) ≥ log 8 - 7Γ > 2.07` for `0 ≤ Γ ≤ 2.3·10⁻¹⁵`. -/
theorem z2_target {Γ : ℝ} (h0 : 0 ≤ Γ) (h : Γ ≤ 23 / 10 ^ 16) :
    2.07 < log 8 - log (1 + 7 * Γ) := by
  have hl : log (1 + 7 * Γ) ≤ 7 * Γ := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + 7 * Γ); linarith
  have h8 : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have := (Transcendental.log_two_bounds).1
  rw [h8]; linarith

end YangMills.OneCube.StepScaling
