import Mathlib

/-!
# Averaged sources past the star threshold

Arithmetic of Proposition `prop:avgsource` of the paper (the star condition with the source
of one star averaged over the star law). The analytic inputs (the harmonic-extension bound of
Appendix `app:sharp` and the enclosure `H ≥ e₀` of the zonal gain) are not formalised here.

* `m_closed` : `1 - A_u^2 - 3 A_u/κ = (7 - s)/(1 + s)^2` with `A_u = κ/(1 + s)`, `s^2 = κ^2 + 9`.
* `m_antitone` : `s ↦ (7 - s)/(1 + s)^2` is antitone on `[3, 15]`.
* `m_at_K0` : `s = 3701/1000` dominates `√(K₀^2 + 9)` for `K₀ = 2709/1250 = 6 β₁`, and
  `(7 - s)/(1 + s)^2 ≥ 1492/10000`.
* `avg_threshold` : with `θ₁ = 1 - 4 e₀ (3609/10000)^2 (1492/10000)`, `e₀ = 193/10000`,
  `θ₁ λ(β₁) ≤ 1 - 6/10^5` at `β₁ = 903/2500`, and `λ(3609/10000) ≤ 1 - 6/10^5`.
* `lam_mono` : `λ(β) = 3β(4+β)/(8 - 8β - 3β²)` is monotone on `[0, 2/5]`.
* `avg_gap` : `6/10^5/(1250 e^2) > 6/10^9`.
-/

namespace YangMills.AveragedSource

/-- The star contraction `λ = 6 c s(c)` as a function of `β_W` (Lemma `lem:sclosed`). -/
noncomputable def lam (b : ℝ) : ℝ := 3 * b * (4 + b) / (8 - 8 * b - 3 * b ^ 2)

/-- The lower bound for the zonal variance in terms of `s = √(κ² + 9)`. -/
noncomputable def m (s : ℝ) : ℝ := (7 - s) / (1 + s) ^ 2

theorem m_closed (κ s : ℝ) (hκ : 0 < κ) (hs : 0 < s) (hss : s ^ 2 = κ ^ 2 + 9) :
    1 - (κ / (1 + s)) ^ 2 - 3 * (κ / (1 + s)) / κ = m s := by
  unfold m
  have h1 : (1 + s) ≠ 0 := by intro h; linarith
  field_simp
  nlinarith [hss]

theorem m_antitone (s t : ℝ) (h3 : 3 ≤ s) (hst : s ≤ t) (ht : t ≤ 15) : m t ≤ m s := by
  unfold m
  have hs1 : 0 < (1 + s) ^ 2 := pow_pos (by linarith) 2
  have ht1 : 0 < (1 + t) ^ 2 := pow_pos (by linarith) 2
  rw [div_le_div_iff₀ ht1 hs1]
  have key : (7 - s) * (1 + t) ^ 2 - (7 - t) * (1 + s) ^ 2 = (t - s) * (15 + 7 * s + 7 * t - s * t) := by
    ring
  have hpos : 0 ≤ 15 + 7 * s + 7 * t - s * t := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hst) hpos]

theorem m_at_K0 :
    ((2709 : ℝ) / 1250) ^ 2 + 9 ≤ ((3701 : ℝ) / 1000) ^ 2 ∧
      (1492 : ℝ) / 10000 ≤ m (3701 / 1000) := by
  unfold m; constructor <;> norm_num

theorem avg_threshold :
    let θ₁ : ℝ := 1 - 4 * (193 / 10000) * (3609 / 10000) ^ 2 * (1492 / 10000)
    θ₁ * lam (903 / 2500) ≤ 1 - 6 / 10 ^ 5 ∧ lam (3609 / 10000) ≤ 1 - 6 / 10 ^ 5 ∧
      θ₁ < 1 ∧ 0 < θ₁ := by
  intro θ₁
  simp only [θ₁, lam]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

theorem lam_mono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 / 5) : lam a ≤ lam b := by
  unfold lam
  have hda : 0 < 8 - 8 * a - 3 * a ^ 2 := by nlinarith
  have hdb : 0 < 8 - 8 * b - 3 * b ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hda hdb]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hab), mul_nonneg (mul_nonneg ha ha) (sub_nonneg.mpr hab),
    mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hab)) (sub_nonneg.mpr hab)]

theorem avg_gap : (6 : ℝ) / 10 ^ 9 < 6 / 10 ^ 5 / (1250 * Real.exp 1 ^ 2) := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 := by gcongr
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

end YangMills.AveragedSource
