import Mathlib

/-!
# The box certificate on the star range

The box certificate `(C)` of the one-box reduction, `X(T_*; b) ≤ x_*` for
`0 ≤ b ≤ β_top`, holds for `T_* = 1012` and `β_top = 1/3`.

* `xstar_lower`: `x_* = log (2/(1 + e^{-η})) ≥ 1/28684` for `η = 1/14341`.
* `starBound`: the explicit bound `𝔅(β, T, q)` of the datum on the star range,
  with the boundary count replaced by `24m³ + 132m² + 240m + 684`, `m = 2R - 1`,
  `R = ⌊(T-3)/2⌋`.
* `starBound_third`: `𝔅(1/3, 1012, 575769/500000) ≤ 1/28684`, exactly.
* `certificate_of_star`: the star bound and the trace bound `X ≤ ψ` give `(C)`.
-/

set_option exponentiation.threshold 2000

namespace YangMills.StarCert

/-- `γ(β) = c(1+c)/(1-4c-6c²)` with `c = β/4`. -/
def gam (b : ℚ) : ℚ := (b / 4) * (1 + b / 4) / (1 - 4 * (b / 4) - 6 * (b / 4) ^ 2)

/-- The boundary count bound with `m = 2R - 1`. -/
def nBd (R : ℕ) : ℚ :=
  24 * (2 * R - 1 : ℚ) ^ 3 + 132 * (2 * R - 1 : ℚ) ^ 2 + 240 * (2 * R - 1 : ℚ) + 684

/-- The bound `𝔅(β, T, q)` of the datum on the star range. -/
def starBound (b : ℚ) (T : ℕ) (q : ℚ) : ℚ :=
  192 * (T : ℚ) ^ 4 * b * (1 + q) * gam b * nBd ((T - 3) / 2) /
    (1 - 6 * gam b * q) / q ^ ((T - 3) / 2)

/-- Clearing denominators in `A/d/(u/v)^R ≤ 1/k`. -/
theorem ratio_le (A d u v k : ℕ) (R : ℕ) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v)
    (hk : 0 < k) (h : A * k * v ^ R ≤ d * u ^ R) :
    (A : ℚ) / d / ((u : ℚ) / v) ^ R ≤ 1 / k := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hu' : (0 : ℚ) < (u : ℚ) ^ R := by positivity
  have hv' : (0 : ℚ) < (v : ℚ) ^ R := by positivity
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  have h' : (A : ℚ) * k * (v : ℚ) ^ R ≤ d * (u : ℚ) ^ R := by exact_mod_cast h
  rw [div_pow, div_div,
    show (d : ℚ) * ((u : ℚ) ^ R / (v : ℚ) ^ R) = d * u ^ R / v ^ R by ring,
    div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hk']
  nlinarith

/-- The admissible range of `q`: `1 ≤ q < 1/λ` with `λ = 6γ`. -/
theorem q_admissible_third :
    (1 : ℚ) ≤ 575769 / 500000 ∧ 6 * gam (1 / 3) * (575769 / 500000) < 1 := by
  norm_num [gam]

/-- **The certificate arithmetic.** -/
theorem starBound_third : starBound (1 / 3) 1012 (575769 / 500000) ≤ 1 / 28684 := by
  have e : starBound (1 / 3) 1012 (575769 / 500000) =
      ((3855517133398885537833564700672 : ℕ) : ℚ) / ((15003 : ℕ) : ℚ) /
        (((575769 : ℕ) : ℚ) / ((500000 : ℕ) : ℚ)) ^ 504 := by
    norm_num [starBound, gam, nBd]
  rw [e]
  have := ratio_le 3855517133398885537833564700672 15003 575769 500000 28684 504
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Nat.le_of_ble_eq_true (by rfl))
  simpa using this

/-- The admissible `q` and the certificate at `β_top = 7/20`, `T_* = 2860`. -/
theorem starBound_seven_twentieths :
    (1 : ℚ) ≤ 1057293 / 1000000 ∧ 6 * gam (7 / 20) * (1057293 / 1000000) < 1 ∧
      starBound (7 / 20) 2860 (1057293 / 1000000) ≤ 1 / 28684 := by
  refine ⟨by norm_num, by norm_num [gam], ?_⟩
  have e : starBound (7 / 20) 2860 (1057293 / 1000000) =
      ((1576096491333154058138101621598208000 : ℕ) : ℚ) / ((1325689 : ℕ) : ℚ) /
        (((1057293 : ℕ) : ℚ) / ((1000000 : ℕ) : ℚ)) ^ 1428 := by
    norm_num [starBound, gam, nBd]
  rw [e]
  have := ratio_le 1576096491333154058138101621598208000 1325689 1057293 1000000 28684 1428
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Nat.le_of_ble_eq_true (by rfl))
  simpa using this

/-- **The lower bound on `x_*`.** With `η = 1/14341`,
`log (2/(1 + e^{-η})) ≥ η/(2 + 2η) = 1/28684`. -/
theorem xstar_lower :
    (1 : ℝ) / 28684 ≤ Real.log (2 / (1 + Real.exp (-(1 / 14341)))) := by
  set η : ℝ := 1 / 14341 with hη
  have hη0 : 0 < η := by norm_num [hη]
  have he : Real.exp (-η) ≤ 1 / (1 + η) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp η])
  have hpos : 0 < 1 + Real.exp (-η) := by positivity
  have hx : 0 < 2 / (1 + Real.exp (-η)) := by positivity
  have hge : 2 * (1 + η) / (2 + η) ≤ 2 / (1 + Real.exp (-η)) := by
    rw [div_le_div_iff₀ (by linarith) hpos]
    have : (1 + Real.exp (-η)) * (1 + η) ≤ 2 + η := by
      have h1 : Real.exp (-η) * (1 + η) ≤ 1 := by
        rw [le_div_iff₀ (by linarith)] at he; linarith
      nlinarith
    nlinarith
  have hlog := Real.one_sub_inv_le_log_of_pos hx
  have hinv : 1 - (2 * (1 + η) / (2 + η))⁻¹ ≤ 1 - (2 / (1 + Real.exp (-η)))⁻¹ := by
    have h0 : 0 < 2 * (1 + η) / (2 + η) := by positivity
    have := inv_anti₀ h0 hge
    linarith
  have hval : 1 - (2 * (1 + η) / (2 + η))⁻¹ = 1 / 28684 := by
    rw [hη]; norm_num
  linarith

/-- **The box certificate from the star bound.** If, on `[0, β_top]`, the pressure
is at most the purity defect `ψ` and `ψ` is at most a bound `B ≤ x`, then `(C)`
holds: `X b ≤ x` for every `b ∈ [0, β_top]`. -/
theorem certificate_of_star (X ψ : ℝ → ℝ) (βtop B x : ℝ)
    (hE3 : ∀ b, 0 ≤ b → b ≤ βtop → X b ≤ ψ b)
    (hstar : ∀ b, 0 ≤ b → b ≤ βtop → ψ b ≤ B) (hB : B ≤ x) :
    ∀ b, 0 ≤ b → b ≤ βtop → X b ≤ x :=
  fun b h0 h1 => (hE3 b h0 h1).trans ((hstar b h0 h1).trans hB)

/-- **The box certificate at `T_* = 1012`, `β_top = 1/3`.** If the pressure is
at most the purity defect and the purity defect is at most the star bound
`𝔅(1/3, 1012, 575769/500000)` on `[0, 1/3]`, then `X b ≤ x_*` there. -/
theorem certificate_third (X ψ : ℝ → ℝ)
    (hE3 : ∀ b, 0 ≤ b → b ≤ 1 / 3 → X b ≤ ψ b)
    (hstar : ∀ b, 0 ≤ b → b ≤ 1 / 3 →
      ψ b ≤ ((starBound (1 / 3) 1012 (575769 / 500000) : ℚ) : ℝ)) :
    ∀ b, 0 ≤ b → b ≤ 1 / 3 →
      X b ≤ Real.log (2 / (1 + Real.exp (-(1 / 14341)))) := by
  refine certificate_of_star X ψ (1 / 3) _ _ hE3 hstar ?_
  refine le_trans ?_ xstar_lower
  have h := starBound_third
  have h' : ((starBound (1 / 3) 1012 (575769 / 500000) : ℚ) : ℝ) ≤ ((1 / 28684 : ℚ) : ℝ) := by
    exact_mod_cast h
  simpa using h'

/-- The one-loop step `c₁ log 2 = 11 log 2/(3π²)` is below `1/3`, so the one-loop
map is a reference map for `β_top = 1/3` and every `0 ≤ D ≤ 1/3 - c₁ log 2`. -/
theorem oneloop_step_lt_third : 11 * Real.log 2 / (3 * Real.pi ^ 2) < 1 / 3 := by
  have hl : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hp : 3.14 < Real.pi := Real.pi_gt_d2
  have hp2 : (3.14 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

end YangMills.StarCert
