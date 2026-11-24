import Mathlib

/-!
# The star threshold of SU(2)

Finite and algebraic parts of Section `sec:stars` of the paper: the seven-spin system
`eq:sevensys`, its closed form (Lemma `lem:sclosed`), the exact threshold
`β_⋆ = (√37 − 5)/3`, the values of Lemma `lem:svalues`, the constants `A` and `B` of
Theorem `thm:uniformthreshold`, the threshold `n ≥ 10/(1 − λ)` and the gap constant
`(1 − λ)/(1250 e²)` of Theorem `thm:C`(iii), and the numbers of Remark `rem:uniformnumbers`.

* `sevenSys_solution`, `sevenSys_unique` : the explicit solution of the seven-spin system and
  its uniqueness whenever the determinant `D(c) = (1 + 2c)(1 − 4c − 6c²)` is nonzero;
* `s_closed`, `one_sub_lam` : `s(c) = (1 + c)/(1 − 4c − 6c²)` and
  `1 − 6c s(c) = (1 − 10c − 12c²)/(1 − 4c − 6c²)`;
* `lam_lt_one_iff`, `lam_lt_one_iff_beta`, `beta_star_bounds` : `6c s(c) < 1` iff
  `c < (√37 − 5)/12`, that is `β_W < (√37 − 5)/3 = 0.36092084…`;
* `svalues`, `s_mono`, `lam_le_of_le` : Lemma `lem:svalues` and the monotonicity of `s`;
* `A_lt`, `B_le`, `half_of_large`, `gap_constant` : Theorem `thm:uniformthreshold` and the
  constants of Theorem `thm:C`(iii);
* `uniform_numbers_*` : Remark `rem:uniformnumbers`.
-/

namespace YangMills.StrongCoupling.StarThreshold

/-! ## The seven-spin system -/

/-- The determinant of the seven-spin system, `D(c) = (1 + 2c)(1 − 4c − 6c²)`. -/
def D (c : ℝ) : ℝ := 1 - 2 * c - 14 * c ^ 2 - 12 * c ^ 3

/-- The denominator `1 − 4c − 6c²` of the closed form of `s`. -/
def den (c : ℝ) : ℝ := 1 - 4 * c - 6 * c ^ 2

theorem D_factor (c : ℝ) : D c = (1 + 2 * c) * den c := by unfold D den; ring

/-- The solution `x_b` of `eq:sevensys`. -/
noncomputable def xb (c : ℝ) : ℝ := (1 - 2 * c - 9 * c ^ 2 - 6 * c ^ 3) / D c
/-- The solution `x_{ā}` of `eq:sevensys`. -/
noncomputable def xa (c : ℝ) : ℝ := c * (1 + 2 * c) / D c
/-- The solution `x_{b̄}` of `eq:sevensys`. -/
noncomputable def xbb (c : ℝ) : ℝ := c ^ 2 * (5 + 6 * c) / D c
/-- The common value `z` of the solution on the four directions `C`. -/
noncomputable def zz (c : ℝ) : ℝ := c * (1 + c) / D c

/-- `s(c) = x_b + x_{ā} + x_{b̄} + 4z`. -/
noncomputable def s (c : ℝ) : ℝ := xb c + xa c + xbb c + 4 * zz c

/-- The star contraction `λ = 6c s(c)`. -/
noncomputable def lam (c : ℝ) : ℝ := 6 * c * s c

/-- The four equations of `eq:sevensys` hold for the explicit solution. -/
theorem sevenSys_solution (c : ℝ) (hD : D c ≠ 0) :
    xb c = 1 + c * (xa c + 4 * zz c) ∧
    xa c = c * (xb c + xbb c + 4 * zz c) ∧
    xbb c = c * (xa c + 4 * zz c) ∧
    zz c = c * (xb c + xa c + xbb c + 2 * zz c) := by
  unfold xb xa xbb zz
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> (try unfold D) <;> ring

/-- Uniqueness: any solution of `eq:sevensys` is the explicit one when `D(c) ≠ 0`. -/
theorem sevenSys_unique (c x₁ x₂ x₃ z : ℝ) (hD : D c ≠ 0)
    (e₁ : x₁ = 1 + c * (x₂ + 4 * z)) (e₂ : x₂ = c * (x₁ + x₃ + 4 * z))
    (e₃ : x₃ = c * (x₂ + 4 * z)) (e₄ : z = c * (x₁ + x₂ + x₃ + 2 * z)) :
    x₁ = xb c ∧ x₂ = xa c ∧ x₃ = xbb c ∧ z = zz c := by
  unfold xb xa xbb zz
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [eq_div_iff hD] <;> unfold D
  · linear_combination (-6*c^3 - 9*c^2 - 2*c + 1) * e₁ + (2*c^2 + c) * e₂ +
      (6*c^3 + 5*c^2) * e₃ + (4*c^2 + 4*c) * e₄
  · linear_combination (2*c^2 + c) * e₁ + (-8*c^2 - 2*c + 1) * e₂ + (2*c^2 + c) * e₃ +
      (8*c^2 + 4*c) * e₄
  · linear_combination (6*c^3 + 5*c^2) * e₁ + (2*c^2 + c) * e₂ +
      (-6*c^3 - 9*c^2 - 2*c + 1) * e₃ + (4*c^2 + 4*c) * e₄
  · linear_combination (c^2 + c) * e₁ + (2*c^2 + c) * e₂ + (c^2 + c) * e₃ +
      (1 - 2*c^2) * e₄

/-- On `[0, 1/6]` the denominator is at least `1/6`. -/
theorem den_ge (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1 / 6) : 1 / 6 ≤ den c := by
  unfold den; nlinarith

theorem D_pos (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1 / 6) : 0 < D c := by
  rw [D_factor]; have := den_ge c h0 h1; positivity

/-- Lemma `lem:sclosed`: `s(c) = (1 + c)/(1 − 4c − 6c²)`. -/
theorem s_closed (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1 / 6) : s c = (1 + c) / den c := by
  have hD := (D_pos c h0 h1).ne'
  have hd : den c ≠ 0 := (lt_of_lt_of_le (by norm_num) (den_ge c h0 h1)).ne'
  have h2 : (1 + 2 * c) ≠ 0 := by linarith
  unfold s xb xa xbb zz
  rw [D_factor]
  field_simp
  ring

/-- Lemma `lem:sclosed`: `1 − 6c s(c) = (1 − 10c − 12c²)/(1 − 4c − 6c²)`. -/
theorem one_sub_lam (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1 / 6) :
    1 - lam c = (1 - 10 * c - 12 * c ^ 2) / den c := by
  have hd : den c ≠ 0 := (lt_of_lt_of_le (by norm_num) (den_ge c h0 h1)).ne'
  unfold lam; rw [s_closed c h0 h1]; field_simp; unfold den; ring

/-- The positive root `c_* = (√37 − 5)/12` of `12c² + 10c − 1`. -/
noncomputable def cstar : ℝ := (Real.sqrt 37 - 5) / 12

/-- The threshold `β_⋆ = (√37 − 5)/3 = 4 c_*`. -/
noncomputable def betaStar : ℝ := (Real.sqrt 37 - 5) / 3

theorem sqrt37_sq : Real.sqrt 37 ^ 2 = 37 := Real.sq_sqrt (by norm_num)

/-- `6.0827625 < √37 < 6.0827626`. -/
theorem sqrt37_bounds : 6.0827625 < Real.sqrt 37 ∧ Real.sqrt 37 < 6.0827626 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `β_⋆ = (√37 − 5)/3 = 0.36092084…`, and `c_* < 1/6`. -/
theorem beta_star_bounds : 0.36092083 < betaStar ∧ betaStar < 0.36092087 ∧ cstar < 1 / 6 := by
  obtain ⟨h1, h2⟩ := sqrt37_bounds
  unfold betaStar cstar
  refine ⟨by linarith, by linarith, by linarith⟩

theorem quad_pos_iff (c : ℝ) (h0 : 0 ≤ c) : 0 < 1 - 10 * c - 12 * c ^ 2 ↔ c < cstar := by
  have hs := sqrt37_sq
  have hs0 : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg _
  unfold cstar
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    nlinarith

/-- Lemma `lem:sclosed`: for `0 ≤ c ≤ 1/6`, `6c s(c) < 1` iff `c < c_* = (√37 − 5)/12`. -/
theorem lam_lt_one_iff (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1 / 6) : lam c < 1 ↔ c < cstar := by
  have hd := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 6) (den_ge c h0 h1)
  rw [← quad_pos_iff c h0, ← sub_pos, one_sub_lam c h0 h1, div_pos_iff_of_pos_right hd]

/-- In the Wilson coupling `b = β_W = 4c`: `1 − λ = 2(4 − 10b − 3b²)/(8 − 8b − 3b²)`. -/
theorem one_sub_lam_beta (b : ℝ) (h0 : 0 ≤ b) (h1 : b ≤ 2 / 3) :
    1 - lam (b / 4) = 2 * (4 - 10 * b - 3 * b ^ 2) / (8 - 8 * b - 3 * b ^ 2) := by
  have hd := den_ge (b / 4) (by positivity) (by linarith)
  have hd' : (8 - 8 * b - 3 * b ^ 2) ≠ 0 := by unfold den at hd; nlinarith
  have hd'' : (1 - 4 * (b / 4) - 6 * (b / 4) ^ 2) ≠ 0 := by unfold den at hd; linarith
  rw [one_sub_lam (b / 4) (by positivity) (by linarith)]
  unfold den
  rw [div_eq_div_iff hd'' hd']
  ring

/-- `λ < 1` iff `β_W < β_⋆ = (√37 − 5)/3`, for `0 ≤ β_W ≤ 2/3`. -/
theorem lam_lt_one_iff_beta (b : ℝ) (h0 : 0 ≤ b) (h1 : b ≤ 2 / 3) :
    lam (b / 4) < 1 ↔ b < betaStar := by
  rw [lam_lt_one_iff (b / 4) (by positivity) (by linarith)]
  unfold cstar betaStar
  constructor <;> intro h <;> linarith

/-! ## Lemma `lem:svalues` -/

/-- Lemma `lem:svalues`: the solution vectors and the values of `s` and `6c s(c)` at
`c = 1/12, 7/80, 9/100`. -/
theorem svalues :
    (xb (1/12), xa (1/12), xbb (1/12), zz (1/12)) = (221/210, 28/210, 11/210, 26/210) ∧
    s (1/12) = 26/15 ∧ lam (1/12) = 13/15 ∧
    (xb (7/80), xa (7/80), xbb (7/80), zz (7/80)) =
      (192531/181702, 26320/181702, 10829/181702, 24360/181702) ∧
    s (7/80) = 3480/1933 ∧ lam (7/80) = 1827/1933 ∧
    (xb (9/100), xa (9/100), xbb (9/100), zz (9/100)) =
      (371363/348926, 53100/348926, 22437/348926, 49050/348926) ∧
    s (9/100) = 5450/2957 ∧ lam (9/100) = 2943/2957 := by
  simp only [lam, s, xb, xa, xbb, zz, D, Prod.mk.injEq]
  norm_num

/-- `s` is nondecreasing on `[0, 1/6]`. -/
theorem s_mono {c c' : ℝ} (h0 : 0 ≤ c) (hc : c ≤ c') (h1 : c' ≤ 1 / 6) : s c ≤ s c' := by
  rw [s_closed c h0 (hc.trans h1), s_closed c' (h0.trans hc) h1]
  have hd := den_ge c h0 (hc.trans h1)
  have hd' := den_ge c' (h0.trans hc) h1
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  unfold den at *
  have hk : 0 ≤ (c' - c) * (6 * c * c' + 6 * c + 6 * c' + 5) := by
    apply mul_nonneg (by linarith); nlinarith
  nlinarith

/-- Lemma `lem:svalues`, last claim: `6c s(c) ≤ 2943/2957` for `0 ≤ c ≤ 9/100`. -/
theorem lam_le_of_le (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 9 / 100) : lam c ≤ 2943 / 2957 := by
  have hs := s_mono h0 h1 (by norm_num)
  have hs0 : 0 ≤ s c := by
    rw [s_closed c h0 (by linarith)]
    have := den_ge c h0 (by linarith); positivity
  have hv : lam (9/100) = 2943/2957 := svalues.2.2.2.2.2.2.2.2
  unfold lam at *
  calc 6 * c * s c ≤ 6 * (9 / 100) * s (9 / 100) := by
        apply mul_le_mul (by linarith) hs hs0 (by norm_num)
    _ = 2943 / 2957 := hv

/-! ## Theorem `thm:uniformthreshold` -/

/-- The constant `A = (1 + 3c + 3λ)/(1 − λ)`. -/
noncomputable def A (c : ℝ) : ℝ := (1 + 3 * c + 3 * lam c) / (1 - lam c)

/-- The constant `B = 6 + 18λ/(1 − λ)`. -/
noncomputable def B (c : ℝ) : ℝ := 6 + 18 * lam c / (1 - lam c)

theorem lam_nonneg (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1 / 6) : 0 ≤ lam c := by
  unfold lam; rw [s_closed c h0 h1]; have := den_ge c h0 h1; positivity

/-- Theorem `thm:uniformthreshold`: `A < 4.2708/(1 − λ)` for `0 ≤ c < c_*`. -/
theorem A_lt (c : ℝ) (h0 : 0 ≤ c) (hc : c < cstar) : A c < 4.2708 / (1 - lam c) := by
  have hc6 : c ≤ 1 / 6 := by linarith [beta_star_bounds.2.2]
  have hl : lam c < 1 := (lam_lt_one_iff c h0 hc6).2 hc
  have hcs : cstar < 0.090231 := by unfold cstar; linarith [sqrt37_bounds.2]
  unfold A
  rw [div_lt_div_iff_of_pos_right (by linarith)]
  linarith

/-- Theorem `thm:uniformthreshold`: `B ≤ 27/(4(1 − λ)²)` whenever `λ < 1`, because
`(1 − λ)(6 + 12λ) = 27/4 − 12(λ − 1/4)² ≤ 27/4`. -/
theorem B_le (c : ℝ) (h1 : lam c < 1) :
    B c ≤ 27 / (4 * (1 - lam c) ^ 2) := by
  have hp : 0 < 1 - lam c := by linarith
  unfold B
  rw [le_div_iff₀ (by positivity)]
  have : (6 + 18 * lam c / (1 - lam c)) * (4 * (1 - lam c) ^ 2)
      = 4 * ((1 - lam c) * (6 + 12 * lam c)) := by field_simp; ring
  rw [this]
  nlinarith [sq_nonneg (lam c - 1 / 4)]

/-- Theorem `thm:C`(iii) and `thm:uniformthreshold`(ii): if `n ≥ 10/(1 − λ)` then
`1 − A/n − B/n² ≥ 1/2`, so the cube condition `BP(n, 1/2)` follows from part (i). -/
theorem half_of_large (c n : ℝ) (h0 : 0 ≤ c) (hc : c < cstar) (hn : 10 / (1 - lam c) ≤ n) :
    1 / 2 ≤ 1 - A c / n - B c / n ^ 2 := by
  have hc6 : c ≤ 1 / 6 := by linarith [beta_star_bounds.2.2]
  have hl : lam c < 1 := (lam_lt_one_iff c h0 hc6).2 hc
  have hl0 := lam_nonneg c h0 hc6
  have hp : 0 < 1 - lam c := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hA := A_lt c h0 hc
  have hB := B_le c hl
  -- `1/n ≤ (1 − λ)/10`
  have hinv : 1 / n ≤ (1 - lam c) / 10 := by
    rw [div_le_iff₀ hn0]; rw [div_le_iff₀ hp] at hn; nlinarith
  have hA' : A c / n ≤ 0.42708 := by
    have hA0 : 0 ≤ A c := by unfold A; apply div_nonneg <;> linarith
    calc A c / n = A c * (1 / n) := by ring
      _ ≤ (4.2708 / (1 - lam c)) * ((1 - lam c) / 10) := by
          apply mul_le_mul hA.le hinv (by positivity) (by positivity)
      _ = 0.42708 := by field_simp; norm_num
  have hB' : B c / n ^ 2 ≤ 0.0675 := by
    have hB0 : 0 ≤ B c := by unfold B; have := div_nonneg (by linarith : (0:ℝ) ≤ 18 * lam c) hp.le; linarith
    calc B c / n ^ 2 = B c * (1 / n) ^ 2 := by ring
      _ ≤ (27 / (4 * (1 - lam c) ^ 2)) * ((1 - lam c) / 10) ^ 2 := by
          apply mul_le_mul hB (pow_le_pow_left₀ (by positivity) hinv 2) (by positivity)
            (by positivity)
      _ = 0.0675 := by field_simp; norm_num
  linarith

/-- Theorem `thm:C`(iii): the lower bound of Theorem `thm:uniformthreshold`(iv) on the
transfer-matrix gap is at least `(1 − λ)/(1250 e²)`, attained at an integer `n ≥ 10`. -/
theorem gap_constant (c : ℝ) (h0 : 0 ≤ c) (hc : c < cstar) :
    ∃ n : ℕ, 10 ≤ n ∧
      (1 - lam c) / (1250 * Real.exp 2) ≤
        (1 - A c / n - B c / n ^ 2) / (Real.exp 2 * (2 + 1 / (n : ℝ)) ^ 4 * n) := by
  have hc6 : c ≤ 1 / 6 := by linarith [beta_star_bounds.2.2]
  have hl : lam c < 1 := (lam_lt_one_iff c h0 hc6).2 hc
  have hl0 := lam_nonneg c h0 hc6
  have hp : 0 < 1 - lam c := by linarith
  set m : ℝ := 10 / (1 - lam c) with hm
  have hm10 : 10 ≤ m := by rw [hm, le_div_iff₀ hp]; linarith
  refine ⟨⌈m⌉₊, ?_, ?_⟩
  · have : (10 : ℝ) ≤ ⌈m⌉₊ := le_trans hm10 (Nat.le_ceil m)
    exact_mod_cast this
  · set n : ℝ := (⌈m⌉₊ : ℝ) with hn
    have hmn : m ≤ n := Nat.le_ceil m
    have hn1 : n < m + 1 := Nat.ceil_lt_add_one (by linarith)
    have hn10 : 10 ≤ n := le_trans hm10 hmn
    have hn0 : 0 < n := by linarith
    have hhalf := half_of_large c n h0 hc hmn
    have he := Real.exp_pos 2
    have hq : (2 + 1 / n) ^ 4 ≤ (2.1 : ℝ) ^ 4 := by
      apply pow_le_pow_left₀ (by positivity)
      have : 1 / n ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hn10
      linarith
    -- `n ≤ 11/(1 − λ)`
    have hn11 : n * (1 - lam c) ≤ 11 := by
      have : m * (1 - lam c) = 10 := by rw [hm]; field_simp
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hden : Real.exp 2 * (2 + 1 / n) ^ 4 * n ≤ Real.exp 2 * 2.1 ^ 4 * n := by
      apply mul_le_mul_of_nonneg_right _ hn0.le
      exact mul_le_mul_of_nonneg_left hq he.le
    calc (1 - lam c) * (Real.exp 2 * (2 + 1 / n) ^ 4 * n)
        ≤ (1 - lam c) * (Real.exp 2 * 2.1 ^ 4 * n) := mul_le_mul_of_nonneg_left hden hp.le
      _ = Real.exp 2 * 2.1 ^ 4 * (n * (1 - lam c)) := by ring
      _ ≤ Real.exp 2 * 2.1 ^ 4 * 11 := by
          apply mul_le_mul_of_nonneg_left hn11; positivity
      _ ≤ (1 / 2) * (1250 * Real.exp 2) := by nlinarith
      _ ≤ (1 - A c / n - B c / n ^ 2) * (1250 * Real.exp 2) := by
          apply mul_le_mul_of_nonneg_right hhalf; positivity

/-! ## Remark `rem:uniformnumbers` -/

/-- `1 − A/n − B/n² ≥ 1/2` is `n² − 2An − 2B ≥ 0`. -/
theorem half_iff (A B n : ℝ) (hn : 0 < n) :
    1 / 2 ≤ 1 - A / n - B / n ^ 2 ↔ 0 ≤ n ^ 2 - 2 * A * n - 2 * B := by
  have h2 : 0 < 2 * n ^ 2 := by positivity
  have key : 1 - A / n - B / n ^ 2 - 1 / 2 = (n ^ 2 - 2 * A * n - 2 * B) / (2 * n ^ 2) := by
    field_simp; ring
  constructor
  · intro h
    have h' : 0 ≤ (n ^ 2 - 2 * A * n - 2 * B) / (2 * n ^ 2) := by rw [← key]; linarith
    have := mul_nonneg h' h2.le
    rwa [div_mul_cancel₀ _ h2.ne'] at this
  · intro h
    have : 0 ≤ (n ^ 2 - 2 * A * n - 2 * B) / (2 * n ^ 2) := div_nonneg h h2.le
    linarith

/-- Remark `rem:uniformnumbers` at `β_W = 7/20` (`c = 7/80`): `1 − λ = 106/1933`,
`A < 74.731`, `B < 316.25`, and `1 − A/n − B/n² ≥ 1/2` exactly for `n ≥ 154` among the
integers `n ≥ 2`. -/
theorem uniform_numbers_7_20 :
    1 - lam (7/80) = 106/1933 ∧ A (7/80) < 74.731 ∧ B (7/80) < 316.25 ∧
    (∀ n : ℕ, 154 ≤ n → 1 / 2 ≤ 1 - A (7/80) / n - B (7/80) / (n : ℝ) ^ 2) ∧
    ¬ (1 / 2 ≤ 1 - A (7/80) / (153 : ℝ) - B (7/80) / (153 : ℝ) ^ 2) := by
  have hl : lam (7/80) = 1827/1933 := svalues.2.2.2.2.2.1
  have hA : A (7/80) = (1 + 3 * (7/80) + 3 * (1827/1933)) / (106/1933) := by
    unfold A; rw [hl]; norm_num
  have hB : B (7/80) = 6 + 18 * (1827/1933) / (106/1933) := by unfold B; rw [hl]; norm_num
  refine ⟨by rw [hl]; norm_num, by rw [hA]; norm_num, by rw [hB]; norm_num, ?_, ?_⟩
  · intro n hn
    have hn' : (154 : ℝ) ≤ n := by exact_mod_cast hn
    rw [half_iff _ _ _ (by linarith), hA, hB]
    nlinarith
  · rw [half_iff _ _ _ (by norm_num), hA, hB]; norm_num

/-- Remark `rem:uniformnumbers` at `β_W = 9/25` (`c = 9/100`): `1 − λ = 14/2957`,
`A < 898.89`, `B < 3789.9`, and the threshold `n ≥ 1802` is exact. -/
theorem uniform_numbers_9_25 :
    1 - lam (9/100) = 14/2957 ∧ A (9/100) < 898.89 ∧ B (9/100) < 3789.9 ∧
    (∀ n : ℕ, 1802 ≤ n → 1 / 2 ≤ 1 - A (9/100) / n - B (9/100) / (n : ℝ) ^ 2) ∧
    ¬ (1 / 2 ≤ 1 - A (9/100) / (1801 : ℝ) - B (9/100) / (1801 : ℝ) ^ 2) := by
  have hl : lam (9/100) = 2943/2957 := svalues.2.2.2.2.2.2.2.2
  have hA : A (9/100) = (1 + 3 * (9/100) + 3 * (2943/2957)) / (14/2957) := by
    unfold A; rw [hl]; norm_num
  have hB : B (9/100) = 6 + 18 * (2943/2957) / (14/2957) := by unfold B; rw [hl]; norm_num
  refine ⟨by rw [hl]; norm_num, by rw [hA]; norm_num, by rw [hB]; norm_num, ?_, ?_⟩
  · intro n hn
    have hn' : (1802 : ℝ) ≤ n := by exact_mod_cast hn
    rw [half_iff _ _ _ (by linarith), hA, hB]
    nlinarith
  · rw [half_iff _ _ _ (by norm_num), hA, hB]; norm_num

/-- Remark `rem:uniformnumbers`: the cube constants `(1 − λ)^5/10⁴ ≈ 4.96·10⁻¹¹` at
`β_W = 7/20`, and `(106/1933)·517⁻⁴ ≈ 7.68·10⁻¹³` of Theorem `thm:starsuniform`. -/
theorem uniform_numbers_varpi :
    4.95e-11 < (106/1933 : ℝ) ^ 5 / 10 ^ 4 ∧ (106/1933 : ℝ) ^ 5 / 10 ^ 4 < 4.97e-11 ∧
    7.67e-13 < (106/1933 : ℝ) / 517 ^ 4 ∧ (106/1933 : ℝ) / 517 ^ 4 < 7.69e-13 := by
  norm_num

end YangMills.StrongCoupling.StarThreshold
