import Mathlib

/-!
# One-cube criteria: exact rational constants (checks L1–L9, L14, L15)

Each theorem is an identity or inequality between explicit rationals (or a
polynomial inequality over `ℚ`/`ℝ`), proved by `norm_num`, `nlinarith` or `ring`.
These checks certify arithmetic only. They do not prove the existence of the
continuum limit, the one-cube bound or the mass gap.
-/

namespace YangMills.OneCube

/-! ## L1: the purity conversion `2x - 3x² ≥ 1/4097` at `x = 1/8192` -/

theorem L1 : (1 : ℚ) / 4097 ≤ 2 * (1 / 8192) - 3 * (1 / 8192) ^ 2 := by norm_num

theorem L1_exact : 2 * ((1 : ℚ) / 8192) - 3 * (1 / 8192) ^ 2 = 16381 / 67108864 ∧
    (16381 : ℚ) / 67108864 - 1 / 4097 = 4093 / 274945015808 := by norm_num

/-! ## L2: window counts -/

theorem L2_counts : (40 * 96 ^ 3 : ℕ) = 35389440 ∧ (161 * 48 ^ 3 : ℕ) = 17805312 := by norm_num

theorem L2 : (1 : ℚ) / 17805313 ≤ 2 * (1 / (322 * 48 ^ 3)) - 3 * (1 / (322 * 48 ^ 3)) ^ 2 := by
  norm_num

/-- The general certificate of L2: with `a ≥ 3`, `1/(a+1) ≤ 2x - 3x²` at `x = 1/(2a)`. -/
theorem L2_general (a : ℚ) (ha : 3 ≤ a) :
    1 / (a + 1) ≤ 2 * (1 / (2 * a)) - 3 * (1 / (2 * a)) ^ 2 := by
  have h0 : 0 < a := by linarith
  rw [div_le_iff₀ (by linarith)]
  field_simp
  nlinarith

/-- Balaban-constant row: `4 · 17805312 = 71221248` and `1/71221248 > 1.404·10⁻⁸`. -/
theorem L2_balaban : (4 * 17805312 : ℕ) = 71221248 ∧ (1.404e-8 : ℚ) < 1 / 71221248 := by
  norm_num

/-! ## L3: residue split (rational part; the `log`/`exp` parts are in `Transcendental`) -/

theorem L3_rat : (3 : ℚ) / 49155 = 1 / 16385 ∧
    ((1 : ℚ) / 16385) / (1 - 1 / 16385) = 1 / 2 ^ 14 ∧
    (2 : ℚ) * (1 / 2 ^ 14) = 1 / 2 ^ 13 ∧
    (49155 : ℕ) = 3 * 16385 ∧ (16385 : ℕ) = 2 ^ 14 + 1 := by norm_num

/-! ## L4: hypercube converse -/

theorem L4 : (16 : ℚ) / 8191 ^ 2 + 8 / 511 ^ 2 + 4 / 255 ^ 2 + 2 / 127 ^ 2 < 2.17e-4 ∧
    (2.17e-4 : ℚ) < 1 / 4097 := by norm_num

theorem L4_sharp : (16 : ℚ) / 8191 ^ 2 + 8 / 511 ^ 2 + 4 / 255 ^ 2 + 2 / 127 ^ 2 < 2.1640e-4 ∧
    (2.4408e-4 : ℚ) < 1 / 4097 := by norm_num

/-- Casimir-criterion row (no separate identifier in the paper's table). -/
theorem L4_casimir : (11 : ℚ) / 10 ^ 5 + 1 / 299 ^ 2 < 1.21186e-4 ∧
    (1.21186e-4 : ℚ) < 1.22070e-4 ∧ (1.22070e-4 : ℚ) < 1 / 8192 ∧
    (1 : ℚ) / 127 ^ 2 + 2 / 255 ^ 2 + 4 / 511 ^ 2 < 1.08077e-4 ∧
    (1.08077e-4 : ℚ) < 1.081e-4 ∧ (1.081e-4 : ℚ) < 11 / 10 ^ 5 ∧
    (1 : ℚ) / 8191 ^ 2 ≤ 1 / 300 := by norm_num

/-! ## L5: exclusivity, `q_N = (4N³ - 6N + 3)/N³ ≥ 23/8` for every `N ≥ 2` -/

theorem L5 (N : ℕ) (hN : 2 ≤ N) :
    (23 : ℚ) / 8 ≤ (4 * (N : ℚ) ^ 3 - 6 * N + 3) / (N : ℚ) ^ 3 := by
  have h2 : (2 : ℚ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℚ) < (N : ℚ) ^ 3 := by positivity
  rw [le_div_iff₀ hpos]
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h2),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h2)) (sub_nonneg.mpr h2)]

theorem L5_value : (4 * (2 : ℚ) ^ 3 - 6 * 2 + 3) / 2 ^ 3 = 23 / 8 := by norm_num

theorem L5_consequences : ((23 : ℚ) / 8 - 4097 / 4096) / (9 / 8) > 1.666 ∧
    ((23 : ℚ) / 8 - 4097 / 4096) / 4 > 0.468 ∧
    (23 : ℚ) / 8 - 9 / 8 * (1 / 4096) > 2.874 := by norm_num

/-! ## L6: the large-`N_c` constant -/

theorem L6 : (239 * 161 * 48 ^ 3 : ℕ) = 4255469568 ∧ (4 * 4255469568 : ℕ) = 17021878272 ∧
    (17021878272 : ℚ) < 1.71e10 := by norm_num

/-- `α = 36β/(1 - 12β)` at the four tabulated couplings. -/
theorem L6_alpha :
    36 * ((1 : ℚ) / 480) / (1 - 12 * (1 / 480)) = 1 / 13 ∧
    36 * ((1 : ℚ) / 192) / (1 - 12 * (1 / 192)) = 1 / 5 ∧
    36 * ((1 : ℚ) / 96) / (1 - 12 * (1 / 96)) = 3 / 7 ∧
    36 * ((1 : ℚ) / 64) / (1 - 12 * (1 / 64)) = 9 / 13 := by norm_num

/-! ## L7: fixed-torus gap and base scale -/

theorem L7 : (1 : ℚ) / 2 + 8 / 3 + 3 / 2 = 14 / 3 ∧ (3 : ℚ) * (14 / 3) = 14 ∧
    (56 * 6 : ℕ) = 336 ∧ (9.6 : ℚ) / 336 = 1 / 35 := by norm_num

/-- The length bound behind `14/3`: `(ℓᵢ+ℓⱼ)² ≤ 2(ℓᵢ²+ℓⱼ²)` and `(ℓ₁+ℓ₂+ℓ₃)² ≤ 3Σℓᵢ²`. -/
theorem L7_lengths (l1 l2 l3 : ℝ) :
    (1 / 2) * (l1 ^ 2 + l2 ^ 2 + l3 ^ 2) +
      (2 / 3) * ((l1 + l2) ^ 2 + (l1 + l3) ^ 2 + (l2 + l3) ^ 2) +
      (1 / 2) * (l1 + l2 + l3) ^ 2 ≤ (14 / 3) * (l1 ^ 2 + l2 ^ 2 + l3 ^ 2) := by
  nlinarith [sq_nonneg (l1 - l2), sq_nonneg (l1 - l3), sq_nonneg (l2 - l3)]

/-- Base-scale arithmetic (rational part of J5). -/
theorem L7_base : (0.632 : ℚ) * 15.30 ≥ 9.6 ∧ (9.6 : ℚ) / 0.632 < 15.19 ∧
    (0.632 : ℚ) ^ 3 / (56 * 9.6 ^ 2) > 4.8912e-5 ∧ (5 * 96 ^ 3 : ℕ) = 4423680 := by norm_num

/-! ## L8: window-level split bookkeeping -/

theorem L8 : (2 : ℚ) * (161 / 645) * (645 / 644) = 1 / 2 ∧ (644 : ℕ) = 4 * 161 ∧
    (322 : ℕ) = 2 * 161 := by norm_num

theorem L8_ineq (x : ℚ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 3) : 1 - 2 * x + 2 * x ^ 2 ≤ 1 - x - x ^ 2 := by
  nlinarith

/-! ## L9: the window margin -/

theorem L9 :
    let q : ℚ := 1 - 1 / 320 + 1 / (2 * 320 ^ 2)
    (160 : ℚ) / 161 - (q ^ 2 + (1 - q) ^ 2) = 32359519 / 3376414720000 := by norm_num

theorem L9_pos : (0 : ℚ) < 32359519 / 3376414720000 := by norm_num

/-! ## L14: universal steps and the ascent iterates -/

theorem L14_rat : (1728 : ℚ) / 216 ^ 2 = 1 / 27 ∧ (216 * 8192 : ℕ) = 1769472 := by norm_num

theorem L14_binom (y : ℝ) (hy : 1 / 8 ≤ y) : 1 + y ≤ 1 + 8 * y ^ 2 ∧ 1 + 8 * y ^ 2 ≤ (1 + y ^ 2) ^ 8 := by
  refine ⟨by nlinarith, ?_⟩
  have := one_add_mul_le_pow (a := y ^ 2) (by nlinarith [sq_nonneg y]) 8
  push_cast at this
  linarith

theorem L14_binom2 (y : ℝ) (hy : 0 ≤ y) : 1 + 4 * y ≤ (1 + y / 2) ^ 8 := by
  have := one_add_mul_le_pow (a := y / 2) (by linarith) 8
  push_cast at this
  linarith

theorem L14_floor (y m : ℝ) (hy : 1 ≤ y) (hm0 : 0 < m) (hm : m ≤ y + 1) : y / 2 ≤ y ^ 2 / m := by
  rw [le_div_iff₀ hm0]
  nlinarith

/-- The majorant map `g(x) = (64x/(1-64x))²` of the ascent. -/
def gAsc (x : ℚ) : ℚ := (64 * x / (1 - 64 * x)) ^ 2

/-- Iterates of `g` from `x₀ = 1/8192`, in exact rational arithmetic. -/
def gIter : ℕ → ℚ
  | 0 => 1 / 8192
  | n + 1 => gAsc (gIter n)

theorem gIter_one : gIter 1 = 1 / 16129 := by norm_num [gIter, gAsc]

theorem L14_iterates :
    gIter 1 ≤ 6.2001e-5 ∧ gIter 2 ≤ 1.5871e-5 ∧ gIter 3 ≤ 1.03381e-6 ∧ gIter 4 ≤ 4.3783e-9 := by
  norm_num [gIter, gAsc]

theorem L14_scales :
    64 * gIter 1 < 3.9681e-3 ∧ 64 * gIter 2 < 1.0158e-3 ∧ 64 * gIter 3 ≤ 6.6164e-5 ∧
    64 * gIter 3 ≤ 6.62e-5 ∧ (6.62e-5 : ℚ) ≤ 1 / 8192 ∧
    (1 : ℚ) / 8192 < 64 * gIter 1 ∧ (1 : ℚ) / 8192 < 64 * gIter 2 ∧ 2 * ((1 : ℚ) / 8192) = 1 / 4096 := by
  norm_num [gIter, gAsc]

theorem L14_x4 : gIter 4 < 2.825e-8 ∧ (2.825e-8 : ℚ) < 1 / 35389440 := by
  norm_num [gIter, gAsc]

/-- One-directionality witness at `ρ = 1/1769473` (rational part). -/
theorem L14_witness :
    (216 : ℚ) * (1 / 1769473) < 1 / 8192 ∧
    (432 * 4097 * (1769473 - 1) - 1769473 ^ 2 : ℤ) = 430 * 1769473 - 431 ∧
    (0 : ℤ) < 430 * 1769473 - 431 ∧
    (1 : ℚ) / 4097 < 432 * (1 / 1769473) * (1 - 1 / 1769473) := by norm_num

/-! ## L15: non-implication, the four exact rational pairs -/

/-- The pair `(1/c² + 3, 4/(c²+1) + 2)`, written in `t = c²`. -/
def pairX1 (t : ℚ) : ℚ × ℚ := (1 / t + 3, 4 / (t + 1) + 2)

theorem L15 : pairX1 (1 / 2) = (5, 14 / 3) ∧ pairX1 (9 / 10) = (37 / 9, 78 / 19) ∧
    pairX1 2 = (7 / 2, 10 / 3) ∧ pairX1 4 = (13 / 4, 14 / 5) := by
  norm_num [pairX1]

theorem L15_difference (t : ℚ) (ht : 0 < t) :
    (pairX1 t).1 - (pairX1 t).2 = (t - 1) ^ 2 / (t * (t + 1)) := by
  simp only [pairX1]
  field_simp
  ring

end YangMills.OneCube
