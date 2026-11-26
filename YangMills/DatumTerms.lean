import Mathlib

/-!
# The first corrections to the datum and the icosahedral design

Arithmetic of Propositions `ly:prop:second` and `ly:prop:design` of the paper and of the
recoupling example after them. The cluster enumeration and the Haar integrals are not
formalised here; the theorems check the algebra that turns the cluster list into the
bracket of `ly:eq:second`, the expansion in `u = a_{1/2}`, the comparison with the momentum
average of Muenster's effective transfer matrix, the Racah sum of the 6j symbol
`{1 1 1; 1/2 1/2 1/2}`, and the character sums of the binary icosahedral group that make it
a spherical 11-design (classes with `cos t = ±1, ±(1+√5)/4, ±(√5-1)/4, ±1/2, 0` and sizes
`1, 1, 12, 12, 12, 12, 20, 20, 30`; `χ_J = U_{2J}(cos t)`, Chebyshev of the second kind).

* `bracket_collect` : counts times amplitudes (divided by `u^{4T}`) equal
  `48 T³ (1 + T x + C(T,2) (3v - 4u²)²)`, `x = 3v - 4u² + 12u⁴`.
* `bracket_in_u` : with `v = 2u²/3 + 2u⁴/9 + w u⁶`, the bracket is
  `1 - 2Tu² + (2T² + 32T/3)u⁴ + u⁶ R`.
* `a1_in_u` : `β²/24 - β⁴/384` at `β = 4u + 8u³/3 + y u⁵` is `2u²/3 + 2u⁴/9 + u⁶ R'`.
* `muenster_check` : `-x + x²/2` at `x = -2u² + 38u⁴/3 + y u⁶` is `2u² - 32u⁴/3 + u⁶ R''`.
* `x_in_u` : `3(2u²/3 + 2u⁴/9) - 4u² + 12u⁴ = -2u² + 38u⁴/3`.
* `sixj_racah` : the Racah sum `(-1)³ 4!/72 = -1/3` and `Δ`-product `(1/24)(1/6)³ = (1/72)²`.
* `sixj_amplitude` : `3·3·2·3·(1/3)² = 6`; `sixj_count` : `24·4·3·2 = 576`.
* `chebU_sum_n` (`n = 1, ..., 12`) : the class sums of `U_n` vanish for `1 ≤ n ≤ 11` and equal
  `120` for `n = 12`.
* `design_excess` : the leading coefficient `1/2724986880` of the 2I excess.
-/

namespace YangMills.DatumTerms

/-- Chebyshev polynomials of the second kind. -/
noncomputable def chebU : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | (n + 2), x => 2 * x * chebU (n + 1) x - chebU n x

/-- The class sum `Σ_{g ∈ 2I} χ_{n/2}(g)` in terms of `s = √5`. -/
noncomputable def classSum (n : ℕ) (s : ℝ) : ℝ :=
  chebU n 1 + chebU n (-1) + 12 * (chebU n ((1 + s) / 4) + chebU n (-((1 + s) / 4))
    + chebU n ((s - 1) / 4) + chebU n (-((s - 1) / 4)))
    + 20 * (chebU n (1 / 2) + chebU n (-(1 / 2))) + 30 * chebU n 0

theorem bracket_collect (T u v : ℝ) :
    2 * (24 * T ^ 3 * 1 + 24 * T ^ 4 * (3 * v) + 12 * T ^ 4 * (T - 1) * (9 * v ^ 2)
        + 288 * T ^ 4 * u ^ 4 + 12 * T ^ 4 * (T - 1) * (-16 * u ^ 4))
      - 16 * T ^ 4 * (3 * (4 * u ^ 2) + 3 * (T - 1) * (12 * u ^ 2 * v)
        + 3 * (T - 1) * (-16 * u ^ 4))
    = 48 * T ^ 3 * (1 + T * (3 * v - 4 * u ^ 2 + 12 * u ^ 4)
        + T * (T - 1) / 2 * (3 * v - 4 * u ^ 2) ^ 2) := by
  ring

theorem bracket_in_u (T u w : ℝ) :
    1 + T * (3 * (2 / 3 * u ^ 2 + 2 / 9 * u ^ 4 + w * u ^ 6) - 4 * u ^ 2 + 12 * u ^ 4)
      + T * (T - 1) / 2 * (3 * (2 / 3 * u ^ 2 + 2 / 9 * u ^ 4 + w * u ^ 6) - 4 * u ^ 2) ^ 2
    = 1 - 2 * T * u ^ 2 + (2 * T ^ 2 + 32 / 3 * T) * u ^ 4 + u ^ 6 * (9*T^2*u^6*w^2/2 + 2*T^2*u^4*w - 6*T^2*u^2*w + 2*T^2*u^2/9 - 4*T^2/3 - 9*T*u^6*w^2/2 - 2*T*u^4*w + 6*T*u^2*w - 2*T*u^2/9 + 3*T*w + 4*T/3) := by
  ring

theorem a1_in_u (u y : ℝ) :
    (4 * u + 8 / 3 * u ^ 3 + y * u ^ 5) ^ 2 / 24 - (4 * u + 8 / 3 * u ^ 3 + y * u ^ 5) ^ 4 / 384
    = 2 / 3 * u ^ 2 + 2 / 9 * u ^ 4 + u ^ 6 * (-u^14*y^4/384 - u^12*y^3/36 - u^10*y^3/24 - u^10*y^2/9 - u^8*y^2/3 - 16*u^8*y/81 - u^6*y^2/4 - 8*u^6*y/9 - 32*u^6/243 + u^4*y^2/24 - 4*u^4*y/3 - 64*u^4/81 - 4*u^2*y/9 - 16*u^2/9 + y/3 - 40/27) := by
  ring

theorem muenster_check (u y : ℝ) :
    -(-2 * u ^ 2 + 38 / 3 * u ^ 4 + y * u ^ 6) + (-2 * u ^ 2 + 38 / 3 * u ^ 4 + y * u ^ 6) ^ 2 / 2
    = 2 * u ^ 2 - 32 / 3 * u ^ 4 + u ^ 6 * (u^6*y^2/2 + 38*u^4*y/3 - 2*u^2*y + 722*u^2/9 - y - 76/3) := by
  ring

/-- The `x` of the bracket at order `u⁴`: `3 (2/3 u² + 2/9 u⁴) - 4u² + 12u⁴ = -2u² + 38/3 u⁴`. -/
theorem x_in_u (u : ℝ) : 3 * (2 / 3 * u ^ 2 + 2 / 9 * u ^ 4) - 4 * u ^ 2 + 12 * u ^ 4
    = -2 * u ^ 2 + 38 / 3 * u ^ 4 := by
  ring

theorem sixj_racah : ((-1 : ℚ) ^ 3 * 24 / 72 = -1 / 3) ∧
    ((1 : ℚ) / 24 * (1 / 6) ^ 3 = (1 / 72) ^ 2) := by
  norm_num

theorem sixj_amplitude : (3 : ℚ) * 3 * 2 * 3 * (-1 / 3) ^ 2 = 6 := by
  norm_num

theorem sixj_count (T : ℕ) : 24 * T ^ 3 * 4 * 3 * T * 2 = 576 * T ^ 4 := by
  ring

/-- The leading coefficient of the 2I excess: with `a_j ≈ (β/2)^2j/(2j+1)!` and
`a_0.5 ≈ β/4`, `(24 a_5.5 + 11 a_0.5 a_5)/a_0.5 = β¹⁰/2724986880`. -/
theorem design_excess :
    (24 * ((1 : ℚ) / 2) ^ 11 / 479001600 + 11 * (1 / 4) * (1 / 2) ^ 10 / 39916800) / (1 / 4)
      = 1 / 2724986880 := by
  norm_num

theorem chebU_sum_1 : classSum 1 (Real.sqrt 5) = 0 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [classSum, chebU]
  linear_combination (0) * hs

theorem chebU_sum_2 : classSum 2 (Real.sqrt 5) = 0 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [classSum, chebU]
  linear_combination (12) * hs

theorem chebU_sum_3 : classSum 3 (Real.sqrt 5) = 0 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [classSum, chebU]
  linear_combination (0) * hs

theorem chebU_sum_4 : classSum 4 (Real.sqrt 5) = 0 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [classSum, chebU]
  linear_combination (3*Real.sqrt 5^2 - 3) * hs

theorem chebU_sum_5 : classSum 5 (Real.sqrt 5) = 0 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [classSum, chebU]
  linear_combination (0) * hs

theorem chebU_sum_6 : classSum 6 (Real.sqrt 5) = 0 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [classSum, chebU]
  linear_combination (3*Real.sqrt 5^4/4 - 27/4) * hs

theorem chebU_sum_7 : classSum 7 (Real.sqrt 5) = 0 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [classSum, chebU]
  linear_combination (0) * hs

theorem chebU_sum_8 : classSum 8 (Real.sqrt 5) = 0 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [classSum, chebU]
  linear_combination (3*Real.sqrt 5^6/16 + 15*Real.sqrt 5^4/16 - 255*Real.sqrt 5^2/16 - 51/16) * hs

theorem chebU_sum_9 : classSum 9 (Real.sqrt 5) = 0 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [classSum, chebU]
  linear_combination (0) * hs

theorem chebU_sum_10 : classSum 10 (Real.sqrt 5) = 0 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [classSum, chebU]
  linear_combination (3*Real.sqrt 5^8/64 + 21*Real.sqrt 5^6/32 - 105*Real.sqrt 5^4/8 + 1155*Real.sqrt 5^2/32 + 21/64) * hs

theorem chebU_sum_11 : classSum 11 (Real.sqrt 5) = 0 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [classSum, chebU]
  linear_combination (0) * hs

theorem chebU_sum_12 : classSum 12 (Real.sqrt 5) = 120 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [classSum, chebU]
  linear_combination (3*Real.sqrt 5^10/256 + 81*Real.sqrt 5^8/256 - 945*Real.sqrt 5^6/128 + 4977*Real.sqrt 5^4/128 - 13425*Real.sqrt 5^2/256 + 3741/256) * hs

end YangMills.DatumTerms
