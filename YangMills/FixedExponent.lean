/-
  FixedExponent: the algebra and arithmetic of Proposition ly:prop:fixedexp
  (the exponent at a fixed box).
  * the quaternion commutator: ab - ba = 2 (Im a x Im b), and the Lagrange identity
    |u x v|^2 = |u|^2 |v|^2 - <u,v>^2;
  * the count of the peeled links of the comb gauge: 3V - 3;
  * the exponent bookkeeping of parts (b)-(d);
  * the elementary steps of the bound on J for SU(2) (the angular integral, the
    split at R_0 = t^(-1/4), the arcsine step) and of the dyadic shells of the
    lower bound (the cross products on the event E_k and the value 7/(3072 pi^4));
  * the rational and log 2 steps of the constants.
-/
import Mathlib

namespace YangMills.FixedExponent

open Real

/-- The commutator of two quaternions is twice the cross product of their imaginary parts. -/
theorem quat_comm (a b : Quaternion ℝ) :
    (a * b - b * a).re = 0 ∧
    (a * b - b * a).imI = 2 * (a.imJ * b.imK - a.imK * b.imJ) ∧
    (a * b - b * a).imJ = 2 * (a.imK * b.imI - a.imI * b.imK) ∧
    (a * b - b * a).imK = 2 * (a.imI * b.imJ - a.imJ * b.imI) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul] <;> ring

/-- Lagrange's identity in three dimensions. -/
theorem lagrange3 (a1 a2 a3 b1 b2 b3 : ℝ) :
    (a2 * b3 - a3 * b2) ^ 2 + (a3 * b1 - a1 * b3) ^ 2 + (a1 * b2 - a2 * b1) ^ 2 =
      (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * (b1 ^ 2 + b2 ^ 2 + b3 ^ 2) - (a1 * b1 + a2 * b2 + a3 * b3) ^ 2 := by
  ring

/-- The peeled links of the comb gauge: at level `k` there are `(4-k)(L_k-1)|S_k|` links of the
first kind and `|S_k| - 1` of the second kind, with `|S_k| = L_{k+1} ... L_4`; the total is
`3V - 3`. -/
theorem peel_count (L1 L2 L3 L4 : ℤ) :
    (0 + (1 - 1)) + ((1 * (L3 - 1) * L4) + (L4 - 1)) + ((2 * (L2 - 1) * (L3 * L4)) + (L3 * L4 - 1)) +
      ((3 * (L1 - 1) * (L2 * L3 * L4)) + (L2 * L3 * L4 - 1)) = 3 * (L1 * L2 * L3 * L4) - 3 := by
  ring

/-- Together with the four axis links and the spanning tree: `(V - 1) + 4 + (3V - 3) = 4V`. -/
theorem link_total (V : ℤ) : (V - 1) + 4 + (3 * V - 3) = 4 * V := by ring

/-- Exponents: upper bound with `J = O(t^-e)`: `(3d/2) V - (d/2)(3V-3) - e`. -/
theorem exponent_upper (d V e : ℚ) : 3 * d / 2 * V - d / 2 * (3 * V - 3) - e = 3 * d / 2 - e := by
  ring

theorem exponent_su2 : (3 * 3 / 2 : ℚ) - 3 = 3 / 2 := by norm_num

theorem exponent_general (d : ℚ) : 3 * d / 2 - d = d / 2 := by ring

/-- Lower bound for SU(2): `(9/2) V`-terms cancel, `(9/2) - 3 = 3/2`. -/
theorem exponent_lower (V : ℚ) : 9 / 2 * V - 3 / 2 * (3 * V - 3) - 3 = 3 / 2 := by ring

/-- The angular integral: `1 - u^2 >= 1 - u` on `[0,1]`. -/
theorem angular_step (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) : 1 - u ≤ 1 - u ^ 2 := by nlinarith

/-- The split point `R_0 = t^(-1/4)`: if `R_0^4 t = 1` then `R_0^12 = t^-3`. -/
theorem split_point (R0 t : ℝ) (ht : 0 < t) (h : R0 ^ 4 * t = 1) : R0 ^ 12 = (t ^ 3)⁻¹ := by
  have h3 : R0 ^ 12 * t ^ 3 = 1 := by
    have : R0 ^ 12 * t ^ 3 = (R0 ^ 4 * t) ^ 3 := by ring
    rw [this, h]; norm_num
  field_simp
  linarith

/-- The constant of the inner part: `4 * a * b^3 / 12 = (1/3) a b^3`. -/
theorem inner_constant (a b : ℝ) : 4 * a * b ^ 3 / 12 = 1 / 3 * a * b ^ 3 := by ring

/-- The arcsine step: if `s <= (pi/2) R` then `s / (2 pi t R^2) <= 1 / (4 t R)`. -/
theorem arcsin_step (s R t : ℝ) (hR : 0 < R) (ht : 0 < t) (hs : s ≤ π / 2 * R) :
    s / (2 * π * t * R ^ 2) ≤ 1 / (4 * t * R) := by
  have hpi : 0 < π := pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hpi (mul_pos ht hR)]

/-- The outer part: `4 (4/pi) / (64 t^3) = 1 / (4 pi t^3)`. -/
theorem outer_constant (t : ℝ) (ht : 0 < t) :
    4 * (4 / π) / (64 * t ^ 3) = 1 / (4 * π * t ^ 3) := by
  have hpi : 0 < π := pi_pos
  field_simp
  ring

/-- On the event `E_k`: with `eta = delta/(8X)` and `X^2 >= delta`, `2 X eta = delta/4` and
`4 X eta + eta^2 <= delta`. -/
theorem shell_cross (X δ : ℝ) (hX : 0 < X) (hδ : 0 < δ) (hXδ : δ ≤ X ^ 2) :
    2 * X * (δ / (8 * X)) = δ / 4 ∧ 4 * X * (δ / (8 * X)) + (δ / (8 * X)) ^ 2 ≤ δ := by
  constructor
  · field_simp; ring
  · have e1 : 4 * X * (δ / (8 * X)) = δ / 2 := by field_simp; ring
    have e2 : (δ / (8 * X)) ^ 2 = δ ^ 2 / (64 * X ^ 2) := by field_simp; ring
    rw [e1, e2]
    have : δ ^ 2 / (64 * X ^ 2) ≤ δ / 64 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith

/-- The probability of `E_k`: `(28 X^3/(3 pi)) (4 X eta^2/pi)^3 = 7 delta^6/(3072 pi^4)`. -/
theorem shell_value (X δ : ℝ) (hX : 0 < X) :
    28 * X ^ 3 / (3 * π) * (4 * X * (δ / (8 * X)) ^ 2 / π) ^ 3 = 7 * δ ^ 6 / (3072 * π ^ 4) := by
  have hpi : 0 < π := pi_pos
  field_simp
  ring

/-- The number of shells: for `y = log_2 c >= 10`, `(y - 5)/4 >= y/8`. -/
theorem shell_count (y : ℝ) (hy : 10 ≤ y) : y / 8 ≤ (y - 5) / 4 := by linarith

/-- The plaquette budget of the lower bound: `4 rho + c^(-1/2) = 2 c^(-1/2)` for `rho = 1/(4 s)`,
and `(c/2)(2/s)^2 = 2` with `s^2 = c`. -/
theorem budget (s : ℝ) (hs : 0 < s) : 4 * (1 / (4 * s)) + 1 / s = 2 / s ∧ s ^ 2 / 2 * (2 / s) ^ 2 = 2 := by
  constructor
  · field_simp; norm_num
  · field_simp

/-- `1/(16 pi) < 0.1129`, used in `0.1129 + x/(16 pi) <= 0.1129 (1 + x)`. -/
theorem sixteen_pi : 1 / (16 * π) < 1129 / 10000 := by
  have := pi_gt_three
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem log_step (x : ℝ) (hx : 0 ≤ x) : 1129 / 10000 + x / (16 * π) ≤ 1129 / 10000 * (1 + x) := by
  have h := sixteen_pi
  have hpi : 0 < π := pi_pos
  have : x / (16 * π) = x * (1 / (16 * π)) := by ring
  rw [this]
  nlinarith

/-- The constant of the upper bound for SU(2): `K_G < 35.234` gives
`K_G + (9/2) log 2 + 3 < 41.4`. -/
theorem su2_upper_constant (K : ℝ) (hK : K < 35234 / 1000) : K + 9 / 2 * log 2 + 3 < 414 / 10 := by
  have := log_two_lt_d9
  linarith

/-- The constant of the upper bound for U(1): `K' < 9.192` gives `K' + (3/2) log 2 < 10.24`. -/
theorem u1_upper_constant (K : ℝ) (hK : K < 9192 / 1000) : K + 3 / 2 * log 2 < 1024 / 100 := by
  have := log_two_lt_d9
  linarith

/-- `C_G = pi^(5/2)/16 > 1` for SU(2): `pi^2 sqrt pi > 16`. -/
theorem su2_CG_gt_one : 16 < π ^ 2 * Real.sqrt π := by
  have hp : (3.14 : ℝ) < π := pi_gt_d2
  have hs : (1.77 : ℝ) < Real.sqrt π := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  have h2 : (3.14 : ℝ) ^ 2 < π ^ 2 := by nlinarith
  nlinarith [Real.sqrt_nonneg π]

end YangMills.FixedExponent
