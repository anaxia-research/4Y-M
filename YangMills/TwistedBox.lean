/-
  TwistedBox: the algebra and arithmetic of Proposition ly:prop:fixedtwist
  (twisted boxes at weak coupling) and of Lemma ly:lem:s4int (its normalisation).
  * the anticommutator of two unit quaternions: |h1 h2 + h2 h1|^2 = 4 e,
    e = x1^2 + x2^2 - x1^2 x2^2 + p^2;
  * the splitting identity eps h x g - x g h = (eps h x - x h) g + x (h g - g h), and the
    defects eps h_i x_k - x_k h_i and x_3 x_4 - sigma x_4 x_3 as multiples of h1 h2 + h2 h1;
  * the signs of the words x = i^a j^b against i, j and against each other;
  * the decomposition of the Pf = 1 case;
  * the elementary inequalities of the proof (Gram eigenvalue, the bounds on e);
  * the constants 37.49, 11, 4096/(9 pi^8), 1/18, and the tail at t = 64;
  * the normalisation 6 sqrt 2 * 4 sqrt 2 pi^2 = 48 pi^2 of Lemma ly:lem:s4int.
-/
import Mathlib

noncomputable section

namespace YangMills.TwistedBox

open Real

/-- Components of the anticommutator of two quaternions. -/
theorem anticomm_comp (a b : Quaternion ℝ) :
    (a * b + b * a).re = 2 * (a.re * b.re - (a.imI * b.imI + a.imJ * b.imJ + a.imK * b.imK)) ∧
    (a * b + b * a).imI = 2 * (a.re * b.imI + b.re * a.imI) ∧
    (a * b + b * a).imJ = 2 * (a.re * b.imJ + b.re * a.imJ) ∧
    (a * b + b * a).imK = 2 * (a.re * b.imK + b.re * a.imK) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul] <;> ring

/-- `|h1 h2 + h2 h1|^2 = 4 (x1^2 + x2^2 - x1^2 x2^2 + p^2)` for unit quaternions. -/
theorem anticomm_normSq (a b : Quaternion ℝ) (ha : Quaternion.normSq a = 1)
    (hb : Quaternion.normSq b = 1) :
    Quaternion.normSq (a * b + b * a) =
      4 * (a.re ^ 2 + b.re ^ 2 - a.re ^ 2 * b.re ^ 2 +
        (a.imI * b.imI + a.imJ * b.imJ + a.imK * b.imK) ^ 2) := by
  rw [Quaternion.normSq_def'] at ha hb ⊢
  obtain ⟨h0, h1, h2, h3⟩ := anticomm_comp a b
  rw [h0, h1, h2, h3]
  linear_combination 4 * a.re ^ 2 * hb + 4 * b.re ^ 2 * ha

/-- The splitting identity, `eps = 1`. -/
theorem split_pos {R : Type*} [Ring R] (h x g : R) :
    h * (x * g) - x * g * h = (h * x - x * h) * g + x * (h * g - g * h) := by noncomm_ring

/-- The splitting identity, `eps = -1`. -/
theorem split_neg {R : Type*} [Ring R] (h x g : R) :
    -(h * (x * g)) - x * g * h = (-(h * x) - x * h) * g + x * (h * g - g * h) := by noncomm_ring

/-- The defects `eps h_i x_k - x_k h_i` in the four nonzero cases. -/
theorem defects {R : Type*} [Ring R] (h1 h2 : R) :
    (-(h1 * h2) - h2 * h1 = -(h1 * h2 + h2 * h1)) ∧
    (-(h2 * h1) - h1 * h2 = -(h1 * h2 + h2 * h1)) ∧
    (-(h1 * (h1 * h2)) - h1 * h2 * h1 = -(h1 * (h1 * h2 + h2 * h1))) ∧
    (-(h2 * (h1 * h2)) - h1 * h2 * h2 = -((h1 * h2 + h2 * h1) * h2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

/-- The defects `x_3 x_4 - sigma x_4 x_3` (`sigma = -1`) in the nonzero cases. -/
theorem pair_defects {R : Type*} [Ring R] (h1 h2 : R) :
    (h1 * h2 + h2 * h1 = h1 * h2 + h2 * h1) ∧
    (h1 * (h1 * h2) + h1 * h2 * h1 = h1 * (h1 * h2 + h2 * h1)) ∧
    (h2 * (h1 * h2) + h1 * h2 * h2 = (h1 * h2 + h2 * h1) * h2) ∧
    (h1 * h2 * h1 + h1 * (h1 * h2) = h1 * (h1 * h2 + h2 * h1)) ∧
    (h1 * h2 * h2 + h2 * (h1 * h2) = (h1 * h2 + h2 * h1) * h2) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> noncomm_ring

/-- The case `Pf = 1`: `eps sigma = -1` gives `eps x3 x4 - x4 x3 = eps (x3 x4 - sigma x4 x3) - 2 x4 x3`. -/
theorem pf_one_split {R : Type*} [Ring R] (x3 x4 : R) :
    (x3 * x4 - x4 * x3 = (x3 * x4 + x4 * x3) - 2 * (x4 * x3)) ∧
    (-(x3 * x4) - x4 * x3 = -(x3 * x4 - x4 * x3) - 2 * (x4 * x3)) := by
  constructor <;> noncomm_ring

/-- The quaternion units used for the words `x = i^a j^b`. -/
def qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
def qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
@[simp] theorem qi_re : qi.re = 0 := rfl
@[simp] theorem qi_imI : qi.imI = 1 := rfl
@[simp] theorem qi_imJ : qi.imJ = 0 := rfl
@[simp] theorem qi_imK : qi.imK = 0 := rfl
@[simp] theorem qj_re : qj.re = 0 := rfl
@[simp] theorem qj_imI : qj.imI = 0 := rfl
@[simp] theorem qj_imJ : qj.imJ = 1 := rfl
@[simp] theorem qj_imK : qj.imK = 0 := rfl
def word (a b : Bool) : Quaternion ℝ := (if a then qi else 1) * (if b then qj else 1)
def sgn (s : Bool) : ℝ := if s then -1 else 1

/-- The word `x = i^a j^b` satisfies `(-1)^b i x = x i` and `(-1)^a j x = x j`. -/
theorem word_signs (a b : Bool) :
    ((sgn b : ℝ) : Quaternion ℝ) * (qi * word a b) = word a b * qi ∧
    ((sgn a : ℝ) : Quaternion ℝ) * (qj * word a b) = word a b * qj := by
  cases a <;> cases b <;> constructor <;>
    ext <;> simp [word, sgn, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]

/-- Two words commute up to the sign `(-1)^(a b' + b a')`. -/
theorem word_pair (a b a' b' : Bool) :
    word a b * word a' b' =
      ((sgn (xor (a && b') (b && a')) : ℝ) : Quaternion ℝ) * (word a' b' * word a b) := by
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    ext <;> simp [word, sgn, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]

/-- With `c12 = 1`: `Pf(c) = c34 + (c13 c24 + c23 c14)` in `Z/2`. -/
theorem pf_reduce (c13 c14 c23 c24 c34 : ZMod 2) :
    1 * c34 + c13 * c24 + c14 * c23 = c34 + (c13 * c24 + c23 * c14) := by ring

/-- `(u - v)^2 >= u^2/2 - v^2`. -/
theorem half_sq (u v : ℝ) : u ^ 2 / 2 - v ^ 2 ≤ (u - v) ^ 2 := by nlinarith [sq_nonneg (u - 2 * v)]

/-- `u^2 + v^2 >= (u + v)^2 / 2`. -/
theorem sum_sq (u v : ℝ) : (u + v) ^ 2 / 2 ≤ u ^ 2 + v ^ 2 := by nlinarith [sq_nonneg (u - v)]

/-- The discriminant bound for the smallest eigenvalue of a 2x2 Gram matrix. -/
theorem disc_le (d p : ℝ) : Real.sqrt (d ^ 2 + 4 * p ^ 2) ≤ |d| + 2 * |p| := by
  rw [Real.sqrt_le_left]
  · nlinarith [abs_nonneg d, abs_nonneg p, sq_abs d, sq_abs p, mul_nonneg (abs_nonneg d) (abs_nonneg p)]
  · positivity

/-- The smallest eigenvalue `m` of the Gram matrix of `a1, a2` (`|a_i|^2 = 1 - x_i^2`,
`<a1,a2> = p`) is at least `1 - max(x1^2, x2^2) - |p|`. -/
theorem gram_min (x1 x2 p : ℝ) :
    1 - max (x1 ^ 2) (x2 ^ 2) - |p| ≤
      ((2 - x1 ^ 2 - x2 ^ 2) - Real.sqrt ((x2 ^ 2 - x1 ^ 2) ^ 2 + 4 * p ^ 2)) / 2 := by
  have h := disc_le (x2 ^ 2 - x1 ^ 2) p
  rcases le_total (x1 ^ 2) (x2 ^ 2) with hle | hle
  · rw [max_eq_right hle]
    rw [abs_of_nonneg (sub_nonneg.2 hle)] at h
    linarith
  · rw [max_eq_left hle]
    rw [abs_of_nonpos (sub_nonpos.2 hle)] at h
    linarith

/-- `x1^2, x2^2, p^2 <= e`, with `e = x1^2 + x2^2 - x1^2 x2^2 + p^2` and `x1^2, x2^2 <= 1`. -/
theorem e_bounds (x1 x2 p : ℝ) (h1 : x1 ^ 2 ≤ 1) (h2 : x2 ^ 2 ≤ 1) :
    x1 ^ 2 ≤ x1 ^ 2 + x2 ^ 2 - x1 ^ 2 * x2 ^ 2 + p ^ 2 ∧
    x2 ^ 2 ≤ x1 ^ 2 + x2 ^ 2 - x1 ^ 2 * x2 ^ 2 + p ^ 2 ∧
    p ^ 2 ≤ x1 ^ 2 + x2 ^ 2 - x1 ^ 2 * x2 ^ 2 + p ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    nlinarith [sq_nonneg x1, sq_nonneg x2, sq_nonneg p, mul_nonneg (sq_nonneg x1) (sub_nonneg.2 h2),
      mul_nonneg (sq_nonneg x2) (sub_nonneg.2 h1)]

/-- For `x_i^2 <= 1/9`: `x1^2 x2^2 <= (x1^2 + x2^2)/18`, so `e >= (17/18)(x1^2 + x2^2) + p^2`. -/
theorem e_lower (x1 x2 p : ℝ) (h1 : x1 ^ 2 ≤ 1 / 9) (h2 : x2 ^ 2 ≤ 1 / 9) :
    17 / 18 * (x1 ^ 2 + x2 ^ 2) + p ^ 2 ≤ x1 ^ 2 + x2 ^ 2 - x1 ^ 2 * x2 ^ 2 + p ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg x1) (sub_nonneg.2 h2), mul_nonneg (sq_nonneg x2) (sub_nonneg.2 h1)]

/-- On the region `|x_i|, |p| <= eta`: `e <= 3 eta^2`. -/
theorem e_region (x1 x2 p η : ℝ) (h1 : x1 ^ 2 ≤ η ^ 2) (h2 : x2 ^ 2 ≤ η ^ 2) (hp : p ^ 2 ≤ η ^ 2) :
    x1 ^ 2 + x2 ^ 2 - x1 ^ 2 * x2 ^ 2 + p ^ 2 ≤ 3 * η ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg x1) (sq_nonneg x2)]

/-- `m0 = 1 - 1/9 - sqrt(1/9) = 5/9`. -/
theorem m0_value : 1 - (1 : ℝ) / 9 - Real.sqrt (1 / 9) = 5 / 9 := by
  have : Real.sqrt (1 / 9) = 1 / 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  rw [this]; norm_num

/-- `(18/(17 pi)) (9 sqrt pi / 32) = 81 / (272 sqrt pi)`. -/
theorem line_factor : (18 / (17 * π)) * (9 * Real.sqrt π / 32) = 81 / (272 * Real.sqrt π) := by
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.2 pi_pos
  have hsq : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt pi_pos.le
  rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination 44064 * hsq

/-- `(1/(2 sqrt 2))^2 (9/5)^3 = 729/1000`. -/
theorem phi_factor : (1 / (2 * Real.sqrt 2)) ^ 2 * (9 / 5) ^ 3 = (729 : ℝ) / 1000 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 2 := by positivity
  field_simp; rw [h2]; norm_num

/-- `sqrt pi < 1.7725`. -/
theorem sqrt_pi_lt : Real.sqrt π < 1.7725 := by
  rw [Real.sqrt_lt' (by norm_num)]
  have := pi_lt_d4; nlinarith

/-- The constant of part (b): `(59049/272000) pi^4 sqrt pi < 37.49`. -/
theorem const_C : (59049 / 272000 : ℝ) * π ^ 4 * Real.sqrt π < 37.49 := by
  have hp : π < 3.1416 := pi_lt_d4
  have hp0 : 0 < π := pi_pos
  have hs := sqrt_pi_lt
  have hs0 : 0 ≤ Real.sqrt π := Real.sqrt_nonneg _
  have h4 : π ^ 4 < 3.1416 ^ 4 := by gcongr
  have h4' : π ^ 4 * Real.sqrt π ≤ 3.1416 ^ 4 * 1.7725 := by
    apply mul_le_mul h4.le hs.le hs0 (by positivity)
  nlinarith

/-- `59049/272000 = (81/272)(729/1000)`. -/
theorem const_C_split : (81 / 272 : ℚ) * (729 / 1000) = 59049 / 272000 := by norm_num

/-- The tail at `t = 64`: `64^(9/2) e^(-4*64/9) < 10^-4`, i.e. `2^27 < 10^-4 e^(256/9)`. -/
theorem tail_64 : (2 : ℝ) ^ 27 < Real.exp (256 / 9) / 10 ^ 4 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h28 : Real.exp 28 = Real.exp 1 ^ 28 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hmono : Real.exp 28 ≤ Real.exp (256 / 9) := Real.exp_le_exp.2 (by norm_num)
  have hpow : (2.7182818283 : ℝ) ^ 28 < Real.exp 1 ^ 28 := by gcongr
  rw [lt_div_iff₀ (by norm_num)]
  have : (2 : ℝ) ^ 27 * 10 ^ 4 < 2.7182818283 ^ 28 := by norm_num
  linarith [h28 ▸ hmono]

/-- The region: `sqrt 2 (2 sqrt 3 + 4 + 2/32) <= 11`. -/
theorem region_const : Real.sqrt 2 * (2 * Real.sqrt 3 + 4 + 2 / 32) ≤ 11 := by
  have h2 : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3 : Real.sqrt 3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h30 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  nlinarith

/-- The measure of the region: `(4/pi)^2 (16/(3 pi^3))^2 = 4096/(9 pi^8)`. -/
theorem measure_const : (4 / π) ^ 2 * (16 / (3 * π ^ 3)) ^ 2 = 4096 / (9 * π ^ 8) := by
  have : π ≠ 0 := pi_ne_zero
  field_simp; ring

/-- The three numbers of part (c), with `e1 = 1/128`, `beta1 = 8/25`, are at least `1/18`. -/
theorem delta_cases :
    (1 : ℝ) / 18 ≤ 8 * (1 / 128) ∧
    (1 : ℝ) / 18 ≤ (1 / 2) * (Real.sqrt (8 * (1 - 1 / 128 - Real.sqrt (1 / 128))) * (8 / 25) -
        2 * Real.sqrt (8 * (1 / 128))) ^ 2 ∧
    (1 : ℝ) / 18 ≤ 2 * ((1 - 2 * (8 / 25) ^ 2) * (2 - 2 * Real.sqrt (1 / 128)) - 4 * (8 / 25)) ^ 2 := by
  have hq : Real.sqrt (1 / 128) < 0.088389 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hq0 : 0 ≤ Real.sqrt (1 / 128) := Real.sqrt_nonneg _
  have h14 : Real.sqrt (8 * (1 / 128)) = 1 / 4 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  refine ⟨by norm_num, ?_, ?_⟩
  · have hm : (2.6889 : ℝ) ≤ Real.sqrt (8 * (1 - 1 / 128 - Real.sqrt (1 / 128))) := by
      rw [Real.le_sqrt (by norm_num)] <;> nlinarith
    rw [h14]
    nlinarith
  · have hb : (0.16 : ℝ) ≤ (1 - 2 * (8 / 25) ^ 2) * (2 - 2 * Real.sqrt (1 / 128)) - 4 * (8 / 25) := by
      nlinarith
    nlinarith

/-- The constant `L_0 = log(64*33) + log(pi^(5/2)/16) + (3/2) log 2` is `log(132 * 2^(3/2) * pi^(5/2))`;
here only the product of the rational factors: `64 * 33 / 16 = 132`. -/
theorem L0_rational : (64 * 33 / 16 : ℚ) = 132 := by norm_num

/-- Exponent bookkeeping: `-(9/2) + 3 = -3/2`, `(9 - 6)/2 = 3/2`, codimensions `12 - 3 = 9`. -/
theorem exponents : (-(9 : ℚ) / 2 + 3 = -3 / 2) ∧ ((9 - 6 : ℚ) / 2 = 3 / 2) ∧ (12 - 3 = (9 : ℕ)) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- The datum tori: `64 * 16 = 2^10`, so `b >= 2^10 T^4` gives `b >= 64 V_2`. -/
theorem datum_threshold (T : ℕ) : 64 * (16 * T ^ 4) = 2 ^ 10 * T ^ 4 := by ring

/-- Lemma ly:lem:s4int: `6 sqrt 2 * (2 pi^2 (sqrt 2)^3) = 48 pi^2`, so `|k(Q_p)| = 1`. -/
theorem s4_normalisation : 6 * Real.sqrt 2 * (2 * π ^ 2 * Real.sqrt 2 ^ 3) = 48 * π ^ 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have : Real.sqrt 2 ^ 4 = 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]; norm_num
  nlinarith [this]

end YangMills.TwistedBox
