import Mathlib

/-!
# One-cube criteria: transcendental constants proved directly

The exponential and logarithmic inequalities behind L3 and J1–J12 that are proved here
from Mathlib's `Real.exp` / `Real.log`, without numerical input other than rational
arithmetic checked by `norm_num`.

Method: for `0 ≤ x ≤ 1`, `Real.exp_bound'` (Taylor polynomial of degree 11 with a
remainder term) and `Real.sum_le_exp_of_nonneg` give rational upper and lower bounds
`eU x` and `eL x`; for larger arguments `exp a = exp (a/k)^k`. The intermediate
rational `c` in `exp a ≤ c^k` (resp. `c^k ≤ exp a`) is a short decimal and is
checked against `eU (a/k)` (resp. `eL (a/k)`) by `norm_num`. `log 2` and `π` enter
through `Real.log_two_near_10`, `Real.pi_gt_d20` and `Real.pi_lt_d20`.
-/

namespace YangMills.OneCube.Transcendental

open Real Finset

/-- Taylor upper bound for `exp` on `[0, 1]`. -/
noncomputable def eU (x : ℝ) : ℝ :=
  ∑ m ∈ range 12, x ^ m / m.factorial + x ^ 12 * (12 + 1) / ((Nat.factorial 12 : ℝ) * 12)

/-- Taylor lower bound for `exp` on `[0, ∞)`. -/
noncomputable def eL (x : ℝ) : ℝ := ∑ m ∈ range 12, x ^ m / m.factorial

theorem exp_le_eU {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : exp x ≤ eU x := by
  have := Real.exp_bound' h0 h1 (n := 12) (by norm_num)
  simpa [eU] using this

theorem exp_le_pow {a c : ℝ} (k : ℕ) (hk : 0 < k) (h0 : 0 ≤ a / k) (h1 : a / k ≤ 1)
    (hc : eU (a / k) ≤ c) : exp a ≤ c ^ k := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have : exp a = exp (a / k) ^ k := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [this]
  exact pow_le_pow_left₀ (exp_pos _).le ((exp_le_eU h0 h1).trans hc) k

theorem pow_le_exp {a c : ℝ} (k : ℕ) (hk : 0 < k) (h0 : 0 ≤ a / k) (hc0 : 0 ≤ c)
    (hc : c ≤ eL (a / k)) : c ^ k ≤ exp a := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have : exp a = exp (a / k) ^ k := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [this]
  exact pow_le_pow_left₀ hc0 (hc.trans (Real.sum_le_exp_of_nonneg h0 12)) k

/-- `exp a ≤ c ^ k`, all side conditions by `norm_num`. -/
macro "exp_up " k:term:max c:term:max : term =>
  `(exp_le_pow $k (c := $c) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [eU, Finset.sum_range_succ, Nat.factorial]))

/-- `c ^ k ≤ exp a`, all side conditions by `norm_num`. -/
macro "exp_dn " k:term:max c:term:max : term =>
  `(pow_le_exp $k (c := $c) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [eL, Finset.sum_range_succ, Nat.factorial]))

/-- `exp t ≤ 1/(1-t)` for `0 ≤ t < 1`. -/
theorem exp_le_inv_one_sub {t : ℝ} (h1 : t < 1) : exp t ≤ 1 / (1 - t) := by
  have h := add_one_le_exp (-t)
  rw [exp_neg] at h
  have hp := exp_pos t
  rw [le_div_iff₀ (by linarith)]
  calc exp t * (1 - t) ≤ exp t * (exp t)⁻¹ := by gcongr; linarith
    _ = 1 := mul_inv_cancel₀ hp.ne'

/-- `e^t - 1 ≤ t/(1-t)` for `t < 1`. -/
theorem expm1_le {t : ℝ} (h1 : t < 1) : exp t - 1 ≤ t / (1 - t) := by
  have h := exp_le_inv_one_sub h1
  have : 1 / (1 - t) - 1 = t / (1 - t) := by field_simp [show (1 - t) ≠ 0 by linarith]; ring
  linarith

theorem lt_neg_log {y c : ℝ} (hy : 0 < y) (h : y * exp c < 1) : c < -log y := by
  rw [lt_neg, log_lt_iff_lt_exp hy, exp_neg]
  have hp := exp_pos c
  calc y = y * exp c * (exp c)⁻¹ := by field_simp
    _ < 1 * (exp c)⁻¹ := by gcongr
    _ = _ := one_mul _

theorem le_neg_log {y c : ℝ} (hy : 0 < y) (h : y * exp c ≤ 1) : c ≤ -log y := by
  rw [le_neg, log_le_iff_le_exp hy, exp_neg]
  have hp := exp_pos c
  calc y = y * exp c * (exp c)⁻¹ := by field_simp
    _ ≤ 1 * (exp c)⁻¹ := by gcongr
    _ = _ := one_mul _

theorem neg_log_lt {y c : ℝ} (hy : 0 < y) (h : 1 < y * exp c) : -log y < c := by
  rw [neg_lt, lt_log_iff_exp_lt hy, exp_neg]
  have hp := exp_pos c
  calc (exp c)⁻¹ = 1 * (exp c)⁻¹ := (one_mul _).symm
    _ < y * exp c * (exp c)⁻¹ := by gcongr
    _ = y := by field_simp

/-- `log 2` to ten digits. -/
theorem log_two_bounds : 0.6931471804 < log 2 ∧ log 2 < 0.6931471807 := by
  have h := abs_sub_le_iff.1 Real.log_two_near_10
  constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]

/-! ## L3 -/

/-- **L3** (log part): `-log(1 - 1/16385) ≤ 2⁻¹⁴`. -/
theorem L3_log : -log (1 - 1 / 16385) ≤ 1 / 2 ^ 14 := by
  rw [← log_inv]
  have := log_le_sub_one_of_pos (x := (1 - 1 / 16385 : ℝ)⁻¹) (by norm_num)
  norm_num at this ⊢; linarith

/-- **L3** (exp part): `1 - e^{-2⁻¹³} ≤ 2⁻¹³`. -/
theorem L3_exp : 1 - exp (-(1 / 2 ^ 13)) ≤ 1 / 2 ^ 13 := by
  have := add_one_le_exp (-(1 / 2 ^ 13 : ℝ)); linarith

/-! ## J1: the fixed point of `f(x) = (e^{64x} - 1)^2` -/

/-- The ascent map. -/
noncomputable def f (x : ℝ) : ℝ := (exp (64 * x) - 1) ^ 2

theorem J1_upper : 4160 * f (1 / 4160) < 0.99991 := by
  have h : exp (64 * (1 / 4160) : ℝ) ≤ (1.0155035678094484 : ℝ) ^ 1 := (exp_up 1 (1.0155035678094484 : ℝ))
  have h0 : (1 : ℝ) ≤ exp (64 * (1 / 4160)) := one_le_exp (by norm_num)
  have : (exp (64 * (1 / 4160) : ℝ) - 1) ^ 2 ≤ ((1.0155035678094484 : ℝ) ^ 1 - 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  unfold f; norm_num at this ⊢; linarith

theorem J1_lower : 1.00014 < 4159 * f (1 / 4159) := by
  have h : (1.0155073242799240 : ℝ) ^ 1 ≤ exp (64 * (1 / 4159) : ℝ) := (exp_dn 1 (1.0155073242799240 : ℝ))
  have : ((1.0155073242799240 : ℝ) ^ 1 - 1) ^ 2 ≤ (exp (64 * (1 / 4159) : ℝ) - 1) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 2
  unfold f; norm_num at this ⊢; linarith

theorem J1_exp : exp (1 / 4159 : ℝ) < 2 := ((exp_up 1 (1.0002404713226360 : ℝ))).trans_lt (by norm_num)

/-- **J1.** The fixed point `x_* = f(x_*)` exists in `(1/4160, 1/4159)`. -/
theorem J1 : ∃ x ∈ Set.Ioo (1 / 4160 : ℝ) (1 / 4159), f x = x := by
  have hc : ContinuousOn (fun x => f x - x) (Set.Icc (1 / 4160 : ℝ) (1 / 4159)) := by
    unfold f; fun_prop
  have h1 := J1_upper
  have h2 := J1_lower
  have hmem : (0 : ℝ) ∈ Set.Ioo ((fun x => f x - x) (1 / 4160)) ((fun x => f x - x) (1 / 4159)) := by
    simp only [Set.mem_Ioo]; constructor <;> linarith
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo (by norm_num) hc hmem
  exact ⟨x, hx, by simp only at hx0; linarith⟩

/-! ## J2: the ascent constants -/

/-- The iterates `x₀ = 2⁻¹³`, `x_{i+1} = f(x_i)`. -/
noncomputable def xs : ℕ → ℝ
  | 0 => 1 / 8192
  | i + 1 => f (xs i)

theorem xs_nonneg (i : ℕ) : 0 ≤ xs i := by
  cases i with
  | zero => norm_num [xs]
  | succ i => exact sq_nonneg _

theorem expm1_le_mul {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 127) : exp t - 1 ≤ 127 / 126 * t := by
  have h := expm1_le (t := t) (by linarith)
  have : t / (1 - t) ≤ 127 / 126 * t := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- **J2.** `v_i = e^{64 x_i} - 1 ≤ θ⁻¹ u^{2^i}/64` for every `i`, with `u = 32/63`,
`θ = 127/126`. -/
theorem J2 (i : ℕ) : exp (64 * xs i) - 1 ≤ 126 / 127 * (32 / 63) ^ (2 ^ i) / 64 := by
  induction i with
  | zero =>
    have h : exp (64 * (1 / 8192) : ℝ) ≤ (1.0078430972064480 : ℝ) ^ 1 := (exp_up 1 (1.0078430972064480 : ℝ))
    simp only [xs, pow_zero, pow_one]; norm_num at h ⊢; linarith
  | succ i ih =>
    have hv0 : 0 ≤ exp (64 * xs i) - 1 := by
      have := one_le_exp (by linarith [xs_nonneg i] : 0 ≤ 64 * xs i); linarith
    set a := 126 / 127 * (32 / 63 : ℝ) ^ (2 ^ (i + 1)) / 64 with ha
    have hu : (32 / 63 : ℝ) ^ (2 ^ (i + 1)) ≤ 32 / 63 :=
      pow_le_of_le_one (by norm_num) (by norm_num) (by positivity)
    have hsq : 64 * (126 / 127 * (32 / 63 : ℝ) ^ (2 ^ i) / 64) ^ 2 = 126 / 127 * a := by
      rw [ha, pow_succ 2 i, pow_mul]; ring
    have hx : 64 * xs (i + 1) ≤ 126 / 127 * a := by
      rw [← hsq]; simp only [xs, f]
      have := pow_le_pow_left₀ hv0 ih 2
      linarith
    have ha0 : 0 ≤ a := by positivity
    have hm := expm1_le_mul (t := 126 / 127 * a) (by positivity) (by rw [ha]; nlinarith)
    have hmono := exp_le_exp.2 hx
    linarith

/-- The form `v_i ≤ u^{2^i}/64`. -/
theorem J2_plan (i : ℕ) : exp (64 * xs i) - 1 ≤ (32 / 63) ^ (2 ^ i) / 64 := by
  have := J2 i
  have : 0 ≤ (32 / 63 : ℝ) ^ (2 ^ i) := by positivity
  linarith

theorem J2_log : 0.67725 < log (63 / 32) :=
  (lt_log_iff_exp_lt (by norm_num)).2 (((exp_up 1 (1.9684570253554978 : ℝ))).trans_lt (by norm_num))

theorem J2_exp : exp (0.677 : ℝ) < 63 / 32 := ((exp_up 1 (1.9679649726083132 : ℝ))).trans_lt (by norm_num)

/-- `u^n ≤ e^{-0.67725 n}`: the doubly exponential decay of `J2`. -/
theorem J2_decay (n : ℕ) : (32 / 63 : ℝ) ^ n ≤ exp (-0.67725 * n) := by
  have h : exp (0.67725 : ℝ) ≤ (1.9684570253554978 : ℝ) ^ 1 := (exp_up 1 (1.9684570253554978 : ℝ))
  have h1 : (32 / 63 : ℝ) ≤ exp (-0.67725) := by
    rw [exp_neg, le_inv_comm₀ (by norm_num) (exp_pos _)]; norm_num at h ⊢; linarith
  rw [mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) h1 n

/-! ## J3: the starting scale -/

theorem J3_log2 : 9.0109 < 13 * log 2 ∧ 13 * log 2 < 9.011 ∧ 9.70406052 < 14 * log 2 ∧
    14 * log 2 < 9.70406053 ∧ 9.0107 < 13 * log 2 - 1 / 8192 := by
  obtain ⟨h1, h2⟩ := log_two_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num at h1 h2 ⊢ <;> linarith

theorem J3_t1 : 9.0108 < -log (exp (1 / 8192) - 1) ∧ -log (exp (1 / 8192) - 1) < 9.01086 := by
  have hy : (0 : ℝ) < exp (1 / 8192) - 1 := by
    have := add_one_lt_exp (x := (1 / 8192 : ℝ)) (by norm_num); linarith
  have u1 : exp (1 / 8192 : ℝ) ≤ (1.0001220777633838 : ℝ) ^ 1 := (exp_up 1 (1.0001220777633838 : ℝ))
  have l1 : (1.0001220777633837 : ℝ) ^ 1 ≤ exp (1 / 8192 : ℝ) := (exp_dn 1 (1.0001220777633837 : ℝ))
  have u2 : exp (9.0108 : ℝ) ≤ (1.7562397187671925 : ℝ) ^ 16 := (exp_up 16 (1.7562397187671925 : ℝ))
  have l2 : (1.7562463046761839 : ℝ) ^ 16 ≤ exp (9.01086 : ℝ) := (exp_dn 16 (1.7562463046761839 : ℝ))
  constructor
  · apply lt_neg_log hy
    calc (exp (1 / 8192) - 1) * exp 9.0108 ≤ ((1.0001220777633838 : ℝ) ^ 1 - 1) * (1.7562397187671925 : ℝ) ^ 16 :=
          mul_le_mul (by linarith) u2 (exp_pos _).le (by norm_num)
      _ < 1 := by norm_num
  · apply neg_log_lt hy
    calc (1 : ℝ) < ((1.0001220777633837 : ℝ) ^ 1 - 1) * (1.7562463046761839 : ℝ) ^ 16 := by norm_num
      _ ≤ (exp (1 / 8192) - 1) * exp 9.01086 :=
          mul_le_mul (by linarith) l2 (by norm_num) hy.le

theorem J3_t1_lt : -log (exp (1 / 8192) - 1) < 13 * log 2 := by
  have h : ((2 : ℝ) ^ 13)⁻¹ < exp (1 / 8192) - 1 := by
    have := add_one_lt_exp (x := (1 / 8192 : ℝ)) (by norm_num); norm_num at this ⊢; linarith
  have := log_lt_log (by positivity) h
  rw [log_inv, log_pow] at this
  push_cast at this; linarith

theorem J3_t2 : 9.70403 < -log (exp (1 / 2 ^ 14) - 1) ∧ -log (exp (1 / 2 ^ 14) - 1) < 9.70404 := by
  have hy : (0 : ℝ) < exp (1 / 2 ^ 14) - 1 := by
    have := add_one_lt_exp (x := (1 / 2 ^ 14 : ℝ)) (by norm_num); linarith
  have u1 : exp (1 / 2 ^ 14 : ℝ) ≤ (1.0000610370189331 : ℝ) ^ 1 := (exp_up 1 (1.0000610370189331 : ℝ))
  have l1 : (1.0000610370189330 : ℝ) ^ 1 ≤ exp (1 / 2 ^ 14 : ℝ) := (exp_dn 1 (1.0000610370189330 : ℝ))
  have u2 : exp (9.70403 : ℝ) ≤ (1.8340045871438586 : ℝ) ^ 16 := (exp_up 16 (1.8340045871438586 : ℝ))
  have l2 : (1.8340057333914807 : ℝ) ^ 16 ≤ exp (9.70404 : ℝ) := (exp_dn 16 (1.8340057333914807 : ℝ))
  constructor
  · apply lt_neg_log hy
    calc (exp (1 / 2 ^ 14) - 1) * exp 9.70403 ≤ ((1.0000610370189331 : ℝ) ^ 1 - 1) * (1.8340045871438586 : ℝ) ^ 16 :=
          mul_le_mul (by linarith) u2 (exp_pos _).le (by norm_num)
      _ < 1 := by norm_num
  · apply neg_log_lt hy
    calc (1 : ℝ) < ((1.0000610370189330 : ℝ) ^ 1 - 1) * (1.8340057333914807 : ℝ) ^ 16 := by norm_num
      _ ≤ (exp (1 / 2 ^ 14) - 1) * exp 9.70404 :=
          mul_le_mul (by linarith) l2 (by norm_num) hy.le

theorem J3_expm1 : exp (1 / 8192 : ℝ) - 1 ≤ 1 / 8192 * (1 + 1 / 8192) := by
  have h : exp (1 / 8192 : ℝ) ≤ (1.0001220777633838 : ℝ) ^ 1 := (exp_up 1 (1.0001220777633838 : ℝ))
  norm_num at h ⊢; linarith

theorem J3_exps : 1 < 8192 * exp (-9.01) ∧ exp (9.0109 : ℝ) < 8191.9 ∧ 8192.7 < exp (9.011 : ℝ) ∧
    exp (9.01 : ℝ) < 8184.6 := by
  have h1 : exp (9.01 : ℝ) ≤ (1.7561519089765171 : ℝ) ^ 16 := (exp_up 16 (1.7561519089765171 : ℝ))
  refine ⟨?_, ((exp_up 16 (1.7562506952997364 : ℝ))).trans_lt (by norm_num), (by norm_num : (8192.7 : ℝ) < _).trans_le (exp_dn 16 (1.7562616718985810 : ℝ)),
    h1.trans_lt (by norm_num)⟩
  rw [exp_neg, ← div_eq_mul_inv, one_lt_div (exp_pos _)]
  exact h1.trans_lt (by norm_num)

/-! ## π, √ and `e^π` -/

theorem pi_lo : 3.1415926535 < π := by linarith [Real.pi_gt_d20]
theorem pi_hi : π < 3.1415926536 := by linarith [Real.pi_lt_d20]

theorem exp_pi_lt : exp π < 23.1406927 :=
  calc exp π < exp 3.1415926536 := exp_lt_exp.2 pi_hi
    _ ≤ (2.1932800507458367 : ℝ) ^ 4 := (exp_up 4 (2.1932800507458367 : ℝ))
    _ < 23.1406927 := by norm_num

theorem exp_neg_pi_gt : 1 / 23.1406927 < exp (-π) := by
  rw [exp_neg, one_div]; exact inv_strictAnti₀ (exp_pos _) exp_pi_lt

theorem exp_two_pi_lt : exp (2 * π) < 535.5 := by
  rw [two_mul, exp_add]; have := exp_pi_lt; have := exp_pos π; nlinarith

theorem exp_neg_two_pi_gt : 1 / 535.5 < exp (-(2 * π)) := by
  rw [exp_neg, one_div]; exact inv_strictAnti₀ (exp_pos _) exp_two_pi_lt

theorem sqrt2_lt : √2 < 1.41421357 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
theorem sqrt3_lt : √3 < 1.73205081 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
theorem sqrt3_gt : 1.7320508 < √3 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)

/-! ## J4: the `e^{-π}` constants and the counting constant -/

theorem J4_exp_neg_pi : 0.04321 < exp (-π) ∧ 0.51856 < 12 * exp (-π) ∧ 1.03713 < 24 * exp (-π) ∧
    4248 < 12 * 8192 * exp (-π) ∧ 4249 < 24 * 4097 * exp (-π) := by
  have h := exp_neg_pi_gt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num at h ⊢ <;> linarith

theorem J4_exp_pi : exp (3.141593 : ℝ) < 23.1408 ∧ exp π < 23.1408 :=
  ⟨((exp_up 4 (2.1932802406838973 : ℝ))).trans_lt (by norm_num), exp_pi_lt.trans (by norm_num)⟩

theorem J4_two_pi : exp (2 * π) < 535.5 ∧ 0.02240 < 12 * exp (-(2 * π)) ∧ 1.86e-3 < exp (-(2 * π)) ∧
    2 * π < 6.283186 ∧ 1.43 < 9.01 / (2 * π) := by
  have h := exp_neg_two_pi_gt
  refine ⟨exp_two_pi_lt, by norm_num at h ⊢; linarith, by norm_num at h ⊢; linarith,
    by linarith [Real.pi_lt_d6], ?_⟩
  rw [lt_div_iff₀ (by positivity)]; linarith [Real.pi_lt_d6]

theorem J4_log1p : 15 / 8192 < log (1 + exp (-(2 * π))) ∧ 1.8656e-3 < log (1 + exp (-(2 * π))) := by
  have h := exp_neg_two_pi_gt
  have hp : 0 < 1 + exp (-(2 * π)) := by positivity
  constructor
  · rw [lt_log_iff_exp_lt hp]
    have u : exp (15 / 8192 : ℝ) ≤ (1.0018327320917844 : ℝ) ^ 1 := (exp_up 1 (1.0018327320917844 : ℝ))
    norm_num at u h ⊢; linarith
  · rw [lt_log_iff_exp_lt hp]
    have u : exp (1.8656e-3 : ℝ) ≤ (1.0018673413143770 : ℝ) ^ 1 := (exp_up 1 (1.0018673413143770 : ℝ))
    norm_num at u h ⊢; linarith

theorem J4_exp_9_0108 : 353.9 < exp (9.0108 - π) ∧ 8191 < exp (9.0108 : ℝ) := by
  constructor
  · calc (353.9 : ℝ) < (2.0826703917378034 : ℝ) ^ 8 := by norm_num
      _ ≤ exp 5.8692073 := (exp_dn 8 (2.0826703917378034 : ℝ))
      _ ≤ exp (9.0108 - π) := exp_le_exp.2 (by linarith [pi_hi])
  · exact (by norm_num : (8191 : ℝ) < _).trans_le (exp_dn 16 (1.7562397187648902 : ℝ))

theorem J4_log_two_add_sqrt3 : 0.76 * √3 ≤ log (2 + √3) := by
  rw [le_log_iff_exp_le (by positivity)]
  calc exp (0.76 * √3) ≤ exp 1.31637 := exp_le_exp.2 (by linarith [sqrt3_lt])
    _ ≤ (1.9312838712089957 : ℝ) ^ 2 := (exp_up 2 (1.9312838712089957 : ℝ))
    _ ≤ 3.72986 := by norm_num
    _ ≤ 2 + √3 := by linarith [sqrt3_gt]

/-- The counting constant `C = 2/(1-e^{-1.52}) · [((1+e^{-b})/(1-e^{-b}))³ - 1]`,
`b = 1.52/√3`. -/
noncomputable def countC : ℝ :=
  2 / (1 - exp (-1.52)) * (((1 + exp (-(1.52 / √3))) / (1 - exp (-(1.52 / √3)))) ^ 3 - 1)

theorem J4_countC : countC < 33.878 ∧ countC < 34 := by
  have hp : exp (-1.52 : ℝ) ≤ 1 / 4.5722 := by
    rw [exp_neg, one_div]
    exact inv_anti₀ (by norm_num) ((by norm_num : (4.5722 : ℝ) ≤ _).trans (exp_dn 2 (2.1382762204145052 : ℝ)))
  have hb : 0.87757 ≤ 1.52 / √3 := by
    rw [le_div_iff₀ (by positivity)]; linarith [sqrt3_lt]
  have hq : exp (-(1.52 / √3)) ≤ 1 / 2.405 := by
    rw [exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (((by norm_num : (2.405 : ℝ) ≤ _).trans (exp_dn 1 (2.4050483319624101 : ℝ))).trans
      (exp_le_exp.2 hb))
  have hq0 := exp_pos (-(1.52 / √3))
  have h1 : 2 / (1 - exp (-1.52)) ≤ 2 / (1 - 1 / 4.5722) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h2 : (1 + exp (-(1.52 / √3))) / (1 - exp (-(1.52 / √3))) ≤ (1 + 1 / 2.405) / (1 - 1 / 2.405) :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) (by linarith)
  have h2' : 1 ≤ (1 + exp (-(1.52 / √3))) / (1 - exp (-(1.52 / √3))) := by
    have : (1 : ℝ) / 2.405 < 1 := by norm_num
    rw [le_div_iff₀ (by linarith)]; linarith
  have h3 := pow_le_pow_left₀ (by linarith) h2 3
  have h4 : 0 ≤ ((1 + exp (-(1.52 / √3))) / (1 - exp (-(1.52 / √3)))) ^ 3 - 1 := by
    have := one_le_pow₀ h2' (n := 3); linarith
  have h5 : countC ≤ 2 / (1 - 1 / 4.5722) * (((1 + 1 / 2.405) / (1 - 1 / 2.405)) ^ 3 - 1) :=
    mul_le_mul h1 (by linarith) h4 (by norm_num)
  have h6 : 2 / (1 - 1 / 4.5722) * (((1 + 1 / 2.405) / (1 - 1 / 2.405)) ^ 3 - 1) < (33.878 : ℝ) := by
    norm_num
  constructor <;> linarith

theorem J4_misc : 8.3176 < 12 * log 2 ∧ exp (2.0794 : ℝ) < 7.9997 := by
  refine ⟨by linarith [log_two_bounds.1], ((exp_up 4 (1.6817753644733305 : ℝ))).trans_lt (by norm_num)⟩

/-- `k ≥ 20`: `-log(1 - e^{-2π/20}) > 1.31`. -/
theorem J4_g20 : 1.31 < -log (1 - exp (-(2 * π / 20))) := by
  have hlt : exp (-(2 * π / 20)) < 1 := by
    rw [← exp_zero]; exact exp_lt_exp.2 (by linarith [Real.pi_pos])
  have hy : 0 < 1 - exp (-(2 * π / 20)) := by linarith
  have h1 : ((1.3691077706262445 : ℝ) ^ 1)⁻¹ ≤ exp (-(2 * π / 20)) := by
    calc ((1.3691077706262445 : ℝ) ^ 1)⁻¹ ≤ (exp 0.31415926536)⁻¹ :=
          inv_anti₀ (exp_pos _) (exp_up 1 (1.3691077706262445 : ℝ))
      _ = exp (-0.31415926536) := (exp_neg _).symm
      _ ≤ _ := exp_le_exp.2 (by linarith [pi_hi])
  have h2 : exp (1.31 : ℝ) ≤ (1.9251425173767595 : ℝ) ^ 2 := (exp_up 2 (1.9251425173767595 : ℝ))
  apply lt_neg_log hy
  calc (1 - exp (-(2 * π / 20))) * exp 1.31 ≤ (1 - ((1.3691077706262445 : ℝ) ^ 1)⁻¹) * (1.9251425173767595 : ℝ) ^ 2 :=
        mul_le_mul (by linarith) h2 (exp_pos _).le (by norm_num)
    _ < 1 := by norm_num

/-! ## J5 -/

/-- `D = e^{1/(5·96³)} - 1`. -/
noncomputable def D : ℝ := exp (1 / (5 * 96 ^ 3)) - 1

theorem J5_D : 2.26056155e-7 ≤ D ∧ D < 2.26056165e-7 ∧ D ≤ 2.2606e-7 := by
  have u : exp (1 / (5 * 96 ^ 3) : ℝ) ≤ (1.0000002260561599 : ℝ) ^ 1 := (exp_up 1 (1.0000002260561599 : ℝ))
  have l : (1.0000002260561598 : ℝ) ^ 1 ≤ exp (1 / (5 * 96 ^ 3) : ℝ) := (exp_dn 1 (1.0000002260561598 : ℝ))
  unfold D; refine ⟨?_, ?_, ?_⟩ <;> norm_num at u l ⊢ <;> linarith

theorem J5_logD : 15.3024 ≤ log (1 / D) := by
  have hD := J5_D
  have hD0 : 0 < D := by linarith [hD.1]
  rw [one_div, log_inv]
  apply le_neg_log hD0
  have u : exp (15.3024 : ℝ) ≤ (2.6023112696270322 : ℝ) ^ 16 := (exp_up 16 (2.6023112696270322 : ℝ))
  calc D * exp 15.3024 ≤ 2.26056165e-7 * (2.6023112696270322 : ℝ) ^ 16 :=
        mul_le_mul hD.2.1.le u (exp_pos _).le (by norm_num)
    _ ≤ 1 := by norm_num

theorem J5_misc : 0.632 ≤ 1 - exp (-1) ∧ D * exp (1 / 4) ≤ 2.903e-7 ∧ 0.40546510 < log 1.5 ∧
    0.405465 ≤ log (1.5 - 1.4515e-7) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [exp_neg]
    have : (exp 1)⁻¹ ≤ (2.7182818283 : ℝ)⁻¹ := inv_anti₀ (by norm_num) Real.exp_one_gt_d9.le
    norm_num at this ⊢; linarith
  · have hD := J5_D
    have u : exp (1 / 4 : ℝ) ≤ (1.2840254166877415 : ℝ) ^ 1 := (exp_up 1 (1.2840254166877415 : ℝ))
    calc D * exp (1 / 4) ≤ 2.26056165e-7 * (1.2840254166877415 : ℝ) ^ 1 :=
          mul_le_mul hD.2.1.le u (exp_pos _).le (by norm_num)
      _ ≤ 2.903e-7 := by norm_num
  · rw [lt_log_iff_exp_lt (by norm_num)]; exact ((exp_up 1 (1.4999999878377556 : ℝ))).trans_lt (by norm_num)
  · rw [le_log_iff_exp_le (by norm_num)]; exact ((exp_up 1 (1.4999998378377644 : ℝ))).trans (by norm_num)

/-- `1/c₂ = 3√2 π/0.94³`. -/
noncomputable def c2inv : ℝ := 3 * √2 * π / 0.94 ^ 3

theorem J5x : c2inv < 16.0475 ∧ 2 / 3 * log 16.05 < 1.8505 ∧ log 8 < 2.0795 ∧
    1 + 2 / 3 * log c2inv + log 8 < 4.931 ∧ exp (10.39 : ℝ) < 32533 ∧ 26.31 < exp (3.27 : ℝ) ∧
    exp (9 : ℝ) < 8103.1 := by
  have hc : c2inv < 16.0475 := by
    have h : √2 * π < 1.41422 * 3.1416 :=
      mul_lt_mul'' (by linarith [sqrt2_lt]) (by linarith [pi_hi]) (Real.sqrt_nonneg _) Real.pi_pos.le
    unfold c2inv; rw [div_lt_iff₀ (by norm_num)]; nlinarith
  have hc0 : 0 < c2inv := by unfold c2inv; positivity
  have h16 : log 16.05 < 2.77575 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    exact (by norm_num : (16.05 : ℝ) < _).trans_le (exp_dn 4 (2.0015812636220112 : ℝ))
  have h8 : log 8 < 2.0795 := by
    have : log (8 : ℝ) = 3 * log 2 := by rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; norm_num
    rw [this]; linarith [log_two_bounds.2]
  have hlog : log c2inv < log 16.05 := log_lt_log hc0 (by linarith)
  refine ⟨hc, by linarith, h8, by linarith, ((exp_up 16 (1.9143439900472626 : ℝ))).trans_lt (by norm_num),
    (by norm_num : (26.31 : ℝ) < _).trans_le (exp_dn 4 (2.2648306771430804 : ℝ)), ((exp_up 16 (1.7550546569603787 : ℝ))).trans_lt (by norm_num)⟩

/-! ## J7 -/

theorem J7_logs : 7729 < exp (9 : ℝ) ∧ log 7729 < 8.953 ∧ 8.948 < log 7700 := by
  refine ⟨(by norm_num : (7729 : ℝ) < _).trans_le (exp_dn 16 (1.7550546569581093 : ℝ)), ?_, ?_⟩
  · rw [log_lt_iff_lt_exp (by norm_num)]; exact (by norm_num : (7729 : ℝ) < _).trans_le (exp_dn 16 (1.7499067485955643 : ℝ))
  · rw [lt_log_iff_exp_lt (by norm_num)]; exact ((exp_up 16 (1.7493599881745240 : ℝ))).trans_lt (by norm_num)

/-- `q(θ) = (θ+θ²)/(2-θ-θ²)`. -/
noncomputable def q (θ : ℝ) : ℝ := (θ + θ ^ 2) / (2 - θ - θ ^ 2)

theorem J7_d4 : 15.3087 ≤ log (1 / q (1 / 2225664)) ∧ 30.6 ≤ 2 * log (1 / q (1 / 2225664)) := by
  have h : 15.3087 ≤ log (1 / q (1 / 2225664)) := by
    rw [one_div, log_inv]; apply le_neg_log (by norm_num [q])
    calc q (1 / 2225664) * exp 15.3087 ≤ q (1 / 2225664) * (2.6033361314458589 : ℝ) ^ 16 :=
          mul_le_mul_of_nonneg_left (exp_up 16 (2.6033361314458589 : ℝ)) (by norm_num [q])
      _ ≤ 1 := by norm_num [q]
  exact ⟨h, by linarith⟩

theorem J7_d3 : 12.1306 ≤ log (1 / q (1 / 92736)) ∧ 24.2 ≤ 2 * log (1 / q (1 / 92736)) := by
  have h : 12.1306 ≤ log (1 / q (1 / 92736)) := by
    rw [one_div, log_inv]; apply le_neg_log (by norm_num [q])
    calc q (1 / 92736) * exp 12.1306 ≤ q (1 / 92736) * (2.1343507455778719 : ℝ) ^ 16 :=
          mul_le_mul_of_nonneg_left (exp_up 16 (2.1343507455778719 : ℝ)) (by norm_num [q])
      _ ≤ 1 := by norm_num [q]
  exact ⟨h, by linarith⟩

theorem J7_d2 : 8.9522 ≤ log (1 / q (1 / 3864)) ∧ 17.9 ≤ 2 * log (1 / q (1 / 3864)) := by
  have h : 8.9522 ≤ log (1 / q (1 / 3864)) := by
    rw [one_div, log_inv]; apply le_neg_log (by norm_num [q])
    calc q (1 / 3864) * exp 8.9522 ≤ q (1 / 3864) * (1.7498192554476125 : ℝ) ^ 16 :=
          mul_le_mul_of_nonneg_left (exp_up 16 (1.7498192554476125 : ℝ)) (by norm_num [q])
      _ ≤ 1 := by norm_num [q]
  exact ⟨h, by linarith⟩

theorem J7_pi_sqrt : 125381 ≤ 13 / 8 * 17805312 * exp (-(π * √3)) ∧
    4363 ≤ 370944 * exp (-(π * √2)) := by
  have h3 : π * √3 ≤ 5.4413981004 := by
    have := mul_le_mul pi_hi.le sqrt3_lt.le (Real.sqrt_nonneg 3) (by norm_num); linarith
  have h2 : π * √2 ≤ 4.4428829622 := by
    have := mul_le_mul pi_hi.le sqrt2_lt.le (Real.sqrt_nonneg 2) (by norm_num); linarith
  have e3 : exp (π * √3) ≤ (1.9742227222816932 : ℝ) ^ 8 := (exp_le_exp.2 h3).trans (exp_up 8 (1.9742227222816932 : ℝ))
  have e2 : exp (π * √2) ≤ (1.7425688416495447 : ℝ) ^ 8 := (exp_le_exp.2 h2).trans (exp_up 8 (1.7425688416495447 : ℝ))
  constructor
  · rw [exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)]; norm_num at e3 ⊢; linarith
  · rw [exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)]; norm_num at e2 ⊢; linarith

/-! ## J10: flux constants -/

theorem one_sub_ge_exp {t : ℝ} (h1 : t < 1) : exp (-(t / (1 - t))) ≤ 1 - t := by
  have h := add_one_le_exp (t / (1 - t))
  have hpos : 0 < 1 - t := by linarith
  have h1' : 1 + t / (1 - t) = 1 / (1 - t) := by field_simp; ring
  rw [exp_neg, inv_le_comm₀ (exp_pos _) hpos, ← one_div]
  linarith

theorem J10 : exp (10.80 : ℝ) < 49020.81 ∧ 49513.4 < exp (10.81 : ℝ) ∧ 5.40 < log 49155 / 2 ∧
    log 49155 / 2 < 5.41 ∧ 0.1342 < 2 / √(√49155) ∧ 2 / √(√49155) < 0.1344 ∧
    exp (-((2 / 49155) / (1 - 2 / 49155))) ≤ 1 - 2 / 49155 := by
  have u : exp (10.80 : ℝ) ≤ (1.9640329759703849 : ℝ) ^ 16 := (exp_up 16 (1.9640329759703849 : ℝ))
  have s1 : 14.881 < √(√49155) := by
    rw [Real.lt_sqrt (by norm_num), Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : √(√49155) < 14.903 := by
    rw [Real.sqrt_lt' (by norm_num), Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨u.trans_lt (by norm_num), (by norm_num : (49513.4 : ℝ) < _).trans_le (exp_dn 16 (1.9652608802400314 : ℝ)), ?_, ?_, ?_, ?_,
    one_sub_ge_exp (by norm_num)⟩
  · have : 10.80 < log 49155 := by
      rw [lt_log_iff_exp_lt (by norm_num)]; exact u.trans_lt (by norm_num)
    linarith
  · have : log 49155 < 10.82 := by
      rw [log_lt_iff_lt_exp (by norm_num)]; exact (by norm_num : (49155 : ℝ) < _).trans_le (exp_dn 16 (1.9664895522099654 : ℝ))
    linarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-! ## J11: universal steps -/

/-- `Λ(q) = 1728 log(1 + (e^{q/216} - 1)²)`. -/
noncomputable def Λ (q : ℝ) : ℝ := 1728 * log (1 + (exp (q / 216) - 1) ^ 2)

theorem J11_log98 : 25.43 < 216 * log (9 / 8) ∧ 216 * log (9 / 8) < 25.46 := by
  constructor
  · have : 25.43 / 216 < log (9 / 8) := by
      rw [lt_log_iff_exp_lt (by norm_num)]; exact ((exp_up 1 (1.1249420030482407 : ℝ))).trans_lt (by norm_num)
    linarith
  · have : log (9 / 8) < 25.46 / 216 := by
      rw [log_lt_iff_lt_exp (by norm_num)]; exact (by norm_num : (9 / 8 : ℝ) < _).trans_le (exp_dn 1 (1.1250982558437458 : ℝ))
    linarith

theorem J11_Λ : Λ 24 < 23.71 ∧ 28 < Λ 26 := by
  constructor
  · have u : exp (24 / 216 : ℝ) ≤ (1.1175190687418637 : ℝ) ^ 1 := (exp_up 1 (1.1175190687418637 : ℝ))
    have h0 : 1 ≤ exp (24 / 216 : ℝ) := one_le_exp (by norm_num)
    have hsq := pow_le_pow_left₀ (by linarith) (sub_le_sub_right u 1) 2
    have : log (1 + (exp (24 / 216) - 1) ^ 2) < 23.71 / 1728 := by
      rw [log_lt_iff_lt_exp (by positivity)]
      calc 1 + (exp (24 / 216) - 1) ^ 2 ≤ 1 + ((1.1175190687418637 : ℝ) ^ 1 - 1) ^ 2 := by linarith
        _ < (1.0138156306442674 : ℝ) ^ 1 := by norm_num
        _ ≤ _ := (exp_dn 1 (1.0138156306442674 : ℝ))
    unfold Λ; linarith
  · have l : (1.1279145203471802 : ℝ) ^ 1 ≤ exp (26 / 216 : ℝ) := (exp_dn 1 (1.1279145203471802 : ℝ))
    have hsq := pow_le_pow_left₀ (by norm_num) (sub_le_sub_right l 1) 2
    have : 28 / 1728 < log (1 + (exp (26 / 216) - 1) ^ 2) := by
      rw [lt_log_iff_exp_lt (by positivity)]
      calc exp (28 / 1728) ≤ (1.0163356956664142 : ℝ) ^ 1 := (exp_up 1 (1.0163356956664142 : ℝ))
        _ < 1 + ((1.1279145203471802 : ℝ) ^ 1 - 1) ^ 2 := by norm_num
        _ ≤ _ := by linarith
    unfold Λ; linarith

theorem J11_misc : exp (14.38 : ℝ) < 1.7586e6 ∧ exp (1 / 1769472 : ℝ) - 1 ≤ 1 / 1769471 ∧
    (exp (1 / 8192) - 1) * exp 9.0108 < 1 ∧ 216 * log (1 + 1 / 1769473) < 1 / 8192 ∧
    1 / 4097 < 432 * log (1 + 1 / 1769473) - 216 * log (1 + (1 / 1769473) ^ 2) := by
  refine ⟨((exp_up 16 (2.4565305280380287 : ℝ))).trans_lt (by norm_num), ?_, ?_, ?_, ?_⟩
  · have := expm1_le (t := (1 / 1769472 : ℝ)) (by norm_num); norm_num at this ⊢; linarith
  · have u1 : exp (1 / 8192 : ℝ) ≤ (1.0001220777633838 : ℝ) ^ 1 := (exp_up 1 (1.0001220777633838 : ℝ))
    have u2 : exp (9.0108 : ℝ) ≤ (1.7562397187671925 : ℝ) ^ 16 := (exp_up 16 (1.7562397187671925 : ℝ))
    have h0 : 1 ≤ exp (1 / 8192 : ℝ) := one_le_exp (by norm_num)
    calc (exp (1 / 8192) - 1) * exp 9.0108 ≤ ((1.0001220777633838 : ℝ) ^ 1 - 1) * (1.7562397187671925 : ℝ) ^ 16 :=
          mul_le_mul (by linarith) u2 (exp_pos _).le (by norm_num)
      _ < 1 := by norm_num
  · have := log_le_sub_one_of_pos (x := (1 + 1 / 1769473 : ℝ)) (by norm_num)
    norm_num at this ⊢; linarith
  · have h1 := one_sub_inv_le_log_of_pos (x := (1 + 1 / 1769473 : ℝ)) (by norm_num)
    have h2 := log_le_sub_one_of_pos (x := (1 + (1 / 1769473) ^ 2 : ℝ)) (by norm_num)
    norm_num at h1 h2 ⊢; linarith

/-! ## J12: the exponential form of L4 -/

theorem J12_expm1 : exp (1 / 8192 : ℝ) - 1 ≤ 1 / 8191 ∧ exp (16 / 8192 : ℝ) - 1 ≤ 1 / 511 ∧
    exp (32 / 8192 : ℝ) - 1 ≤ 1 / 255 ∧ exp (64 / 8192 : ℝ) - 1 ≤ 1 / 127 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := expm1_le (t := (1 / 8192 : ℝ)) (by norm_num); norm_num at this ⊢; linarith
  · have := expm1_le (t := (16 / 8192 : ℝ)) (by norm_num); norm_num at this ⊢; linarith
  · have := expm1_le (t := (32 / 8192 : ℝ)) (by norm_num); norm_num at this ⊢; linarith
  · have := expm1_le (t := (64 / 8192 : ℝ)) (by norm_num); norm_num at this ⊢; linarith

/-- **J12.** The L4 sum with exponentials is `< 2.1640·10⁻⁴`. -/
theorem J12 : 16 * (exp (1 / 8192 : ℝ) - 1) ^ 2 + 8 * (exp (16 / 8192 : ℝ) - 1) ^ 2 +
    4 * (exp (32 / 8192 : ℝ) - 1) ^ 2 + 2 * (exp (64 / 8192 : ℝ) - 1) ^ 2 < 2.1640e-4 ∧
    2 / 81 < 24 * exp (-π) := by
  obtain ⟨h1, h2, h3, h4⟩ := J12_expm1
  have p : ∀ t : ℝ, 0 ≤ t → ∀ b, exp t - 1 ≤ b → (exp t - 1) ^ 2 ≤ b ^ 2 := fun t ht b hb =>
    pow_le_pow_left₀ (by linarith [one_le_exp ht]) hb 2
  have := p _ (by norm_num) _ h1
  have := p _ (by norm_num) _ h2
  have := p _ (by norm_num) _ h3
  have := p _ (by norm_num) _ h4
  have h := exp_neg_pi_gt
  constructor
  · norm_num at *; linarith
  · norm_num at h ⊢; linarith

/-! ## Unlabelled rows of the certificate table -/

theorem A_rows : exp (6.4 : ℝ) < 601.85 ∧ 6063 < exp (8.71 : ℝ) ∧ exp (2.708 : ℝ) < 14.9993 ∧
    exp (0.014746 : ℝ) - 1 < 0.01485526 ∧ 2 / √8192 + 1 / 8192 < 0.0223 ∧
    48 * π * √(5 / 2) < 239 ∧ 4 * π * √(5 / 2) < 19.87 ∧ 0.0385 < 8 * exp (-π) - 0.3072 ∧
    π / 2 * 1.44 < 2.27 ∧ 4.61 ≤ (2 * π - 0.2) ^ 2 / 8 ∧ 38 / 3 < 9 + √17 ∧ log 4 < 2 ∧
    21 * 0.1 * exp (-46) < 1e-19 := by
  have s : √(5 / 2) < 1.58114 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hs0 := Real.sqrt_nonneg (5 / 2)
  have hpi := pi_hi
  have hpi' := pi_lo
  refine ⟨((exp_up 8 (2.2255409284950616 : ℝ))).trans_lt (by norm_num), (by norm_num : (6063 : ℝ) < _).trans_le (exp_dn 16 (1.7235308389033857 : ℝ)),
    ((exp_up 4 (1.9679649726083132 : ℝ))).trans_lt (by norm_num), ?_, ?_, ?_, ?_, ?_, by linarith, by nlinarith, ?_, ?_, ?_⟩
  · have : exp (0.014746 : ℝ) ≤ (1.0148552586400516 : ℝ) ^ 1 := (exp_up 1 (1.0148552586400516 : ℝ))
    norm_num at this ⊢; linarith
  · have h : 90.5 < √8192 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    have : 2 / √8192 < 2 / 90.5 := div_lt_div_of_pos_left (by norm_num) (by norm_num) h
    norm_num at this ⊢; linarith
  · nlinarith [mul_le_mul hpi.le s.le hs0 (by norm_num)]
  · nlinarith [mul_le_mul hpi.le s.le hs0 (by norm_num)]
  · have := exp_neg_pi_gt; norm_num at this ⊢; linarith
  · have : 4 < √17 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    linarith
  · rw [log_lt_iff_lt_exp (by norm_num)]; exact (by norm_num : (4 : ℝ) < _).trans_le (exp_dn 2 (2.7182818261984928 : ℝ))
  · rw [exp_neg]
    have : (2.0518667734459822 : ℝ) ^ 64 ≤ exp (46 : ℝ) := (exp_dn 64 (2.0518667734459822 : ℝ))
    have h : (exp 46)⁻¹ ≤ ((2.0518667734459822 : ℝ) ^ 64)⁻¹ := inv_anti₀ (by norm_num) this
    calc 21 * 0.1 * (exp 46)⁻¹ ≤ 21 * 0.1 * ((2.0518667734459822 : ℝ) ^ 64)⁻¹ := by gcongr
      _ < 1e-19 := by norm_num

theorem A_heat_kernel : π ^ 2 / (32 * log 15) < 0.114 ∧
    π / 2 * (16 + 0.72 * log 4) < 26.71 := by
  have hpi := pi_hi
  have hl15 : 2.708 < log 15 := by
    rw [lt_log_iff_exp_lt (by norm_num)]; exact ((exp_up 4 (1.9679649726083132 : ℝ))).trans_lt (by norm_num)
  have hl4 : log (4 : ℝ) < 1.3863 := by
    have : log (4 : ℝ) = 2 * log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
    rw [this]; linarith [log_two_bounds.2]
  have hl4' : 0 < log (4 : ℝ) := log_pos (by norm_num)
  constructor
  · rw [div_lt_iff₀ (by nlinarith)]; nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- `ε₈(c) = 12(log c + 5.42)/c` crosses `1/99` between `18084` and `18085`. -/
theorem A_eps8 : 12 * (log 18085 + 5.42) / 18085 < 1 / 99 ∧ 1 / 99 < 12 * (log 18084 + 5.42) / 18084 := by
  have h1 : log 18085 < 9.80305 := by
    rw [log_lt_iff_lt_exp (by norm_num)]; exact (by norm_num : (18085 : ℝ) < _).trans_le (exp_dn 16 (1.8453899773541450 : ℝ))
  have h2 : 9.8025 < log 18084 := by
    rw [lt_log_iff_exp_lt (by norm_num)]; exact ((exp_up 16 (1.8453265431702834 : ℝ))).trans_lt (by norm_num)
  constructor
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith

/-- The `η₀` row: `(1 - 2t + 2t²) e^{1/161} < 1 - 7·10⁻⁸` at `t = 1 - e^{-0.00311048}`. -/
theorem A_eta0 :
    (1 - 2 * (1 - exp (-0.00311048)) + 2 * (1 - exp (-0.00311048)) ^ 2) * exp (1 / 161) < 1 - 7e-8 := by
  set t := 1 - exp (-0.00311048 : ℝ) with ht
  have l : (1.0031153225625114 : ℝ) ^ 1 ≤ exp (0.00311048 : ℝ) := (exp_dn 1 (1.0031153225625114 : ℝ))
  have hlo : 1 - ((1.0031153225625114 : ℝ) ^ 1)⁻¹ ≤ t := by
    rw [ht, exp_neg]; have := inv_anti₀ (by norm_num) l; linarith
  have hhi : t ≤ 1 / 2 := by
    rw [ht]; have : (1 / 2 : ℝ) ≤ exp (-0.00311048) := by
      have := add_one_le_exp (-0.00311048 : ℝ); linarith
    linarith
  set t0 := 1 - ((1.0031153225625114 : ℝ) ^ 1)⁻¹ with ht0
  have ht0' : 0 ≤ t0 := by rw [ht0]; norm_num
  have hg : 1 - 2 * t + 2 * t ^ 2 ≤ 1 - 2 * t0 + 2 * t0 ^ 2 := by nlinarith
  have hg0 : 0 ≤ 1 - 2 * t + 2 * t ^ 2 := by nlinarith
  have u : exp (1 / 161 : ℝ) ≤ (1.0062305095021849 : ℝ) ^ 1 := (exp_up 1 (1.0062305095021849 : ℝ))
  calc (1 - 2 * t + 2 * t ^ 2) * exp (1 / 161) ≤ (1 - 2 * t0 + 2 * t0 ^ 2) * (1.0062305095021849 : ℝ) ^ 1 :=
        mul_le_mul hg u (exp_pos _).le (by nlinarith)
    _ < 1 - 7e-8 := by rw [ht0]; norm_num

end YangMills.OneCube.Transcendental
