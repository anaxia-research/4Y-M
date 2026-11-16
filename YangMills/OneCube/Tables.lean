import YangMills.OneCube.Transcendental

/-!
# One-cube criteria: the certified tables (checks J8, J9)

**J8.** For the strong-coupling rows, `θ = tanh(β) κ(z)` (any compact `G`, with
`κ(z) = max(12 + 4z + 2z², 6 + 12z)`) or `θ = β κ(z)/4` (`SU(2)`), and
`L = (1 - θ)/(K β z)` with `K = 96·161·48³`. The datum at `T` is
`(1 + 2/T)² ≤ z` and `(T + 1)⁴ ≤ L z^T`; we prove that it holds at the tabulated
`T_*` and fails at every even `4 ≤ T < T_*`. `tanh β` is enclosed through
`tanh β = (e^{2β} - 1)/(e^{2β} + 1)` and the Taylor bounds of `Transcendental`.

**J9.** For `N_c ∈ {2, 3, 10, 10⁶}` and `β ∈ {1/480, 1/192, 1/96, 1/64}`, with
`α = 36β/(1 - 12β)` and `h = ⌊(T - 3)/2⌋`, the condition
`4255469568 N_c² β T⁴ α^h ≤ h + 1` holds for every `T ≥ T_*` and fails at `T_* - 1`.
-/

namespace YangMills.OneCube.Tables

open Real YangMills.OneCube.Transcendental

/-- If `(T₀ + s)⁴ c ≤ d T₀⁴` then `(T + s)⁴ c ≤ d T⁴` for `T ≥ T₀ > 0`, `s, c ≥ 0`. -/
theorem ratio_mono {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {s c d T0 T : F}
    (hs : 0 ≤ s) (hc : 0 ≤ c) (h0 : 0 < T0) (h : T0 ≤ T) (h1 : (T0 + s) ^ 4 * c ≤ d * T0 ^ 4) :
    (T + s) ^ 4 * c ≤ d * T ^ 4 := by
  have hT : 0 < T := lt_of_lt_of_le h0 h
  have e1 : (T + s) * T0 ≤ (T0 + s) * T := by nlinarith
  have e2 := pow_le_pow_left₀ (by positivity) e1 4
  rw [mul_pow, mul_pow] at e2
  have e3 := mul_le_mul_of_nonneg_right e2 hc
  have e4 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hT.le 4)
  have : (T + s) ^ 4 * c * T0 ^ 4 ≤ d * T ^ 4 * T0 ^ 4 := by nlinarith
  exact le_of_mul_le_mul_right this (by positivity)

/-! ## J8 -/

/-- `κ(z) = max(12 + 4z + 2z², 6 + 12z)`. -/
noncomputable def kappa (z : ℝ) : ℝ := max (12 + 4 * z + 2 * z ^ 2) (6 + 12 * z)

/-- `K = 96·161·48³`. -/
def K : ℕ := 96 * 161 * 48 ^ 3

/-- The datum at `T`: `(1 + 2/T)² ≤ z` and `(T + 1)⁴ ≤ L z^T`. -/
def Datum (T : ℕ) (z L : ℝ) : Prop := (1 + 2 / (T : ℝ)) ^ 2 ≤ z ∧ ((T : ℝ) + 1) ^ 4 ≤ L * z ^ T

theorem tanh_eq_exp (x : ℝ) : tanh x = (exp (2 * x) - 1) / (exp (2 * x) + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, show 2 * x = x + x by ring, exp_add,
    exp_neg]
  have h := exp_pos x
  field_simp

theorem tanh_le_of {x c : ℝ} (h : exp (2 * x) ≤ c) : tanh x ≤ (c - 1) / (c + 1) := by
  rw [tanh_eq_exp]
  have hE := exp_pos (2 * x)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

theorem le_tanh_of {x c : ℝ} (hc : 0 ≤ c) (h : c ≤ exp (2 * x)) : (c - 1) / (c + 1) ≤ tanh x := by
  rw [tanh_eq_exp]
  have hE := exp_pos (2 * x)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

/-- The certificate: the datum at `T_s` from the smallest admissible `L`, failure below
`T_s` from the largest. `(1 + 2/T)² ≤ z` fails for even `T < T₁` (it fails at `T₁ - 2`);
for `T ≥ T₁`, `(T + 1)⁴ z^{-T}` decreases in steps of two, and it exceeds `L` at `T_s - 2`. -/
theorem cert (z Lmin Lmax : ℚ) (L : ℝ) (Ts T1 : ℕ) (hz : 1 < z) (hmin : (Lmin : ℝ) ≤ L)
    (hmax : L ≤ Lmax) (hd1 : (1 + 2 / (Ts : ℚ)) ^ 2 ≤ z) (hd2 : ((Ts : ℚ) + 1) ^ 4 ≤ Lmin * z ^ Ts)
    (hf : T1 = 4 ∨ z < (1 + 2 / ((T1 : ℚ) - 2)) ^ 2)
    (hT1 : ((T1 : ℚ) + 1 + 2) ^ 4 * 1 ≤ z ^ 2 * ((T1 : ℚ) + 1) ^ 4)
    (hlast : Lmax * z ^ (Ts - 2) < (((Ts - 2 : ℕ) : ℚ) + 1) ^ 4)
    (hT14 : 4 ≤ T1) (hT1e : T1 % 2 = 0) (hTs : Ts % 2 = 0) :
    Datum Ts z L ∧ ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < Ts → ¬ Datum T z L := by
  have hz' : (1 : ℝ) < z := by exact_mod_cast hz
  have hzp : (0 : ℝ) < z := by linarith
  constructor
  · refine ⟨by have h := (Rat.cast_le (K := ℝ)).mpr hd1; push_cast at h; exact h, ?_⟩
    have h2 : ((Ts : ℝ) + 1) ^ 4 ≤ (Lmin : ℝ) * (z : ℝ) ^ Ts := by
      have h := (Rat.cast_le (K := ℝ)).mpr hd2; push_cast at h; exact h
    exact h2.trans (mul_le_mul_of_nonneg_right hmin (by positivity))
  · have hT1' : ((T1 : ℝ) + 1 + 2) ^ 4 * 1 ≤ (z : ℝ) ^ 2 * ((T1 : ℝ) + 1) ^ 4 := by
      have h := (Rat.cast_le (K := ℝ)).mpr hT1; push_cast at h; exact h
    have key : ∀ j : ℕ, T1 ≤ Ts - 2 - 2 * j →
        L * (z : ℝ) ^ (Ts - 2 - 2 * j) < (((Ts - 2 - 2 * j : ℕ) : ℝ) + 1) ^ 4 := by
      intro j
      induction j with
      | zero =>
        intro _
        have h : (Lmax : ℝ) * (z : ℝ) ^ (Ts - 2) < (((Ts - 2 : ℕ) : ℝ) + 1) ^ 4 := by
          have h := (Rat.cast_lt (K := ℝ)).mpr hlast; push_cast at h ⊢; exact h
        simp only [mul_zero, Nat.sub_zero]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hmax (by positivity)) h
      | succ j ih =>
        intro hj
        obtain ⟨a, ha⟩ : ∃ a, a = Ts - 2 - 2 * (j + 1) := ⟨_, rfl⟩
        rw [← ha] at hj ⊢
        have hsplit : Ts - 2 - 2 * j = a + 2 := by omega
        have ih' := ih (by omega)
        rw [hsplit, pow_add] at ih'
        push_cast at ih'
        have haT : (T1 : ℝ) ≤ a := by exact_mod_cast hj
        have hr := ratio_mono (s := (2 : ℝ)) (c := 1) (T0 := (T1 : ℝ) + 1) (T := (a : ℝ) + 1)
          (by norm_num) (by norm_num) (by positivity) (by linarith) hT1'
        have : L * (z : ℝ) ^ a * (z : ℝ) ^ 2 < ((a : ℝ) + 1) ^ 4 * (z : ℝ) ^ 2 := by
          have e : ((a : ℝ) + 2 + 1) = (a : ℝ) + 1 + 2 := by ring
          rw [e] at ih'; nlinarith
        exact lt_of_mul_lt_mul_right this (by positivity)
    intro T hT h4 hTs' ⟨d1, d2⟩
    by_cases hTT1 : T < T1
    · rcases hf with hf | hf
      · omega
      have hle : (T : ℝ) ≤ (T1 : ℝ) - 2 := by
        have : T + 2 ≤ T1 := by omega
        have : ((T + 2 : ℕ) : ℝ) ≤ T1 := by exact_mod_cast this
        push_cast at this; linarith
      have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
      have h' : (z : ℝ) < (1 + 2 / ((T1 : ℝ) - 2)) ^ 2 := by
        have h := (Rat.cast_lt (K := ℝ)).mpr hf; push_cast at h; exact h
      have h3 : 2 / ((T1 : ℝ) - 2) ≤ 2 / (T : ℝ) := div_le_div_of_nonneg_left (by norm_num) hT0 hle
      have h6 : (0 : ℝ) ≤ 2 / ((T1 : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
      have h5 : (1 + 2 / ((T1 : ℝ) - 2)) ^ 2 ≤ (1 + 2 / (T : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      linarith
    · have hj := key ((Ts - 2 - T) / 2) (by omega)
      rw [show Ts - 2 - 2 * ((Ts - 2 - T) / 2) = T by omega] at hj
      linarith

/-- A row for an arbitrary compact group: `θ = tanh(β) κ(z)`. -/
theorem rowG (β z θup θdn : ℚ) (Ts T1 : ℕ) (hβ : 0 < β) (hz : 1 < z)
    (hθ : tanh β * kappa z ≤ θup) (hθ' : θdn ≤ tanh β * kappa z)
    (hd1 : (1 + 2 / (Ts : ℚ)) ^ 2 ≤ z) (hd2 : ((Ts : ℚ) + 1) ^ 4 ≤ (1 - θup) / (K * β * z) * z ^ Ts)
    (hf : T1 = 4 ∨ z < (1 + 2 / ((T1 : ℚ) - 2)) ^ 2)
    (hT1 : ((T1 : ℚ) + 1 + 2) ^ 4 * 1 ≤ z ^ 2 * ((T1 : ℚ) + 1) ^ 4)
    (hlast : (1 - θdn) / (K * β * z) * z ^ (Ts - 2) < (((Ts - 2 : ℕ) : ℚ) + 1) ^ 4)
    (hT14 : 4 ≤ T1) (hT1e : T1 % 2 = 0) (hTs : Ts % 2 = 0) :
    Datum Ts z ((1 - tanh β * kappa z) / (K * β * z)) ∧
      ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < Ts → ¬ Datum T z ((1 - tanh β * kappa z) / (K * β * z)) := by
  have hpos : (0 : ℝ) < K * β * z := by
    have : (0 : ℝ) < β := by exact_mod_cast hβ
    have : (0 : ℝ) < z := by exact_mod_cast (by linarith : (0 : ℚ) < z)
    unfold K; positivity
  refine cert z ((1 - θup) / (K * β * z)) ((1 - θdn) / (K * β * z)) _ Ts T1 hz ?_ ?_ hd1 hd2 hf hT1
    hlast hT14 hT1e hTs
  · push_cast; exact div_le_div_of_nonneg_right (by linarith) hpos.le
  · push_cast; exact div_le_div_of_nonneg_right (by linarith) hpos.le

/-- A row for `SU(2)`: `θ = β κ(z)/4`, exact. -/
theorem rowSU2 (β z θ : ℚ) (Ts T1 : ℕ) (hθ : β * kappa z / 4 = θ)
    (hz : 1 < z)
    (hd1 : (1 + 2 / (Ts : ℚ)) ^ 2 ≤ z) (hd2 : ((Ts : ℚ) + 1) ^ 4 ≤ (1 - θ) / (K * β * z) * z ^ Ts)
    (hf : T1 = 4 ∨ z < (1 + 2 / ((T1 : ℚ) - 2)) ^ 2)
    (hT1 : ((T1 : ℚ) + 1 + 2) ^ 4 * 1 ≤ z ^ 2 * ((T1 : ℚ) + 1) ^ 4)
    (hlast : (1 - θ) / (K * β * z) * z ^ (Ts - 2) < (((Ts - 2 : ℕ) : ℚ) + 1) ^ 4)
    (hT14 : 4 ≤ T1) (hT1e : T1 % 2 = 0) (hTs : Ts % 2 = 0) :
    Datum Ts z ((1 - β * kappa z / 4) / (K * β * z)) ∧
      ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < Ts → ¬ Datum T z ((1 - β * kappa z / 4) / (K * β * z)) := by
  have hL : ((1 - β * kappa z / 4) / (K * β * z) : ℝ) = (((1 - θ) / (K * β * z) : ℚ) : ℝ) := by
    rw [hθ]; push_cast; ring
  rw [hL]
  exact cert z _ _ _ Ts T1 hz le_rfl le_rfl hd1 hd2 hf hT1 hlast hT14 hT1e hTs

/-- `artanh(1/18) = (1/2) log(19/17) ∈ (0.0556128, 0.0556129)`. -/
theorem J8_artanh : 0.0556128 < (1 / 2) * log (19 / 17) ∧ (1 / 2) * log (19 / 17) < 0.0556129 := by
  constructor
  · have : 0.1112256 < log (19 / 17) := by
      rw [lt_log_iff_exp_lt (by norm_num)]; exact ((exp_up 1 (1.1176470195826911 : ℝ))).trans_lt (by norm_num)
    linarith
  · have : log (19 / 17) < 0.1112258 := by
      rw [log_lt_iff_lt_exp (by norm_num)]; exact (by norm_num : (19 / 17 : ℝ) < _).trans_le (exp_dn 1 (1.1176472431121173 : ℝ))
    linarith

/-- **J8**, any `G`, row 1: `β = 1/1000`, `z = 15`, `T_* = 12`, `θ = tanh(β) κ(z) ∈ [0.521999826, 0.522]`. -/
theorem J8_G1 :
    tanh ((1 / 1000 : ℚ) : ℝ) * kappa (15 : ℚ) ≤ ((261 / 500 : ℚ) : ℝ) ∧
    Datum 12 (15 : ℚ) ((1 - tanh ((1 / 1000 : ℚ) : ℝ) * kappa (15 : ℚ)) / (K * ((1 / 1000 : ℚ) : ℝ) * (15 : ℚ))) ∧
    ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < 12 →
      ¬ Datum T (15 : ℚ) ((1 - tanh ((1 / 1000 : ℚ) : ℝ) * kappa (15 : ℚ)) / (K * ((1 / 1000 : ℚ) : ℝ) * (15 : ℚ))) := by
  have hk : kappa (15 : ℚ) = ((522 / 1 : ℚ) : ℝ) := by norm_num [kappa]
  have hu : exp (2 * ((1 / 1000 : ℚ) : ℝ)) ≤ (1.0020020013340003 : ℝ) ^ 1 := (exp_up 1 (1.0020020013340003 : ℝ))
  have hl : (1.0020020013340002 : ℝ) ^ 1 ≤ exp (2 * ((1 / 1000 : ℚ) : ℝ)) := (exp_dn 1 (1.0020020013340002 : ℝ))
  have h1 := tanh_le_of hu
  have h2 := le_tanh_of (by norm_num) hl
  have hθ : tanh ((1 / 1000 : ℚ) : ℝ) * kappa (15 : ℚ) ≤ ((261 / 500 : ℚ) : ℝ) := by
    rw [hk]
    calc tanh ((1 / 1000 : ℚ) : ℝ) * ((522 / 1 : ℚ) : ℝ)
        ≤ ((1.0020020013340003 : ℝ) ^ 1 - 1) / ((1.0020020013340003 : ℝ) ^ 1 + 1) * ((522 / 1 : ℚ) : ℝ) := by gcongr
      _ ≤ _ := by norm_num
  have hθ' : ((260999913 / 500000000 : ℚ) : ℝ) ≤ tanh ((1 / 1000 : ℚ) : ℝ) * kappa (15 : ℚ) := by
    rw [hk]
    calc ((260999913 / 500000000 : ℚ) : ℝ)
        ≤ ((1.0020020013340002 : ℝ) ^ 1 - 1) / ((1.0020020013340002 : ℝ) ^ 1 + 1) * ((522 / 1 : ℚ) : ℝ) := by norm_num
      _ ≤ _ := by gcongr
  exact ⟨hθ, rowG (1 / 1000) (15 : ℚ) (261 / 500) (260999913 / 500000000) 12 4
    (by norm_num) (by norm_num) hθ hθ' (by decide +kernel) (by decide +kernel) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)⟩

/-- **J8**, any `G`, row 2: `β = 1/100`, `z = 5`, `T_* = 20`, `θ = tanh(β) κ(z) ∈ [0.819972667759, 0.82]`. -/
theorem J8_G2 :
    tanh ((1 / 100 : ℚ) : ℝ) * kappa (5 : ℚ) ≤ ((41 / 50 : ℚ) : ℝ) ∧
    Datum 20 (5 : ℚ) ((1 - tanh ((1 / 100 : ℚ) : ℝ) * kappa (5 : ℚ)) / (K * ((1 / 100 : ℚ) : ℝ) * (5 : ℚ))) ∧
    ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < 20 →
      ¬ Datum T (5 : ℚ) ((1 - tanh ((1 / 100 : ℚ) : ℝ) * kappa (5 : ℚ)) / (K * ((1 / 100 : ℚ) : ℝ) * (5 : ℚ))) := by
  have hk : kappa (5 : ℚ) = ((82 / 1 : ℚ) : ℝ) := by norm_num [kappa]
  have hu : exp (2 * ((1 / 100 : ℚ) : ℝ)) ≤ (1.0202013400267559 : ℝ) ^ 1 := (exp_up 1 (1.0202013400267559 : ℝ))
  have hl : (1.0202013400267558 : ℝ) ^ 1 ≤ exp (2 * ((1 / 100 : ℚ) : ℝ)) := (exp_dn 1 (1.0202013400267558 : ℝ))
  have h1 := tanh_le_of hu
  have h2 := le_tanh_of (by norm_num) hl
  have hθ : tanh ((1 / 100 : ℚ) : ℝ) * kappa (5 : ℚ) ≤ ((41 / 50 : ℚ) : ℝ) := by
    rw [hk]
    calc tanh ((1 / 100 : ℚ) : ℝ) * ((82 / 1 : ℚ) : ℝ)
        ≤ ((1.0202013400267559 : ℝ) ^ 1 - 1) / ((1.0202013400267559 : ℝ) ^ 1 + 1) * ((82 / 1 : ℚ) : ℝ) := by gcongr
      _ ≤ _ := by norm_num
  have hθ' : ((819972667759 / 1000000000000 : ℚ) : ℝ) ≤ tanh ((1 / 100 : ℚ) : ℝ) * kappa (5 : ℚ) := by
    rw [hk]
    calc ((819972667759 / 1000000000000 : ℚ) : ℝ)
        ≤ ((1.0202013400267558 : ℝ) ^ 1 - 1) / ((1.0202013400267558 : ℝ) ^ 1 + 1) * ((82 / 1 : ℚ) : ℝ) := by norm_num
      _ ≤ _ := by gcongr
  exact ⟨hθ, rowG (1 / 100) (5 : ℚ) (41 / 50) (819972667759 / 1000000000000) 20 4
    (by norm_num) (by norm_num) hθ hθ' (by decide +kernel) (by decide +kernel) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)⟩

/-- **J8**, any `G`, row 3: `β = 1/50`, `z = 3`, `T_* = 32`, `θ = tanh(β) κ(z) ∈ [0.839888017917, 0.84]`. -/
theorem J8_G3 :
    tanh ((1 / 50 : ℚ) : ℝ) * kappa (3 : ℚ) ≤ ((21 / 25 : ℚ) : ℝ) ∧
    Datum 32 (3 : ℚ) ((1 - tanh ((1 / 50 : ℚ) : ℝ) * kappa (3 : ℚ)) / (K * ((1 / 50 : ℚ) : ℝ) * (3 : ℚ))) ∧
    ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < 32 →
      ¬ Datum T (3 : ℚ) ((1 - tanh ((1 / 50 : ℚ) : ℝ) * kappa (3 : ℚ)) / (K * ((1 / 50 : ℚ) : ℝ) * (3 : ℚ))) := by
  have hk : kappa (3 : ℚ) = ((42 / 1 : ℚ) : ℝ) := by norm_num [kappa]
  have hu : exp (2 * ((1 / 50 : ℚ) : ℝ)) ≤ (1.0408107741923883 : ℝ) ^ 1 := (exp_up 1 (1.0408107741923883 : ℝ))
  have hl : (1.0408107741923882 : ℝ) ^ 1 ≤ exp (2 * ((1 / 50 : ℚ) : ℝ)) := (exp_dn 1 (1.0408107741923882 : ℝ))
  have h1 := tanh_le_of hu
  have h2 := le_tanh_of (by norm_num) hl
  have hθ : tanh ((1 / 50 : ℚ) : ℝ) * kappa (3 : ℚ) ≤ ((21 / 25 : ℚ) : ℝ) := by
    rw [hk]
    calc tanh ((1 / 50 : ℚ) : ℝ) * ((42 / 1 : ℚ) : ℝ)
        ≤ ((1.0408107741923883 : ℝ) ^ 1 - 1) / ((1.0408107741923883 : ℝ) ^ 1 + 1) * ((42 / 1 : ℚ) : ℝ) := by gcongr
      _ ≤ _ := by norm_num
  have hθ' : ((839888017917 / 1000000000000 : ℚ) : ℝ) ≤ tanh ((1 / 50 : ℚ) : ℝ) * kappa (3 : ℚ) := by
    rw [hk]
    calc ((839888017917 / 1000000000000 : ℚ) : ℝ)
        ≤ ((1.0408107741923882 : ℝ) ^ 1 - 1) / ((1.0408107741923882 : ℝ) ^ 1 + 1) * ((42 / 1 : ℚ) : ℝ) := by norm_num
      _ ≤ _ := by gcongr
  exact ⟨hθ, rowG (1 / 50) (3 : ℚ) (21 / 25) (839888017917 / 1000000000000) 32 4
    (by norm_num) (by norm_num) hθ hθ' (by decide +kernel) (by decide +kernel) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)⟩

/-- **J8**, any `G`, row 4: `β = 1/25`, `z = 3/2`, `T_* = 100`, `θ = tanh(β) κ(z) ∈ [0.959488327467, 0.96]`. -/
theorem J8_G4 :
    tanh ((1 / 25 : ℚ) : ℝ) * kappa (3 / 2 : ℚ) ≤ ((24 / 25 : ℚ) : ℝ) ∧
    Datum 100 (3 / 2 : ℚ) ((1 - tanh ((1 / 25 : ℚ) : ℝ) * kappa (3 / 2 : ℚ)) / (K * ((1 / 25 : ℚ) : ℝ) * (3 / 2 : ℚ))) ∧
    ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < 100 →
      ¬ Datum T (3 / 2 : ℚ) ((1 - tanh ((1 / 25 : ℚ) : ℝ) * kappa (3 / 2 : ℚ)) / (K * ((1 / 25 : ℚ) : ℝ) * (3 / 2 : ℚ))) := by
  have hk : kappa (3 / 2 : ℚ) = ((24 / 1 : ℚ) : ℝ) := by norm_num [kappa]
  have hu : exp (2 * ((1 / 25 : ℚ) : ℝ)) ≤ (1.0832870676749586 : ℝ) ^ 1 := (exp_up 1 (1.0832870676749586 : ℝ))
  have hl : (1.0832870676749585 : ℝ) ^ 1 ≤ exp (2 * ((1 / 25 : ℚ) : ℝ)) := (exp_dn 1 (1.0832870676749585 : ℝ))
  have h1 := tanh_le_of hu
  have h2 := le_tanh_of (by norm_num) hl
  have hθ : tanh ((1 / 25 : ℚ) : ℝ) * kappa (3 / 2 : ℚ) ≤ ((24 / 25 : ℚ) : ℝ) := by
    rw [hk]
    calc tanh ((1 / 25 : ℚ) : ℝ) * ((24 / 1 : ℚ) : ℝ)
        ≤ ((1.0832870676749586 : ℝ) ^ 1 - 1) / ((1.0832870676749586 : ℝ) ^ 1 + 1) * ((24 / 1 : ℚ) : ℝ) := by gcongr
      _ ≤ _ := by norm_num
  have hθ' : ((959488327467 / 1000000000000 : ℚ) : ℝ) ≤ tanh ((1 / 25 : ℚ) : ℝ) * kappa (3 / 2 : ℚ) := by
    rw [hk]
    calc ((959488327467 / 1000000000000 : ℚ) : ℝ)
        ≤ ((1.0832870676749585 : ℝ) ^ 1 - 1) / ((1.0832870676749585 : ℝ) ^ 1 + 1) * ((24 / 1 : ℚ) : ℝ) := by norm_num
      _ ≤ _ := by gcongr
  exact ⟨hθ, rowG (1 / 25) (3 / 2 : ℚ) (24 / 25) (959488327467 / 1000000000000) 100 10
    (by norm_num) (by norm_num) hθ hθ' (by decide +kernel) (by decide +kernel) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)⟩

/-- **J8**, any `G`, row 5: `β = 1/20`, `z = 7/6`, `T_* = 316`, `θ = tanh(β) κ(z) ∈ [0.999167499157, 0.9992]`. -/
theorem J8_G5 :
    tanh ((1 / 20 : ℚ) : ℝ) * kappa (7 / 6 : ℚ) ≤ ((1249 / 1250 : ℚ) : ℝ) ∧
    Datum 316 (7 / 6 : ℚ) ((1 - tanh ((1 / 20 : ℚ) : ℝ) * kappa (7 / 6 : ℚ)) / (K * ((1 / 20 : ℚ) : ℝ) * (7 / 6 : ℚ))) ∧
    ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < 316 →
      ¬ Datum T (7 / 6 : ℚ) ((1 - tanh ((1 / 20 : ℚ) : ℝ) * kappa (7 / 6 : ℚ)) / (K * ((1 / 20 : ℚ) : ℝ) * (7 / 6 : ℚ))) := by
  have hk : kappa (7 / 6 : ℚ) = ((20 / 1 : ℚ) : ℝ) := by norm_num [kappa]
  have hu : exp (2 * ((1 / 20 : ℚ) : ℝ)) ≤ (1.1051709180756477 : ℝ) ^ 1 := (exp_up 1 (1.1051709180756477 : ℝ))
  have hl : (1.1051709180756476 : ℝ) ^ 1 ≤ exp (2 * ((1 / 20 : ℚ) : ℝ)) := (exp_dn 1 (1.1051709180756476 : ℝ))
  have h1 := tanh_le_of hu
  have h2 := le_tanh_of (by norm_num) hl
  have hθ : tanh ((1 / 20 : ℚ) : ℝ) * kappa (7 / 6 : ℚ) ≤ ((1249 / 1250 : ℚ) : ℝ) := by
    rw [hk]
    calc tanh ((1 / 20 : ℚ) : ℝ) * ((20 / 1 : ℚ) : ℝ)
        ≤ ((1.1051709180756477 : ℝ) ^ 1 - 1) / ((1.1051709180756477 : ℝ) ^ 1 + 1) * ((20 / 1 : ℚ) : ℝ) := by gcongr
      _ ≤ _ := by norm_num
  have hθ' : ((999167499157 / 1000000000000 : ℚ) : ℝ) ≤ tanh ((1 / 20 : ℚ) : ℝ) * kappa (7 / 6 : ℚ) := by
    rw [hk]
    calc ((999167499157 / 1000000000000 : ℚ) : ℝ)
        ≤ ((1.1051709180756476 : ℝ) ^ 1 - 1) / ((1.1051709180756476 : ℝ) ^ 1 + 1) * ((20 / 1 : ℚ) : ℝ) := by norm_num
      _ ≤ _ := by gcongr
  exact ⟨hθ, rowG (1 / 20) (7 / 6 : ℚ) (1249 / 1250) (999167499157 / 1000000000000) 316 26
    (by norm_num) (by norm_num) hθ hθ' (by decide +kernel) (by decide +kernel) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)⟩

/-- **J8**, any `G`, row 6: `β = 11/200`, `z = 203/200`, `T_* = 3914`, `θ = tanh(β) κ(z) ∈ [0.998892985969, 0.998893]`. -/
theorem J8_G6 :
    tanh ((11 / 200 : ℚ) : ℝ) * kappa (203 / 200 : ℚ) ≤ ((998893 / 1000000 : ℚ) : ℝ) ∧
    Datum 3914 (203 / 200 : ℚ) ((1 - tanh ((11 / 200 : ℚ) : ℝ) * kappa (203 / 200 : ℚ)) / (K * ((11 / 200 : ℚ) : ℝ) * (203 / 200 : ℚ))) ∧
    ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < 3914 →
      ¬ Datum T (203 / 200 : ℚ) ((1 - tanh ((11 / 200 : ℚ) : ℝ) * kappa (203 / 200 : ℚ)) / (K * ((11 / 200 : ℚ) : ℝ) * (203 / 200 : ℚ))) := by
  have hk : kappa (203 / 200 : ℚ) = ((909 / 50 : ℚ) : ℝ) := by norm_num [kappa]
  have hu : exp (2 * ((11 / 200 : ℚ) : ℝ)) ≤ (1.1162780704588713 : ℝ) ^ 1 := (exp_up 1 (1.1162780704588713 : ℝ))
  have hl : (1.1162780704588712 : ℝ) ^ 1 ≤ exp (2 * ((11 / 200 : ℚ) : ℝ)) := (exp_dn 1 (1.1162780704588712 : ℝ))
  have h1 := tanh_le_of hu
  have h2 := le_tanh_of (by norm_num) hl
  have hθ : tanh ((11 / 200 : ℚ) : ℝ) * kappa (203 / 200 : ℚ) ≤ ((998893 / 1000000 : ℚ) : ℝ) := by
    rw [hk]
    calc tanh ((11 / 200 : ℚ) : ℝ) * ((909 / 50 : ℚ) : ℝ)
        ≤ ((1.1162780704588713 : ℝ) ^ 1 - 1) / ((1.1162780704588713 : ℝ) ^ 1 + 1) * ((909 / 50 : ℚ) : ℝ) := by gcongr
      _ ≤ _ := by norm_num
  have hθ' : ((998892985969 / 1000000000000 : ℚ) : ℝ) ≤ tanh ((11 / 200 : ℚ) : ℝ) * kappa (203 / 200 : ℚ) := by
    rw [hk]
    calc ((998892985969 / 1000000000000 : ℚ) : ℝ)
        ≤ ((1.1162780704588712 : ℝ) ^ 1 - 1) / ((1.1162780704588712 : ℝ) ^ 1 + 1) * ((909 / 50 : ℚ) : ℝ) := by norm_num
      _ ≤ _ := by gcongr
  exact ⟨hθ, rowG (11 / 200) (203 / 200 : ℚ) (998893 / 1000000) (998892985969 / 1000000000000) 3914 268
    (by norm_num) (by norm_num) hθ hθ' (by decide +kernel) (by decide +kernel) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)⟩

/-- **J8**, `SU(2)`, row 1: `β = 1/10`, `z = 27/10`, `θ = βκ(z)/4 = 24/25`, `T_* = 40`. -/
theorem J8_SU2_1 :
    Datum 40 (27 / 10 : ℚ) ((1 - ((1 / 10 : ℚ) : ℝ) * kappa (27 / 10 : ℚ) / 4) / (K * ((1 / 10 : ℚ) : ℝ) * (27 / 10 : ℚ))) ∧
    ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < 40 →
      ¬ Datum T (27 / 10 : ℚ) ((1 - ((1 / 10 : ℚ) : ℝ) * kappa (27 / 10 : ℚ) / 4) / (K * ((1 / 10 : ℚ) : ℝ) * (27 / 10 : ℚ))) :=
  rowSU2 (1 / 10) (27 / 10 : ℚ) (24 / 25 : ℚ) 40 4 (by norm_num [kappa]) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

/-- **J8**, `SU(2)`, row 2: `β = 3/20`, `z = 5/3`, `θ = βκ(z)/4 = 39/40`, `T_* = 82`. -/
theorem J8_SU2_2 :
    Datum 82 (5 / 3 : ℚ) ((1 - ((3 / 20 : ℚ) : ℝ) * kappa (5 / 3 : ℚ) / 4) / (K * ((3 / 20 : ℚ) : ℝ) * (5 / 3 : ℚ))) ∧
    ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < 82 →
      ¬ Datum T (5 / 3 : ℚ) ((1 - ((3 / 20 : ℚ) : ℝ) * kappa (5 / 3 : ℚ) / 4) / (K * ((3 / 20 : ℚ) : ℝ) * (5 / 3 : ℚ))) :=
  rowSU2 (3 / 20) (5 / 3 : ℚ) (39 / 40 : ℚ) 82 8 (by norm_num [kappa]) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

/-- **J8**, `SU(2)`, row 3: `β = 1/5`, `z = 23/20`, `θ = βκ(z)/4 = 99/100`, `T_* = 342`. -/
theorem J8_SU2_3 :
    Datum 342 (23 / 20 : ℚ) ((1 - ((1 / 5 : ℚ) : ℝ) * kappa (23 / 20 : ℚ) / 4) / (K * ((1 / 5 : ℚ) : ℝ) * (23 / 20 : ℚ))) ∧
    ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < 342 →
      ¬ Datum T (23 / 20 : ℚ) ((1 - ((1 / 5 : ℚ) : ℝ) * kappa (23 / 20 : ℚ) / 4) / (K * ((1 / 5 : ℚ) : ℝ) * (23 / 20 : ℚ))) :=
  rowSU2 (1 / 5) (23 / 20 : ℚ) (99 / 100 : ℚ) 342 28 (by norm_num [kappa]) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

/-- **J8**, `SU(2)`, row 4: `β = 11/50`, `z = 203/200`, `θ = βκ(z)/4 = 9999/10000`, `T_* = 4188`. -/
theorem J8_SU2_4 :
    Datum 4188 (203 / 200 : ℚ) ((1 - ((11 / 50 : ℚ) : ℝ) * kappa (203 / 200 : ℚ) / 4) / (K * ((11 / 50 : ℚ) : ℝ) * (203 / 200 : ℚ))) ∧
    ∀ T : ℕ, T % 2 = 0 → 4 ≤ T → T < 4188 →
      ¬ Datum T (203 / 200 : ℚ) ((1 - ((11 / 50 : ℚ) : ℝ) * kappa (203 / 200 : ℚ) / 4) / (K * ((11 / 50 : ℚ) : ℝ) * (203 / 200 : ℚ))) :=
  rowSU2 (11 / 50) (203 / 200 : ℚ) (9999 / 10000 : ℚ) 4188 268 (by norm_num [kappa]) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

/-- **J8**, `(β, z) = (1/1000, 15)`: `T⁴ z^{-2⌊T/2⌋} ≤ L` at `T = 10` and `> L` at `T = 11`. -/
theorem J8_T10 :
    (10 : ℝ) ^ 4 / 15 ^ 10 ≤ (1 - tanh ((1 / 1000 : ℚ) : ℝ) * kappa (15 : ℚ)) / (K * ((1 / 1000 : ℚ) : ℝ) * (15 : ℚ)) ∧
    (1 - tanh ((1 / 1000 : ℚ) : ℝ) * kappa (15 : ℚ)) / (K * ((1 / 1000 : ℚ) : ℝ) * (15 : ℚ)) < (11 : ℝ) ^ 4 / 15 ^ 10 := by
  have hk : kappa (15 : ℚ) = ((522 : ℚ) : ℝ) := by norm_num [kappa]
  have hu : exp (2 * ((1 / 1000 : ℚ) : ℝ)) ≤ (1.0020020013340003 : ℝ) ^ 1 := (exp_up 1 (1.0020020013340003 : ℝ))
  have hl : (1.0020020013340002 : ℝ) ^ 1 ≤ exp (2 * ((1 / 1000 : ℚ) : ℝ)) := (exp_dn 1 (1.0020020013340002 : ℝ))
  have h1 := tanh_le_of hu
  have h2 := le_tanh_of (by norm_num) hl
  rw [hk]
  unfold K
  constructor
  · rw [le_div_iff₀ (by norm_num)]; norm_num at h1 ⊢; linarith
  · rw [div_lt_iff₀ (by norm_num)]; norm_num at h2 ⊢; linarith


/-! ## J9 -/

/-- The large-`N_c` condition at `T`. -/
def J9cond (N : ℕ) (β : ℚ) (T : ℕ) : Prop :=
  4255469568 * (N : ℚ) ^ 2 * β * (T : ℚ) ^ 4 * (36 * β / (1 - 12 * β)) ^ ((T - 3) / 2) ≤
    (((T - 3) / 2 : ℕ) : ℚ) + 1

instance (N : ℕ) (β : ℚ) (T : ℕ) : Decidable (J9cond N β T) := by unfold J9cond; infer_instance

/-- If the condition holds at `T₀` and `T₀ + 1` and `(T₀ + 2)⁴ α ≤ T₀⁴`, it holds for all
`T ≥ T₀`. -/
theorem J9_tail (N : ℕ) (β : ℚ) (T0 : ℕ) (hβ : 0 ≤ β) (hβ1 : 12 * β < 1) (h3 : 3 ≤ T0)
    (hr : ((T0 : ℚ) + 2) ^ 4 * (36 * β / (1 - 12 * β)) ≤ 1 * (T0 : ℚ) ^ 4)
    (h0 : J9cond N β T0) (h1 : J9cond N β (T0 + 1)) : ∀ T ≥ T0, J9cond N β T := by
  have hα : 0 ≤ 36 * β / (1 - 12 * β) := div_nonneg (by linarith) (by linarith)
  have step : ∀ T ≥ T0, J9cond N β T → J9cond N β (T + 2) := by
    intro T hT hc
    unfold J9cond at hc ⊢
    have hh : (T + 2 - 3) / 2 = (T - 3) / 2 + 1 := by omega
    rw [hh, pow_succ (36 * β / (1 - 12 * β))]
    have hr' := ratio_mono (s := (2 : ℚ)) (T0 := (T0 : ℚ)) (T := (T : ℚ)) (by norm_num) hα (by exact_mod_cast (by omega : 0 < T0))
      (by exact_mod_cast hT) hr
    have hK : 0 ≤ 4255469568 * (N : ℚ) ^ 2 * β * (36 * β / (1 - 12 * β)) ^ ((T - 3) / 2) := by
      positivity
    push_cast
    calc 4255469568 * (N : ℚ) ^ 2 * β * ((T : ℚ) + 2) ^ 4 *
          ((36 * β / (1 - 12 * β)) ^ ((T - 3) / 2) * (36 * β / (1 - 12 * β)))
        = (4255469568 * (N : ℚ) ^ 2 * β * (36 * β / (1 - 12 * β)) ^ ((T - 3) / 2)) *
          (((T : ℚ) + 2) ^ 4 * (36 * β / (1 - 12 * β))) := by ring
      _ ≤ (4255469568 * (N : ℚ) ^ 2 * β * (36 * β / (1 - 12 * β)) ^ ((T - 3) / 2)) *
          (1 * (T : ℚ) ^ 4) := mul_le_mul_of_nonneg_left hr' hK
      _ = 4255469568 * (N : ℚ) ^ 2 * β * (T : ℚ) ^ 4 * (36 * β / (1 - 12 * β)) ^ ((T - 3) / 2) := by
          ring
      _ ≤ (((T - 3) / 2 : ℕ) : ℚ) + 1 := hc
      _ ≤ (((T - 3) / 2 : ℕ) : ℚ) + 1 + 1 := by linarith
  have both : ∀ k : ℕ, J9cond N β (T0 + k) ∧ J9cond N β (T0 + k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have := step (T0 + k) (by omega) ih.1
      rwa [show T0 + k + 2 = T0 + (k + 1) + 1 by omega] at this
  intro T hT
  have := (both (T - T0)).1
  rwa [show T0 + (T - T0) = T by omega] at this

/-- **J9**: `N_c = 2`, `β = 1/480`, `T_* = 25`. -/
theorem J9_2_480 : (∀ T ≥ 25, J9cond 2 (1 / 480) T) ∧ ¬ J9cond 2 (1 / 480) 24 :=
  ⟨J9_tail 2 (1 / 480) 25 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 2`, `β = 1/192`, `T_* = 41`. -/
theorem J9_2_192 : (∀ T ≥ 41, J9cond 2 (1 / 192) T) ∧ ¬ J9cond 2 (1 / 192) 40 :=
  ⟨J9_tail 2 (1 / 192) 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 2`, `β = 1/96`, `T_* = 81`. -/
theorem J9_2_96 : (∀ T ≥ 81, J9cond 2 (1 / 96) T) ∧ ¬ J9cond 2 (1 / 96) 80 :=
  ⟨J9_tail 2 (1 / 96) 81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 2`, `β = 1/64`, `T_* = 199`. -/
theorem J9_2_64 : (∀ T ≥ 199, J9cond 2 (1 / 64) T) ∧ ¬ J9cond 2 (1 / 64) 198 :=
  ⟨J9_tail 2 (1 / 64) 199 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 3`, `β = 1/480`, `T_* = 27`. -/
theorem J9_3_480 : (∀ T ≥ 27, J9cond 3 (1 / 480) T) ∧ ¬ J9cond 3 (1 / 480) 26 :=
  ⟨J9_tail 3 (1 / 480) 27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 3`, `β = 1/192`, `T_* = 43`. -/
theorem J9_3_192 : (∀ T ≥ 43, J9cond 3 (1 / 192) T) ∧ ¬ J9cond 3 (1 / 192) 42 :=
  ⟨J9_tail 3 (1 / 192) 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 3`, `β = 1/96`, `T_* = 83`. -/
theorem J9_3_96 : (∀ T ≥ 83, J9cond 3 (1 / 96) T) ∧ ¬ J9cond 3 (1 / 96) 82 :=
  ⟨J9_tail 3 (1 / 96) 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 3`, `β = 1/64`, `T_* = 205`. -/
theorem J9_3_64 : (∀ T ≥ 205, J9cond 3 (1 / 64) T) ∧ ¬ J9cond 3 (1 / 64) 204 :=
  ⟨J9_tail 3 (1 / 64) 205 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 10`, `β = 1/480`, `T_* = 29`. -/
theorem J9_10_480 : (∀ T ≥ 29, J9cond 10 (1 / 480) T) ∧ ¬ J9cond 10 (1 / 480) 28 :=
  ⟨J9_tail 10 (1 / 480) 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 10`, `β = 1/192`, `T_* = 45`. -/
theorem J9_10_192 : (∀ T ≥ 45, J9cond 10 (1 / 192) T) ∧ ¬ J9cond 10 (1 / 192) 44 :=
  ⟨J9_tail 10 (1 / 192) 45 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 10`, `β = 1/96`, `T_* = 89`. -/
theorem J9_10_96 : (∀ T ≥ 89, J9cond 10 (1 / 96) T) ∧ ¬ J9cond 10 (1 / 96) 88 :=
  ⟨J9_tail 10 (1 / 96) 89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 10`, `β = 1/64`, `T_* = 219`. -/
theorem J9_10_64 : (∀ T ≥ 219, J9cond 10 (1 / 64) T) ∧ ¬ J9cond 10 (1 / 64) 218 :=
  ⟨J9_tail 10 (1 / 64) 219 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 1000000`, `β = 1/480`, `T_* = 47`. -/
theorem J9_1000000_480 : (∀ T ≥ 47, J9cond 1000000 (1 / 480) T) ∧ ¬ J9cond 1000000 (1 / 480) 46 :=
  ⟨J9_tail 1000000 (1 / 480) 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 1000000`, `β = 1/192`, `T_* = 77`. -/
theorem J9_1000000_192 : (∀ T ≥ 77, J9cond 1000000 (1 / 192) T) ∧ ¬ J9cond 1000000 (1 / 192) 76 :=
  ⟨J9_tail 1000000 (1 / 192) 77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 1000000`, `β = 1/96`, `T_* = 147`. -/
theorem J9_1000000_96 : (∀ T ≥ 147, J9cond 1000000 (1 / 96) T) ∧ ¬ J9cond 1000000 (1 / 96) 146 :=
  ⟨J9_tail 1000000 (1 / 96) 147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩

/-- **J9**: `N_c = 1000000`, `β = 1/64`, `T_* = 351`. -/
theorem J9_1000000_64 : (∀ T ≥ 351, J9cond 1000000 (1 / 64) T) ∧ ¬ J9cond 1000000 (1 / 64) 350 :=
  ⟨J9_tail 1000000 (1 / 64) 351 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel), by decide +kernel⟩


end YangMills.OneCube.Tables
