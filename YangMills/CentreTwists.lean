import Mathlib

/-!
# Centre twists: the finite and elementary steps

Finite and elementary parts of Subsection `ssec:twists` of the paper.

* `twist_ratio_bounds`, `twist_lower_eq` : the spectral step of Lemma `lem:twistdatum`. If the
  twisted trace is `1 + Σ εᵢ rᵢ^M` with `|εᵢ| ≤ 1`, `rᵢ ≥ 0`, and the untwisted one is
  `1 + D = e^X`, then the ratio lies in `[2e^{-X} − 1, 1]`.
* `datum_twist` : `X ≤ 1/8192` gives every twisted ratio `≥ 1 − 1/4096`.
* `peierls_series` : the geometric sum `Σ_{m ≥ M} (20e)^{m−1} u^m` of the proof of
  Proposition `prop:z2peierls`.
* `peierls_threshold_2127`, `peierls_threshold_2495`, `peierls_threshold_2023`,
  `peierls_threshold_2048` : the four thresholds of Proposition `prop:z2peierls`, for every
  torus size `T ≥ 2` (respectively `T ≥ 8`).
* `twistEater_commutator` : the commutators of the quaternions `1, i, k` used in Remark
  `rem:twisteater`; `iqk` and `kqi` are `−1`.
* `abelian_slice_cost` : the footnote of Remark `rem:twisteater`. If plaquette angles
  `φ_p ∈ [−π, π]` on a slice of `m` plaquettes sum to `π` modulo `2π`, then
  `Σ (1 − cos φ_p) ≥ 2/m`.
-/

open Real Finset

namespace YangMills.CentreTwists

/-! ## Lemma `lem:twistdatum` -/

/-- The spectral step of Lemma `lem:twistdatum`: with `D = Σ rᵢ`, `rᵢ ≥ 0` and `|εᵢ| ≤ 1`,
`(1 − D)/(1 + D) ≤ (1 + Σ εᵢ rᵢ)/(1 + D) ≤ 1`. -/
theorem twist_ratio_bounds {ι : Type*} (s : Finset ι) (r ε : ι → ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i) (hε : ∀ i ∈ s, |ε i| ≤ 1) :
    (1 - ∑ i ∈ s, r i) / (1 + ∑ i ∈ s, r i) ≤
        (1 + ∑ i ∈ s, ε i * r i) / (1 + ∑ i ∈ s, r i) ∧
      (1 + ∑ i ∈ s, ε i * r i) / (1 + ∑ i ∈ s, r i) ≤ 1 := by
  have hD : 0 ≤ ∑ i ∈ s, r i := sum_nonneg hr
  have hpos : 0 < 1 + ∑ i ∈ s, r i := by linarith
  have hup : ∑ i ∈ s, ε i * r i ≤ ∑ i ∈ s, r i := by
    apply sum_le_sum; intro i hi
    have := hε i hi; have := hr i hi
    nlinarith [le_abs_self (ε i)]
  have hlo : -∑ i ∈ s, r i ≤ ∑ i ∈ s, ε i * r i := by
    rw [← sum_neg_distrib]; apply sum_le_sum; intro i hi
    have := hε i hi; have := hr i hi
    nlinarith [neg_abs_le (ε i)]
  constructor
  · exact div_le_div_of_nonneg_right (by linarith) hpos.le
  · rw [div_le_one hpos]; linarith

/-- In Lemma `lem:twistdatum`, `(1 − D)/(1 + D) = 2/(1 + D) − 1 = 2e^{−X} − 1` when
`1 + D = e^X`. -/
theorem twist_lower_eq (D X : ℝ) (h : 1 + D = Real.exp X) :
    (1 - D) / (1 + D) = 2 * Real.exp (-X) - 1 := by
  have hp : 0 < 1 + D := h ▸ Real.exp_pos X
  rw [Real.exp_neg, ← h]
  field_simp
  ring

/-- `2e^{−x} − 1 ≥ 1 − 2x` for every real `x`. -/
theorem two_exp_neg_sub_one_ge (x : ℝ) : 1 - 2 * x ≤ 2 * Real.exp (-x) - 1 := by
  have := Real.add_one_le_exp (-x)
  linarith

/-- Lemma `lem:twistdatum`, last claim: if `X ≤ 1/8192` every twisted ratio bounded below by
`2e^{−X} − 1` is at least `1 − 1/4096`. -/
theorem datum_twist (X ρ : ℝ) (hX : X ≤ 1 / 8192) (hρ : 2 * Real.exp (-X) - 1 ≤ ρ) :
    1 - 1 / 4096 ≤ ρ := by
  have := two_exp_neg_sub_one_ge X
  linarith

/-! ## Proposition `prop:z2peierls` -/

/-- The geometric sum of the proof of Proposition `prop:z2peierls`: for `q = 20 e u < 1`,
`Σ_{k ≥ 0} (20e)^{M−1+k} u^{M+k} = u q^{M−1}/(1 − q)`. -/
theorem peierls_series (u : ℝ) (M : ℕ) (hu : 0 ≤ u) (hq : 20 * Real.exp 1 * u < 1) :
    HasSum (fun k : ℕ => (20 * Real.exp 1) ^ (M + k) * u ^ (M + 1 + k))
      (u * (20 * Real.exp 1 * u) ^ M / (1 - 20 * Real.exp 1 * u)) := by
  have hq0 : 0 ≤ 20 * Real.exp 1 * u := by positivity
  have h := (hasSum_geometric_of_lt_one hq0 hq).mul_left (u * (20 * Real.exp 1 * u) ^ M)
  have hfun : (fun k : ℕ => (20 * Real.exp 1) ^ (M + k) * u ^ (M + 1 + k)) =
      fun k => u * (20 * Real.exp 1 * u) ^ M * (20 * Real.exp 1 * u) ^ k := by
    funext k; rw [mul_pow, mul_pow, pow_add, pow_add, pow_add]; ring
  rw [hfun, div_eq_mul_inv]
  exact h

/-- The Peierls bound `24T² u (20eu)^{2T²−1}/(1 − 20eu)` of Proposition `prop:z2peierls`,
with `u = e^{−2K}`. -/
noncomputable def peierls (T : ℕ) (K : ℝ) : ℝ :=
  24 * (T : ℝ) ^ 2 * Real.exp (-2 * K) * (20 * Real.exp 1 * Real.exp (-2 * K)) ^ (2 * T ^ 2 - 1)
    / (1 - 20 * Real.exp 1 * Real.exp (-2 * K))

/-- The variable `q = 20 e u` with `u = e^{−2K}`. -/
noncomputable def q (K : ℝ) : ℝ := 20 * Real.exp 1 * Real.exp (-2 * K)

/-- In terms of `q`: the Peierls bound is `(6T²/(5e)) q^{2T²}/(1 − q)`. -/
theorem peierls_eq (T : ℕ) (hT : 1 ≤ T) (K : ℝ) :
    peierls T K = 6 * (T : ℝ) ^ 2 / (5 * Real.exp 1) * q K ^ (2 * T ^ 2) / (1 - q K) := by
  unfold peierls q
  have he := Real.exp_pos 1
  have h1 : 1 ≤ T ^ 2 := Nat.one_le_pow _ _ hT
  obtain ⟨n, hn⟩ : ∃ n, 2 * T ^ 2 = n + 1 := ⟨2 * T ^ 2 - 1, by omega⟩
  have hn' : 2 * T ^ 2 - 1 = n := by omega
  rw [hn, Nat.add_sub_cancel, pow_succ]
  field_simp
  ring

theorem q_pos (K : ℝ) : 0 < q K := by unfold q; positivity

/-- `q` decreases in `K`. -/
theorem q_anti {K K' : ℝ} (h : K ≤ K') : q K' ≤ q K := by
  unfold q
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.2 (by linarith)

/-- `x ↦ x^N/(1 − x)` is monotone on `[0, 1)`. -/
theorem pow_div_mono {x y : ℝ} (N : ℕ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    x ^ N / (1 - x) ≤ y ^ N / (1 - y) := by
  exact div_le_div₀ (pow_nonneg (hx.trans hxy) N) (pow_le_pow_left₀ hx hxy N) (by linarith)
    (by linarith)

/-- One step in `T`: if `((T+1)/T)² q^{4T+2} ≤ 1`, the Peierls bound does not increase. -/
theorem peierls_succ_le (T : ℕ) (hT : 1 ≤ T) (K : ℝ) (hq : q K < 1)
    (hr : ((T + 1 : ℝ) / T) ^ 2 * q K ^ (4 * T + 2) ≤ 1) :
    peierls (T + 1) K ≤ peierls T K := by
  rw [peierls_eq (T + 1) (by omega) K, peierls_eq T hT K]
  have hq0 := q_pos K
  have he := Real.exp_pos 1
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hexp : 2 * (T + 1) ^ 2 = 2 * T ^ 2 + (4 * T + 2) := by ring
  rw [hexp, pow_add]
  have h1q : 0 < 1 - q K := by linarith
  rw [div_le_div_iff_of_pos_right h1q]
  have key : 6 * ((T + 1 : ℕ) : ℝ) ^ 2 / (5 * Real.exp 1) * (q K ^ (2 * T ^ 2) * q K ^ (4 * T + 2))
      = (6 * (T : ℝ) ^ 2 / (5 * Real.exp 1) * q K ^ (2 * T ^ 2)) *
          (((T + 1 : ℝ) / T) ^ 2 * q K ^ (4 * T + 2)) := by
    push_cast; field_simp
  rw [key]
  have hA : 0 ≤ 6 * (T : ℝ) ^ 2 / (5 * Real.exp 1) * q K ^ (2 * T ^ 2) := by positivity
  calc _ ≤ (6 * (T : ℝ) ^ 2 / (5 * Real.exp 1) * q K ^ (2 * T ^ 2)) * 1 :=
        mul_le_mul_of_nonneg_left hr hA
    _ = _ := by ring

/-- The ratio `((T+1)/T)² q^{4T+2}` is at most its value at `T₀` for `T ≥ T₀`. -/
theorem ratio_le (T₀ T : ℕ) (hT₀ : 1 ≤ T₀) (hT : T₀ ≤ T) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    ((T + 1 : ℝ) / T) ^ 2 * x ^ (4 * T + 2) ≤ ((T₀ + 1 : ℝ) / T₀) ^ 2 * x ^ (4 * T₀ + 2) := by
  have h0 : (0 : ℝ) < T₀ := by exact_mod_cast hT₀
  have h1 : (T₀ : ℝ) ≤ T := by exact_mod_cast hT
  apply mul_le_mul _ (pow_le_pow_of_le_one hx hx1 (by omega)) (pow_nonneg hx _) (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  rw [div_le_div_iff₀ (by linarith) h0]
  nlinarith

/-- For `T ≥ T₀`, the Peierls bound at `T` is at most its value at `T₀`, provided the step ratio
at `T₀` is at most one. -/
theorem peierls_le_base (T₀ : ℕ) (hT₀ : 1 ≤ T₀) (K : ℝ) (hq : q K < 1)
    (hr : ((T₀ + 1 : ℝ) / T₀) ^ 2 * q K ^ (4 * T₀ + 2) ≤ 1) :
    ∀ T, T₀ ≤ T → peierls T K ≤ peierls T₀ K := by
  intro T hT
  induction T, hT using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    refine le_trans (peierls_succ_le n (by omega) K hq ?_) ih
    exact (ratio_le T₀ n hT₀ hn (q K) (q_pos K).le hq.le).trans hr

/-- The Taylor polynomial of degree seven of the exponential. -/
noncomputable def taylor7 (x : ℝ) : ℝ :=
  1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 + x ^ 7 / 5040

/-- A Taylor lower bound for the exponential: `Σ_{i<8} x^i/i! ≤ e^x` for `x ≥ 0`. -/
theorem exp_ge_taylor (x : ℝ) (hx : 0 ≤ x) : taylor7 x ≤ Real.exp x := by
  have := Real.sum_le_exp_of_nonneg hx 8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num at this
  unfold taylor7
  linarith

/-- Upper bound for `q(K)`: if `e^{2K} ≥ L > 0` then `q(K) ≤ 20 · 2.7182818286/L`. -/
theorem q_le_of_exp_ge (K L : ℝ) (hL : 0 < L) (h : L ≤ Real.exp (2 * K)) :
    q K ≤ 20 * 2.7182818286 / L := by
  unfold q
  have he := Real.exp_one_lt_d9
  have hE : Real.exp (-2 * K) = (Real.exp (2 * K))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [hE, div_eq_mul_inv]
  exact mul_le_mul (by linarith) (inv_anti₀ hL h) (by positivity) (by norm_num)

/-- `e^{4 + f} ≥ 2.7182818283⁴ · taylor7 f` for `f ≥ 0`. -/
theorem exp_four_add_ge (f : ℝ) (hf : 0 ≤ f) :
    2.7182818283 ^ 4 * taylor7 f ≤ Real.exp (4 + f) := by
  rw [Real.exp_add, show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  have h0 : 0 ≤ taylor7 f := by unfold taylor7; positivity
  exact mul_le_mul (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 4)
    (exp_ge_taylor f hf) h0 (by positivity)

/-- `q(K₀) ≤ Q` from `2K₀ = 4 + f` and a rational check. -/
theorem q_le_of_split (K f Q : ℝ) (hf : 0 ≤ f) (hK : 2 * K = 4 + f)
    (hQ : 20 * 2.7182818286 / (2.7182818283 ^ 4 * taylor7 f) ≤ Q) : q K ≤ Q := by
  have h0 : 0 < taylor7 f := by unfold taylor7; positivity
  refine le_trans (q_le_of_exp_ge K _ (by positivity) ?_) hQ
  rw [hK]; exact exp_four_add_ge f hf

/-- The bound in terms of rational data: if `q ≤ Q < 1` the Peierls bound at `T` is at most
`(6T²/(5 · 2.7182818283)) Q^{2T²}/(1 − Q)`. -/
theorem peierls_le_rat (T : ℕ) (hT : 1 ≤ T) (K Q : ℝ) (hqQ : q K ≤ Q) (hQ : Q < 1) :
    peierls T K ≤ 6 * (T : ℝ) ^ 2 / (5 * 2.7182818283) * (Q ^ (2 * T ^ 2) / (1 - Q)) := by
  rw [peierls_eq T hT K, mul_div_assoc]
  have he := Real.exp_one_gt_d9
  apply mul_le_mul _ (pow_div_mono _ (q_pos K).le hqQ hQ) (by
    have := q_pos K; have : q K < 1 := lt_of_le_of_lt hqQ hQ
    apply div_nonneg (by positivity) (by linarith)) (by positivity)
  apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)

/-- Proposition `prop:z2peierls`: for `K ≥ 2.127` and every `T ≥ 2` the Peierls bound is below
`1 − 1/4096`, and `20 e u < 1`. -/
theorem peierls_threshold_2127 (K : ℝ) (hK : 2.127 ≤ K) (T : ℕ) (hT : 2 ≤ T) :
    q K < 1 ∧ peierls T K < 1 - 1 / 4096 := by
  have hq0 : q 2.127 ≤ 0.77239 :=
    q_le_of_split 2.127 0.254 0.77239 (by norm_num) (by norm_num) (by unfold taylor7; norm_num)
  have hqK : q K ≤ 0.77239 := (q_anti hK).trans hq0
  refine ⟨by linarith, ?_⟩
  have hr : ((2 + 1 : ℝ) / 2) ^ 2 * q K ^ (4 * 2 + 2) ≤ 1 := by
    have := pow_le_pow_left₀ (q_pos K).le hqK 10
    nlinarith
  calc peierls T K ≤ peierls 2 K := peierls_le_base 2 (by norm_num) K (by linarith)
        (by exact_mod_cast hr) T hT
    _ ≤ 6 * ((2 : ℕ) : ℝ) ^ 2 / (5 * 2.7182818283) * (0.77239 ^ (2 * 2 ^ 2) / (1 - 0.77239)) :=
        peierls_le_rat 2 (by norm_num) K _ hqK (by norm_num)
    _ < 1 - 1 / 4096 := by norm_num

/-- Proposition `prop:z2peierls`: for `K ≥ 2.495` and every `T ≥ 2` the Peierls bound is at
most `10⁻³`. -/
theorem peierls_threshold_2495 (K : ℝ) (hK : 2.495 ≤ K) (T : ℕ) (hT : 2 ≤ T) :
    q K < 1 ∧ peierls T K ≤ 1e-3 := by
  have hq0 : q 2.495 ≤ 0.37 :=
    q_le_of_split 2.495 0.99 0.37 (by norm_num) (by norm_num) (by unfold taylor7; norm_num)
  have hqK : q K ≤ 0.37 := (q_anti hK).trans hq0
  refine ⟨by linarith, ?_⟩
  have hr : ((2 + 1 : ℝ) / 2) ^ 2 * q K ^ (4 * 2 + 2) ≤ 1 := by
    have := pow_le_pow_left₀ (q_pos K).le hqK 10
    nlinarith
  calc peierls T K ≤ peierls 2 K := peierls_le_base 2 (by norm_num) K (by linarith)
        (by exact_mod_cast hr) T hT
    _ ≤ 6 * ((2 : ℕ) : ℝ) ^ 2 / (5 * 2.7182818283) * (0.37 ^ (2 * 2 ^ 2) / (1 - 0.37)) :=
        peierls_le_rat 2 (by norm_num) K _ hqK (by norm_num)
    _ ≤ 1e-3 := by norm_num

/-- Proposition `prop:z2peierls`: for `T ≥ 8` the threshold `1 − 1/4096` is reached at
`K ≥ 2.023`. -/
theorem peierls_threshold_2023 (K : ℝ) (hK : 2.023 ≤ K) (T : ℕ) (hT : 8 ≤ T) :
    q K < 1 ∧ peierls T K < 1 - 1 / 4096 := by
  have hq0 : q 2.023 ≤ 0.95098 :=
    q_le_of_split 2.023 0.046 0.95098 (by norm_num) (by norm_num) (by unfold taylor7; norm_num)
  have hqK : q K ≤ 0.95098 := (q_anti hK).trans hq0
  refine ⟨by linarith, ?_⟩
  have hr : ((8 + 1 : ℝ) / 8) ^ 2 * q K ^ (4 * 8 + 2) ≤ 1 := by
    have h1 := pow_le_pow_left₀ (q_pos K).le hqK 34
    have h2 : (0.95098 : ℝ) ^ 34 ≤ 0.2 := by norm_num
    nlinarith
  calc peierls T K ≤ peierls 8 K := peierls_le_base 8 (by norm_num) K (by linarith)
        (by exact_mod_cast hr) T hT
    _ ≤ 6 * ((8 : ℕ) : ℝ) ^ 2 / (5 * 2.7182818283) * (0.95098 ^ (2 * 8 ^ 2) / (1 - 0.95098)) :=
        peierls_le_rat 8 (by norm_num) K _ hqK (by norm_num)
    _ < 1 - 1 / 4096 := by norm_num

/-- Proposition `prop:z2peierls`: for `T ≥ 8` the bound `10⁻³` is reached at `K ≥ 2.048`. -/
theorem peierls_threshold_2048 (K : ℝ) (hK : 2.048 ≤ K) (T : ℕ) (hT : 8 ≤ T) :
    q K < 1 ∧ peierls T K ≤ 1e-3 := by
  have hq0 : q 2.048 ≤ 0.9046 :=
    q_le_of_split 2.048 0.096 0.9046 (by norm_num) (by norm_num) (by unfold taylor7; norm_num)
  have hqK : q K ≤ 0.9046 := (q_anti hK).trans hq0
  refine ⟨by linarith, ?_⟩
  have hr : ((8 + 1 : ℝ) / 8) ^ 2 * q K ^ (4 * 8 + 2) ≤ 1 := by
    have h1 := pow_le_pow_left₀ (q_pos K).le hqK 34
    have h2 : (0.9046 : ℝ) ^ 34 ≤ 0.04 := by norm_num
    nlinarith
  calc peierls T K ≤ peierls 8 K := peierls_le_base 8 (by norm_num) K (by linarith)
        (by exact_mod_cast hr) T hT
    _ ≤ 6 * ((8 : ℕ) : ℝ) ^ 2 / (5 * 2.7182818283) * (0.9046 ^ (2 * 8 ^ 2) / (1 - 0.9046)) :=
        peierls_le_rat 8 (by norm_num) K _ hqK (by norm_num)
    _ ≤ 1e-3 := by norm_num

/-! ## Remark `rem:twisteater` -/

open Quaternion

/-- The unit quaternion `i`. -/
def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
/-- The unit quaternion `k`. -/
def qk : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

theorem qi_re : qi.re = 0 := rfl
theorem qi_imI : qi.imI = 1 := rfl
theorem qi_imJ : qi.imJ = 0 := rfl
theorem qi_imK : qi.imK = 0 := rfl
theorem qk_re : qk.re = 0 := rfl
theorem qk_imI : qk.imI = 0 := rfl
theorem qk_imJ : qk.imJ = 0 := rfl
theorem qk_imK : qk.imK = 1 := rfl

set_option linter.unusedSimpArgs false

/-- Componentwise evaluation of products of `1, i, k` and their conjugates. -/
macro "quat_eval" : tactic => `(tactic| (ext <;> simp only [Quaternion.re_mul,
  Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
  Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, qi_re, qi_imI, qi_imJ, qi_imK,
  qk_re, qk_imI, qk_imJ, qk_imK, Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg,
  Quaternion.imK_neg, Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
  Quaternion.imK_one] <;> norm_num))

theorem qi_mul_star : qi * star qi = 1 := by
  quat_eval
theorem qk_mul_star : qk * star qk = 1 := by
  quat_eval

theorem qi_inv : qi⁻¹ = star qi := inv_eq_of_mul_eq_one_right qi_mul_star
theorem qk_inv : qk⁻¹ = star qk := inv_eq_of_mul_eq_one_right qk_mul_star

/-- The commutator `A B A⁻¹ B⁻¹` of two quaternions. -/
noncomputable def comm (A B : ℍ[ℝ]) : ℍ[ℝ] := A * B * A⁻¹ * B⁻¹

/-- Remark `rem:twisteater`: on the values `1, i, k` the plaquette variable `A B A⁻¹ B⁻¹` is
`−1` exactly for the pairs `(i, k)` and `(k, i)`, and `1` otherwise, because `i` and `k`
anticommute. -/
theorem twistEater_commutator :
    comm qi qk = -1 ∧ comm qk qi = -1 ∧ comm qi qi = 1 ∧ comm qk qk = 1 ∧
    (∀ A : ℍ[ℝ], A ≠ 0 → comm A 1 = 1) ∧ (∀ B : ℍ[ℝ], B ≠ 0 → comm 1 B = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold comm; rw [qi_inv, qk_inv]; quat_eval
  · unfold comm; rw [qi_inv, qk_inv]; quat_eval
  · unfold comm; rw [qi_inv]; quat_eval
  · unfold comm; rw [qk_inv]; quat_eval
  · intro A hA
    unfold comm
    rw [mul_one, inv_one, mul_one, mul_inv_cancel₀ hA]
  · intro B hB
    unfold comm
    rw [one_mul, inv_one, mul_one, mul_inv_cancel₀ hB]

/-- `1 − cos φ ≥ 2φ²/π²` for `|φ| ≤ π` (Jordan's inequality at `φ/2`). -/
theorem one_sub_cos_ge (φ : ℝ) (h : |φ| ≤ π) : 2 * φ ^ 2 / π ^ 2 ≤ 1 - Real.cos φ := by
  have hπ := Real.pi_pos
  have hcos : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    rw [show φ = 2 * (φ / 2) by ring, Real.cos_two_mul, Real.cos_sq']
    ring_nf
  have habs : |φ / 2| ≤ π / 2 := by rw [abs_div, abs_two]; linarith
  have hs : 2 / π * |φ / 2| ≤ |Real.sin (φ / 2)| := by
    rcases le_total 0 (φ / 2) with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0
        (by rw [abs_of_nonneg h0] at habs; linarith))]
      exact Real.mul_le_sin h0 (by rw [abs_of_nonneg h0] at habs; exact habs)
    · have h0' : 0 ≤ -(φ / 2) := by linarith
      rw [abs_of_nonpos h0, abs_of_nonpos (by
        have := Real.sin_nonneg_of_nonneg_of_le_pi h0' (by rw [abs_of_nonpos h0] at habs; linarith)
        rw [Real.sin_neg] at this; linarith)]
      have := Real.mul_le_sin h0' (by rw [abs_of_nonpos h0] at habs; exact habs)
      rw [Real.sin_neg] at this; linarith
  have hsq : (2 / π * |φ / 2|) ^ 2 ≤ Real.sin (φ / 2) ^ 2 := by
    rw [← sq_abs (Real.sin _)]
    exact pow_le_pow_left₀ (by positivity) hs 2
  rw [hcos]
  have : (2 / π * |φ / 2|) ^ 2 = φ ^ 2 / π ^ 2 := by
    rw [mul_pow, sq_abs]; field_simp
  rw [this] at hsq
  have : 2 * φ ^ 2 / π ^ 2 = 2 * (φ ^ 2 / π ^ 2) := by ring
  linarith

/-- The footnote of Remark `rem:twisteater`: if angles `φ_p ∈ [−π, π]` over a slice of `m ≥ 1`
plaquettes sum to `π + 2πk` for an integer `k`, then `Σ (1 − cos φ_p) ≥ 2/m`. -/
theorem abelian_slice_cost {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (φ : ι → ℝ)
    (hφ : ∀ p ∈ S, |φ p| ≤ π) (k : ℤ) (hsum : ∑ p ∈ S, φ p = π + 2 * π * k) :
    2 / (S.card : ℝ) ≤ ∑ p ∈ S, (1 - Real.cos (φ p)) := by
  have hπ := Real.pi_pos
  have hm : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  -- `Σ |φ_p| ≥ π`
  have habs : π ≤ ∑ p ∈ S, |φ p| := by
    rcases le_or_gt 0 k with hk | hk
    · have : (0 : ℝ) ≤ k := by exact_mod_cast hk
      calc π ≤ π + 2 * π * k := by nlinarith
        _ = ∑ p ∈ S, φ p := hsum.symm
        _ ≤ ∑ p ∈ S, |φ p| := sum_le_sum fun p _ => le_abs_self _
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      calc π ≤ -(π + 2 * π * k) := by nlinarith
        _ = ∑ p ∈ S, -φ p := by rw [sum_neg_distrib, hsum]
        _ ≤ ∑ p ∈ S, |φ p| := sum_le_sum fun p _ => neg_le_abs _
  -- Cauchy–Schwarz
  have hcs : (∑ p ∈ S, |φ p|) ^ 2 ≤ S.card * ∑ p ∈ S, |φ p| ^ 2 := sq_sum_le_card_mul_sum_sq
  have hsq : π ^ 2 / S.card ≤ ∑ p ∈ S, φ p ^ 2 := by
    rw [div_le_iff₀ hm]
    have : ∑ p ∈ S, |φ p| ^ 2 = ∑ p ∈ S, φ p ^ 2 := by simp [sq_abs]
    rw [this] at hcs
    nlinarith [pow_le_pow_left₀ hπ.le habs 2]
  have hlow : ∑ p ∈ S, 2 * φ p ^ 2 / π ^ 2 ≤ ∑ p ∈ S, (1 - Real.cos (φ p)) :=
    sum_le_sum fun p hp => one_sub_cos_ge (φ p) (hφ p hp)
  have : ∑ p ∈ S, 2 * φ p ^ 2 / π ^ 2 = 2 / π ^ 2 * ∑ p ∈ S, φ p ^ 2 := by
    rw [mul_sum]; congr 1; funext p; ring
  rw [this] at hlow
  calc 2 / (S.card : ℝ) = 2 / π ^ 2 * (π ^ 2 / S.card) := by field_simp
    _ ≤ 2 / π ^ 2 * ∑ p ∈ S, φ p ^ 2 := by
        apply mul_le_mul_of_nonneg_left hsq; positivity
    _ ≤ _ := hlow

end YangMills.CentreTwists
