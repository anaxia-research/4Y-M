import Mathlib

/-!
# Two static sources and the compensation of flux

Finite and elementary parts of the section `sec:sources` of the paper.

* `holder_sector` : the Hölder step of Theorem `thm:PT`. If `c i k ≥ 0` has row and column
  sums at most `N`, then `∑ c i k · aᵢ^{1−θ} b_k^θ ≤ N (∑ aᵢ)^{1−θ} (∑ b_k)^θ` for `0 < θ < 1`.
* `pow_split`, `compensation_sector` : with `aᵢ = λᵢ^L`, `b_k = μ_k^L` and `θ = ℓ/L`, the
  same bound for `∑ c i k λᵢ^{L−ℓ} μ_k^ℓ`, which is the direct-sector bound
  `a(ℓ) ≤ N_c² Z₊^{1−s} Z₋^s` of Theorem `thm:PT`.
* `two_point`, `compensation_final` : the last step of Theorem `thm:PT`,
  `((1+ζ)/2)^{1−s}((1−ζ)/2)^s + ((1+ζ)/2)^s((1−ζ)/2)^{1−s} ≤ (1−ζ²)^{min(s,1−s)}`.
* `logconvex_sum` : the Cauchy–Schwarz step of Lemma `lem:logconvex`.
* `chi`, `sum_chi`, `chi_orth`, `fourier_inversion`, `twist_lower`, `twist_upper`,
  `flux_small`, `flux_zero_large` : Proposition `prop:fluxfree` (a)–(c) on `(ZMod 2)^m`.
* `twist_of_Ftw` : Proposition `prop:fluxfree` (d).
* `trace_sandwich` : the trace of `X ↦ A X B*` on matrices, used in Theorem `thm:gauss` (b).
* `sheet_expansion` : the expansion of Theorem `thm:sheet` (b).
* `datum_*`, `ascent_*`, `flux_*` : the constants of the corollaries `cor:datum`,
  `cor:ascent` and `cor:flux`.
-/

open Real Finset

namespace YangMills.TwoSources

/-! ## Theorem `thm:PT`: the Hölder step -/

/-- The Hölder step of Theorem `thm:PT`. Let `c i k ≥ 0` have all row sums and all column
sums at most `N`, and let `aᵢ, b_k ≥ 0`. For `0 < θ < 1`,
`∑ᵢ ∑ₖ c i k · aᵢ^{1−θ} · b_k^θ ≤ N · (∑ aᵢ)^{1−θ} · (∑ b_k)^θ`. -/
theorem holder_sector {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ι → κ → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) (N θ : ℝ) (hN : 0 ≤ N)
    (hc : ∀ i ∈ s, ∀ k ∈ t, 0 ≤ c i k) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ k ∈ t, 0 ≤ b k)
    (hrow : ∀ i ∈ s, ∑ k ∈ t, c i k ≤ N) (hcol : ∀ k ∈ t, ∑ i ∈ s, c i k ≤ N)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∑ i ∈ s, ∑ k ∈ t, c i k * (a i ^ (1 - θ) * b k ^ θ) ≤
      N * ((∑ i ∈ s, a i) ^ (1 - θ) * (∑ k ∈ t, b k) ^ θ) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hpq : (1 / (1 - θ)).HolderConjugate (1 / θ) :=
    Real.holderConjugate_one_div h1θ hθ0 (by ring)
  set f : ι × κ → ℝ := fun x => (c x.1 x.2 * a x.1) ^ (1 - θ) with hf
  set g : ι × κ → ℝ := fun x => (c x.1 x.2 * b x.2) ^ θ with hg
  have hf0 : ∀ x ∈ s ×ˢ t, 0 ≤ f x := fun x _ => rpow_nonneg (by
    have := Finset.mem_product.1 ‹x ∈ s ×ˢ t›
    exact mul_nonneg (hc _ this.1 _ this.2) (ha _ this.1)) _
  have hg0 : ∀ x ∈ s ×ˢ t, 0 ≤ g x := fun x _ => rpow_nonneg (by
    have := Finset.mem_product.1 ‹x ∈ s ×ˢ t›
    exact mul_nonneg (hc _ this.1 _ this.2) (hb _ this.2)) _
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (s ×ˢ t) hpq hf0 hg0
  -- the left side
  have hL : ∑ x ∈ s ×ˢ t, f x * g x =
      ∑ i ∈ s, ∑ k ∈ t, c i k * (a i ^ (1 - θ) * b k ^ θ) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => ?_
    have hc' := hc i hi k hk
    simp only [hf, hg]
    rw [mul_rpow hc' (ha i hi), mul_rpow hc' (hb k hk)]
    have : c i k ^ (1 - θ) * c i k ^ θ = c i k := by
      rw [← rpow_add' hc' (by ring_nf; norm_num)]; simp
    calc c i k ^ (1 - θ) * a i ^ (1 - θ) * (c i k ^ θ * b k ^ θ)
        = (c i k ^ (1 - θ) * c i k ^ θ) * (a i ^ (1 - θ) * b k ^ θ) := by ring
      _ = c i k * (a i ^ (1 - θ) * b k ^ θ) := by rw [this]
  -- the two factors
  have hF : (∑ x ∈ s ×ˢ t, f x ^ (1 / (1 - θ))) ^ (1 / (1 / (1 - θ))) ≤
      (N * ∑ i ∈ s, a i) ^ (1 - θ) := by
    have e : ∑ x ∈ s ×ˢ t, f x ^ (1 / (1 - θ)) = ∑ i ∈ s, a i * ∑ k ∈ t, c i k := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [hf, one_div]
      rw [rpow_rpow_inv (mul_nonneg (hc i hi k hk) (ha i hi)) h1θ.ne']; ring
    rw [e, one_div_one_div]
    apply rpow_le_rpow (sum_nonneg fun i hi => mul_nonneg (ha i hi)
      (sum_nonneg fun k hk => hc i hi k hk)) _ h1θ.le
    rw [Finset.mul_sum]
    exact sum_le_sum fun i hi => by
      rw [mul_comm N]; exact mul_le_mul_of_nonneg_left (hrow i hi) (ha i hi)
  have hG : (∑ x ∈ s ×ˢ t, g x ^ (1 / θ)) ^ (1 / (1 / θ)) ≤ (N * ∑ k ∈ t, b k) ^ θ := by
    have e : ∑ x ∈ s ×ˢ t, g x ^ (1 / θ) = ∑ k ∈ t, b k * ∑ i ∈ s, c i k := by
      rw [Finset.sum_product, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [hg, one_div]
      rw [rpow_rpow_inv (mul_nonneg (hc i hi k hk) (hb k hk)) hθ0.ne']; ring
    rw [e, one_div_one_div]
    apply rpow_le_rpow (sum_nonneg fun k hk => mul_nonneg (hb k hk)
      (sum_nonneg fun i hi => hc i hi k hk)) _ hθ0.le
    rw [Finset.mul_sum]
    exact sum_le_sum fun k hk => by
      rw [mul_comm N]; exact mul_le_mul_of_nonneg_left (hcol k hk) (hb k hk)
  have hA : 0 ≤ ∑ i ∈ s, a i := sum_nonneg ha
  have hB : 0 ≤ ∑ k ∈ t, b k := sum_nonneg hb
  have hprod : (N * ∑ i ∈ s, a i) ^ (1 - θ) * (N * ∑ k ∈ t, b k) ^ θ =
      N * ((∑ i ∈ s, a i) ^ (1 - θ) * (∑ k ∈ t, b k) ^ θ) := by
    rw [mul_rpow hN hA, mul_rpow hN hB]
    have : N ^ (1 - θ) * N ^ θ = N := by
      rw [← rpow_add' hN (by ring_nf; norm_num)]; simp
    calc N ^ (1 - θ) * (∑ i ∈ s, a i) ^ (1 - θ) * (N ^ θ * (∑ k ∈ t, b k) ^ θ)
        = (N ^ (1 - θ) * N ^ θ) * ((∑ i ∈ s, a i) ^ (1 - θ) * (∑ k ∈ t, b k) ^ θ) := by ring
      _ = _ := by rw [this]
  rw [← hL, ← hprod]
  refine hH.trans (mul_le_mul hF hG (rpow_nonneg (sum_nonneg fun x hx => rpow_nonneg (hg0 x hx) _) _)
    (rpow_nonneg (mul_nonneg hN hA) _))

/-- `λ^{L−ℓ} = (λ^L)^{1 − ℓ/L}` and `μ^ℓ = (μ^L)^{ℓ/L}` for `λ, μ ≥ 0` and `ℓ ≤ L`, `L > 0`. -/
theorem pow_split (x : ℝ) (hx : 0 ≤ x) (L ℓ : ℕ) (hL : 0 < L) (hℓ : ℓ ≤ L) :
    x ^ (L - ℓ) = (x ^ L) ^ (1 - (ℓ : ℝ) / L) ∧ x ^ ℓ = (x ^ L) ^ ((ℓ : ℝ) / L) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  constructor
  · rw [← rpow_natCast x L, ← rpow_mul hx, ← rpow_natCast]
    congr 1
    rw [Nat.cast_sub hℓ]; field_simp
  · rw [← rpow_natCast x L, ← rpow_mul hx, ← rpow_natCast]
    congr 1
    field_simp

/-- The direct-sector bound of Theorem `thm:PT`: for `0 < ℓ < L`, with eigenvalues
`λᵢ, μ_k ≥ 0` and overlaps `c i k ≥ 0` whose row and column sums are at most `N`,
`∑ c i k λᵢ^{L−ℓ} μ_k^ℓ ≤ N (∑ λᵢ^L)^{1−ℓ/L} (∑ μ_k^L)^{ℓ/L}`. -/
theorem compensation_sector {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ι → κ → ℝ)
    (lam : ι → ℝ) (mu : κ → ℝ) (N : ℝ) (hN : 0 ≤ N)
    (hc : ∀ i ∈ s, ∀ k ∈ t, 0 ≤ c i k) (hl : ∀ i ∈ s, 0 ≤ lam i) (hm : ∀ k ∈ t, 0 ≤ mu k)
    (hrow : ∀ i ∈ s, ∑ k ∈ t, c i k ≤ N) (hcol : ∀ k ∈ t, ∑ i ∈ s, c i k ≤ N)
    (L ℓ : ℕ) (hℓ0 : 0 < ℓ) (hℓL : ℓ < L) :
    ∑ i ∈ s, ∑ k ∈ t, c i k * (lam i ^ (L - ℓ) * mu k ^ ℓ) ≤
      N * ((∑ i ∈ s, lam i ^ L) ^ (1 - (ℓ : ℝ) / L) *
        (∑ k ∈ t, mu k ^ L) ^ ((ℓ : ℝ) / L)) := by
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le _) hℓL
  have hθ0 : 0 < (ℓ : ℝ) / L := div_pos (by exact_mod_cast hℓ0) (by exact_mod_cast hL)
  have hθ1 : (ℓ : ℝ) / L < 1 := by
    rw [div_lt_one (by exact_mod_cast hL)]; exact_mod_cast hℓL
  have key := holder_sector s t c (fun i => lam i ^ L) (fun k => mu k ^ L) N ((ℓ : ℝ) / L) hN hc
    (fun i hi => pow_nonneg (hl i hi) _) (fun k hk => pow_nonneg (hm k hk) _) hrow hcol hθ0 hθ1
  refine le_trans (le_of_eq ?_) key
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => ?_
  rw [(pow_split (lam i) (hl i hi) L ℓ hL hℓL.le).1, (pow_split (mu k) (hm k hk) L ℓ hL hℓL.le).2]

/-! ## Theorem `thm:PT`: the two-point bound -/

/-- `(1+ζ)^{1−θ}(1−ζ)^θ + (1+ζ)^θ(1−ζ)^{1−θ} ≤ 2(1−ζ²)^θ` for `0 ≤ ζ ≤ 1`, `0 ≤ θ ≤ 1/2`. -/
theorem two_point (ζ θ : ℝ) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) :
    (1 + ζ) ^ (1 - θ) * (1 - ζ) ^ θ + (1 + ζ) ^ θ * (1 - ζ) ^ (1 - θ) ≤
      2 * (1 - ζ ^ 2) ^ θ := by
  have hp : 0 ≤ 1 - ζ := by linarith
  have hq : 0 < 1 + ζ := by linarith
  have hsplit : (1 : ℝ) - θ = θ + (1 - 2 * θ) := by ring
  have e1 : (1 + ζ) ^ (1 - θ) = (1 + ζ) ^ θ * (1 + ζ) ^ (1 - 2 * θ) := by
    rw [hsplit, rpow_add hq]
  have e2 : (1 - ζ) ^ (1 - θ) = (1 - ζ) ^ θ * (1 - ζ) ^ (1 - 2 * θ) := by
    rw [hsplit, rpow_add' hp (by linarith)]
  have e3 : (1 + ζ) ^ θ * (1 - ζ) ^ θ = (1 - ζ ^ 2) ^ θ := by
    rw [← mul_rpow hq.le hp]; congr 1; ring
  have b1 : (1 + ζ) ^ (1 - 2 * θ) ≤ 1 + (1 - 2 * θ) * ζ :=
    rpow_one_add_le_one_add_mul_self (by linarith) (by linarith) (by linarith)
  have b2 : (1 - ζ) ^ (1 - 2 * θ) ≤ 1 + (1 - 2 * θ) * (-ζ) := by
    have := rpow_one_add_le_one_add_mul_self (s := -ζ) (p := 1 - 2 * θ) (by linarith)
      (by linarith) (by linarith)
    simpa [sub_eq_add_neg] using this
  have hw : 0 ≤ (1 - ζ ^ 2) ^ θ := rpow_nonneg (by nlinarith) _
  calc (1 + ζ) ^ (1 - θ) * (1 - ζ) ^ θ + (1 + ζ) ^ θ * (1 - ζ) ^ (1 - θ)
      = ((1 + ζ) ^ θ * (1 - ζ) ^ θ) * ((1 + ζ) ^ (1 - 2 * θ) + (1 - ζ) ^ (1 - 2 * θ)) := by
        rw [e1, e2]; ring
    _ = (1 - ζ ^ 2) ^ θ * ((1 + ζ) ^ (1 - 2 * θ) + (1 - ζ) ^ (1 - 2 * θ)) := by rw [e3]
    _ ≤ (1 - ζ ^ 2) ^ θ * 2 := by
        apply mul_le_mul_of_nonneg_left _ hw; linarith
    _ = 2 * (1 - ζ ^ 2) ^ θ := by ring

/-- The last inequality of Theorem `thm:PT`: with `Z_±/Z = (1 ± ζ)/2`, `0 ≤ ζ ≤ 1` and
`0 ≤ s ≤ 1`, `(Z₊/Z)^{1−s}(Z₋/Z)^s + (Z₊/Z)^s(Z₋/Z)^{1−s} ≤ (1 − ζ²)^{min(s, 1−s)}`. -/
theorem compensation_final (ζ s : ℝ) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ((1 + ζ) / 2) ^ (1 - s) * ((1 - ζ) / 2) ^ s + ((1 + ζ) / 2) ^ s * ((1 - ζ) / 2) ^ (1 - s) ≤
      (1 - ζ ^ 2) ^ (min s (1 - s)) := by
  have hp : 0 ≤ 1 - ζ := by linarith
  have hq : 0 ≤ 1 + ζ := by linarith
  have half : ∀ x y u v : ℝ, 0 ≤ x → 0 ≤ y → u + v = 1 →
      (x / 2) ^ u * (y / 2) ^ v = (x ^ u * y ^ v) / 2 := by
    intro x y u v hx hy huv
    rw [div_rpow hx (by norm_num), div_rpow hy (by norm_num)]
    have h2 : (2 : ℝ) ^ u * 2 ^ v = 2 := by rw [← rpow_add (by norm_num), huv, rpow_one]
    rw [div_mul_div_comm, h2]
  rw [half _ _ _ _ hq hp (by ring), half _ _ _ _ hq hp (by ring)]
  rcases le_total s (1 / 2) with h | h
  · rw [min_eq_left (by linarith)]
    have := two_point ζ s h0 h1 hs0 h
    linarith
  · rw [min_eq_right (by linarith)]
    have := two_point ζ (1 - s) h0 h1 (by linarith) (by linarith)
    rw [sub_sub_cancel] at this
    linarith

/-! ## Lemma `lem:logconvex` -/

/-- The Cauchy–Schwarz step of Lemma `lem:logconvex`: for `f(ℓ) = ∑ c r^ℓ q^{L−ℓ}` with
`c, r, q ≥ 0`, `f(ℓ)² ≤ f(ℓ − 1) f(ℓ + 1)`. -/
theorem logconvex_sum {ι : Type*} (s : Finset ι) (c r q : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hr : ∀ i ∈ s, 0 ≤ r i) (hq : ∀ i ∈ s, 0 ≤ q i) (n m : ℕ) :
    (∑ i ∈ s, c i * r i ^ (n + 1) * q i ^ (m + 1)) ^ 2 ≤
      (∑ i ∈ s, c i * r i ^ n * q i ^ (m + 2)) * ∑ i ∈ s, c i * r i ^ (n + 2) * q i ^ m := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro i hi; exact mul_nonneg (mul_nonneg (hc i hi) (pow_nonneg (hr i hi) _))
      (pow_nonneg (hq i hi) _)
  · intro i hi; exact mul_nonneg (mul_nonneg (hc i hi) (pow_nonneg (hr i hi) _))
      (pow_nonneg (hq i hi) _)
  · intro i _; exact le_of_eq (by ring)

/-! ## Proposition `prop:fluxfree`: twist sectors and electric flux on `(ZMod 2)^m` -/

section Flux

variable {m : ℕ}

/-- The pairing `e · z` on `(ZMod 2)^m`. -/
def dot (e z : Fin m → ZMod 2) : ZMod 2 := ∑ i, e i * z i

/-- The character `χ_e(z) = (−1)^{e·z}`. -/
def chi (e z : Fin m → ZMod 2) : ℝ := if dot e z = 0 then 1 else -1

theorem dot_add_right (e z w : Fin m → ZMod 2) : dot e (z + w) = dot e z + dot e w := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_add_left (e e' z : Fin m → ZMod 2) : dot (e + e') z = dot e z + dot e' z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_zero_left (z : Fin m → ZMod 2) : dot 0 z = 0 := by simp [dot]

theorem dot_zero_right (e : Fin m → ZMod 2) : dot e 0 = 0 := by simp [dot]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem chi_of_add (a b : ZMod 2) :
    (if a + b = 0 then (1 : ℝ) else -1) =
      (if a = 0 then (1 : ℝ) else -1) * (if b = 0 then 1 else -1) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [show (1 : ZMod 2) + 1 = 0 from rfl]

theorem chi_add_right (e z w : Fin m → ZMod 2) : chi e (z + w) = chi e z * chi e w := by
  unfold chi; rw [dot_add_right]; exact chi_of_add _ _

theorem chi_add_left (e e' z : Fin m → ZMod 2) : chi (e + e') z = chi e z * chi e' z := by
  unfold chi; rw [dot_add_left]; exact chi_of_add _ _

theorem chi_zero_left (z : Fin m → ZMod 2) : chi 0 z = 1 := by simp [chi, dot_zero_left]

theorem chi_zero_right (e : Fin m → ZMod 2) : chi e 0 = 1 := by simp [chi, dot_zero_right]

theorem chi_cases (e z : Fin m → ZMod 2) : chi e z = 1 ∨ chi e z = -1 := by
  unfold chi; split_ifs <;> simp

theorem abs_chi (e z : Fin m → ZMod 2) : |chi e z| = 1 := by
  rcases chi_cases e z with h | h <;> simp [h]

/-- For `e ≠ 0` some `δ` has `χ_e(δ) = −1`. -/
theorem exists_chi_neg (e : Fin m → ZMod 2) (he : e ≠ 0) : ∃ δ, chi e δ = -1 := by
  obtain ⟨j, hj⟩ : ∃ j, e j ≠ 0 := by
    by_contra h; push Not at h; exact he (funext h)
  refine ⟨Pi.single j 1, ?_⟩
  have hd : dot e (Pi.single j 1) = e j := by
    simp [dot, Pi.single_apply, Finset.sum_ite_eq']
  rcases zmod2_cases (e j) with h | h
  · exact absurd h hj
  · simp [chi, hd, h]

/-- Orthogonality: `∑_z χ_e(z) = 0` for `e ≠ 0`. -/
theorem sum_chi (e : Fin m → ZMod 2) (he : e ≠ 0) : ∑ z, chi e z = 0 := by
  obtain ⟨δ, hδ⟩ := exists_chi_neg e he
  have h : ∑ z, chi e z = ∑ z, chi e (z + δ) :=
    (Fintype.sum_equiv (Equiv.addRight δ) _ _ (fun z => rfl)).symm
  simp only [chi_add_right, hδ, mul_neg, mul_one, Finset.sum_neg_distrib] at h
  linarith

theorem card_vec : (Fintype.card (Fin m → ZMod 2) : ℝ) = 2 ^ m := by
  simp [ZMod.card]

/-- `∑_z χ_e(z) χ_{e'}(z) = 2^m [e = e']`. -/
theorem chi_orth (e e' : Fin m → ZMod 2) :
    ∑ z, chi e z * chi e' z = if e = e' then (2 : ℝ) ^ m else 0 := by
  simp_rw [← chi_add_left]
  split_ifs with h
  · subst h
    have : e + e = 0 := by funext i; simp [ZModModule.add_self]
    simp [this, chi_zero_left]
  · apply sum_chi
    intro h'
    apply h
    funext i
    have := congr_fun h' i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    rcases zmod2_cases (e i) with h1 | h1 <;> rcases zmod2_cases (e' i) with h2 | h2 <;>
      simp_all

variable (Ze : (Fin m → ZMod 2) → ℝ)

/-- The twisted partition function `Z_z = ∑_e χ_e(z) Z_e` (Proposition `prop:fluxfree` (a)). -/
def Zt (z : Fin m → ZMod 2) : ℝ := ∑ e, chi e z * Ze e

theorem Zt_zero : Zt Ze 0 = ∑ e, Ze e := by simp [Zt, chi_zero_right]

/-- Fourier inversion: `∑_z χ_e(z) Z_z = 2^m Z_e`. -/
theorem fourier_inversion (e : Fin m → ZMod 2) : ∑ z, chi e z * Zt Ze z = 2 ^ m * Ze e := by
  simp only [Zt, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ e', ∑ z, chi e z * (chi e' z * Ze e') = (∑ z, chi e z * chi e' z) * Ze e' := by
    intro e'; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun z _ => by ring
  simp_rw [this, chi_orth]
  simp

/-- Proposition `prop:fluxfree` (b), upper half: `Z_z ≤ Z`. -/
theorem twist_upper (hZ : ∀ e, 0 ≤ Ze e) (z : Fin m → ZMod 2) : Zt Ze z ≤ Zt Ze 0 := by
  rw [Zt_zero]
  exact Finset.sum_le_sum fun e _ => by
    rcases chi_cases e z with h | h <;> rw [h] <;> linarith [hZ e]

/-- Proposition `prop:fluxfree` (b), lower half: `Z_z ≥ 2 Z_0 − Z`, `Z_0` the weight of the
flux-free sector. -/
theorem twist_lower (hZ : ∀ e, 0 ≤ Ze e) (z : Fin m → ZMod 2) :
    2 * Ze 0 - Zt Ze 0 ≤ Zt Ze z := by
  rw [Zt_zero]
  unfold Zt
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), ← Finset.add_sum_erase _ _
    (Finset.mem_univ 0), chi_zero_left, one_mul]
  have : -∑ e ∈ Finset.univ.erase 0, Ze e ≤ ∑ e ∈ Finset.univ.erase 0, chi e z * Ze e := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun e _ => by
      rcases chi_cases e z with h | h <;> rw [h] <;> linarith [hZ e]
  linarith

/-- Proposition `prop:fluxfree` (c): if every nonzero twisted ratio is at least `1 − η`, every
nonzero electric-flux weight is at most `η/2` of the total. -/
theorem flux_small (hZ : ∀ e, 0 ≤ Ze e) (η : ℝ) (hη : 0 ≤ η)
    (h : ∀ z, z ≠ 0 → (1 - η) * Zt Ze 0 ≤ Zt Ze z) (e : Fin m → ZMod 2) (he : e ≠ 0) :
    Ze e ≤ η / 2 * Zt Ze 0 := by
  set Z := Zt Ze 0
  have hZnn : 0 ≤ Z := by
    show 0 ≤ Zt Ze 0
    rw [Zt_zero]; exact Finset.sum_nonneg fun e _ => hZ e
  have inv := fourier_inversion Ze e
  have hs := sum_chi e he
  -- subtract (1 − η) Z ∑ χ = 0
  have h1 : ∑ z, chi e z * Zt Ze z = ∑ z, chi e z * (Zt Ze z - (1 - η) * Z) := by
    have : ∑ z, chi e z * (Zt Ze z - (1 - η) * Z) =
        ∑ z, chi e z * Zt Ze z - (1 - η) * Z * ∑ z, chi e z := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [this, hs]; ring
  -- termwise bound
  have h2 : ∀ z, chi e z * (Zt Ze z - (1 - η) * Z) ≤ (1 + chi e z) / 2 * (η * Z) := by
    intro z
    have up : Zt Ze z - (1 - η) * Z ≤ η * Z := by
      have := twist_upper Ze hZ z; linarith
    have lo : 0 ≤ Zt Ze z - (1 - η) * Z := by
      by_cases hz : z = 0
      · subst hz; nlinarith
      · linarith [h z hz]
    rcases chi_cases e z with hc | hc <;> rw [hc] <;> nlinarith
  have h3 : ∑ z, (1 + chi e z) / 2 * (η * Z) = 2 ^ m / 2 * (η * Z) := by
    rw [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib, hs]
    simp
  have h4 : 2 ^ m * Ze e ≤ 2 ^ m / 2 * (η * Z) := by
    rw [← inv, h1, ← h3]; exact Finset.sum_le_sum fun z _ => h2 z
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have : Ze e ≤ (η * Z) / 2 := by
    have := (mul_le_mul_iff_of_pos_left h2m).1 (by
      calc 2 ^ m * Ze e ≤ 2 ^ m / 2 * (η * Z) := h4
        _ = 2 ^ m * ((η * Z) / 2) := by ring)
    exact this
  linarith

/-- Proposition `prop:fluxfree` (c), second half: the flux-free weight is at least
`(1 − (1 − 2^{−m}) η) Z`. -/
theorem flux_zero_large (η : ℝ) (h : ∀ z, z ≠ 0 → (1 - η) * Zt Ze 0 ≤ Zt Ze z) :
    (1 - (1 - 1 / 2 ^ m) * η) * Zt Ze 0 ≤ Ze 0 := by
  have inv := fourier_inversion Ze 0
  simp only [chi_zero_left, one_mul] at inv
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)] at inv
  have hsum : ((2 : ℝ) ^ m - 1) * ((1 - η) * Zt Ze 0) ≤
      ∑ z ∈ Finset.univ.erase 0, Zt Ze z := by
    have hc : ((Finset.univ.erase (0 : Fin m → ZMod 2)).card : ℝ) = 2 ^ m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Nat.cast_sub
        (Finset.card_pos.2 ⟨0, Finset.mem_univ _⟩), Finset.card_univ, card_vec]
      simp
    rw [← hc, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun z hz => h z (Finset.ne_of_mem_erase hz)
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have key : 2 ^ m * ((1 - (1 - 1 / 2 ^ m) * η) * Zt Ze 0) ≤ 2 ^ m * Ze 0 := by
    have e : 2 ^ m * ((1 - (1 - 1 / 2 ^ m) * η) * Zt Ze 0) =
        Zt Ze 0 + ((2 : ℝ) ^ m - 1) * ((1 - η) * Zt Ze 0) := by
      field_simp; ring
    rw [e, ← inv]; linarith
  exact le_of_mul_le_mul_left key h2m

/-- Proposition `prop:fluxfree` (d): if `Z ≤ e^φ Z_0`, every twisted ratio is at least
`2e^{−φ} − 1`. -/
theorem twist_of_Ftw (hZ : ∀ e, 0 ≤ Ze e) (φ : ℝ)
    (h : Zt Ze 0 ≤ Real.exp φ * Ze 0) (z : Fin m → ZMod 2) :
    (2 * Real.exp (-φ) - 1) * Zt Ze 0 ≤ Zt Ze z := by
  have h1 := twist_lower Ze hZ z
  have h2 : Real.exp (-φ) * Zt Ze 0 ≤ Ze 0 := by
    have := mul_le_mul_of_nonneg_left h (Real.exp_pos (-φ)).le
    rwa [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at this
  nlinarith

end Flux

/-! ## Theorem `thm:gauss` (b): the trace of `X ↦ A X B*` -/

/-- The trace on `M_N(ℂ)` of `X ↦ A X B*`, computed in the basis of matrix units, is
`Tr A · conj(Tr B)`. -/
theorem trace_sandwich {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    ∑ a, ∑ b, (A * Matrix.single a b (1 : ℂ) * B.conjTranspose : Matrix n n ℂ) a b =
      A.trace * star B.trace := by
  have h : ∀ a b, (A * Matrix.single a b (1 : ℂ) * B.conjTranspose : Matrix n n ℂ) a b =
      A a a * star (B b b) := by
    intro a b
    rw [Matrix.mul_apply]
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and,
      Finset.sum_ite_eq, ite_mul]
  simp_rw [h, Matrix.trace, Matrix.diag, star_sum, Finset.sum_mul_sum]

/-! ## Theorem `thm:sheet` (b): the expansion in sheets -/

/-- `∏_p (w₊(U_p) + ζ_p w₋(U_p)) = ∑_{S ⊆ P} (∏_{p ∈ S} ζ_p w₋(U_p)) ∏_{p ∉ S} w₊(U_p)`. -/
theorem sheet_expansion {ι : Type*} [DecidableEq ι] (P : Finset ι) (wp wm ζ : ι → ℝ) :
    ∏ p ∈ P, (wp p + ζ p * wm p) =
      ∑ S ∈ P.powerset, (∏ p ∈ S, ζ p * wm p) * ∏ p ∈ P \ S, wp p := by
  rw [← Finset.prod_add]
  exact Finset.prod_congr rfl fun p _ => by ring

/-! ## Constants of the corollaries `cor:datum`, `cor:ascent`, `cor:flux` -/

/-- `1 − (1 − 1/4096)² ≤ 1/2048`. -/
theorem datum_one_sub_sq : 1 - (1 - (1 : ℝ) / 4096) ^ 2 ≤ 1 / 2048 := by norm_num

/-- `1 − ζ² ≤ 2(1 − ζ)` for `ζ ≤ 1`. -/
theorem one_sub_sq_le (ζ : ℝ) (h1 : ζ ≤ 1) : 1 - ζ ^ 2 ≤ 2 * (1 - ζ) := by
  nlinarith

/-- The vortex free energy in `cor:datum` (a): `−log(1 − 1/4096) ≤ 1/4095`. -/
theorem datum_vortex : -Real.log (1 - 1 / 4096) ≤ (1 : ℝ) / 4095 := by
  have h := Real.one_sub_inv_le_log_of_pos (x := (1 : ℝ) - 1 / 4096) (by norm_num)
  have : (1 : ℝ) - (1 - 1 / 4096)⁻¹ = -(1 / 4095) := by norm_num
  linarith

/-- `cor:datum` (b): `4/√2048 ≤ 0.08839` and `2/√2048 ≤ 0.04420`. -/
theorem datum_antipodal :
    4 * Real.sqrt (1 / 2048) ≤ 0.08839 ∧ 2 * Real.sqrt (1 / 2048) ≤ 0.04420 := by
  have hs : Real.sqrt (1 / 2048) ≤ 0.0220975 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  constructor <;> linarith

/-- `cor:datum` (b): the static-pair free energy `½ log 2048 − log 4 = (7/2) log 2 ≥ 2.4260`. -/
theorem datum_pair_free_energy :
    (2.4260 : ℝ) ≤ (1 / 2) * Real.log 2048 - Real.log 4 := by
  have h2048 : Real.log 2048 = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]; norm_num
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [h2048, h4]
  have := Real.log_two_gt_d9
  linarith

/-- `cor:datum` (c): `e^{1/8192} − 1 < 1/8191`. -/
theorem datum_flux_sum : Real.exp (1 / 8192) - 1 < 1 / 8191 := by
  have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 8192) (by norm_num) (by norm_num)
  have e : (1 : ℝ) / (1 - 1 / 8192) = 1 + 1 / 8191 := by norm_num
  linarith

/-- `cor:datum` (c): `log 8191 > 9.0107`. -/
theorem datum_flux_log : (9.0107 : ℝ) < Real.log 8191 := by
  have h1 : Real.log 8191 = Real.log 8192 + Real.log (8191 / 8192) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 : Real.log 8192 = 13 * Real.log 2 := by
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]; norm_num
  have h3 := Real.one_sub_inv_le_log_of_pos (x := (8191 : ℝ) / 8192) (by norm_num)
  have := Real.log_two_gt_d9
  rw [h1, h2]
  have e : (1 : ℝ) - (8191 / 8192)⁻¹ = -(1 / 8191) := by norm_num
  linarith

/-- `cor:ascent` (a): `(1 − D)/(1 + D) ≥ 1 − 2D` for `D ≥ 0`. -/
theorem ascent_ratio (D : ℝ) (hD : 0 ≤ D) : 1 - 2 * D ≤ (1 - D) / (1 + D) := by
  rw [le_div_iff₀ (by linarith)]; nlinarith

/-- `cor:ascent` (b): `4 √(x²/1024) = x/8` for `x ≥ 0`, with `x = u^{2^{i−1}}`. -/
theorem ascent_sqrt (x : ℝ) (hx : 0 ≤ x) : 4 * Real.sqrt (x ^ 2 / 1024) = x / 8 := by
  have : x ^ 2 / 1024 = (x / 32) ^ 2 := by ring
  rw [this, Real.sqrt_sq (by positivity)]; ring

/-- `cor:ascent` (b): `x₀ = 1/8192 < u/4096` with `u = 32/63`. -/
theorem ascent_start : (1 : ℝ) / 8192 < (32 / 63) / 4096 := by norm_num

/-- `cor:flux`: at `η = 1/7169`, `(7/8) η ≤ 1 − e^{−1/8192}`, so `F_tw ≤ 1/8192`. -/
theorem flux_eta : (7 / 8) * ((1 : ℝ) / 7169) ≤ 1 - Real.exp (-(1 / 8192)) := by
  have h := Real.add_one_le_exp (1 / 8192 : ℝ)
  have hpos := Real.exp_pos (1 / 8192 : ℝ)
  have e : Real.exp (-(1 / 8192)) = 1 / Real.exp (1 / 8192) := by
    rw [Real.exp_neg]; simp
  rw [e]
  have : 1 / Real.exp (1 / 8192) ≤ 1 / (1 / 8192 + 1) :=
    one_div_le_one_div_of_le (by norm_num) h
  have : (1 : ℝ) / (1 / 8192 + 1) = 8192 / 8193 := by norm_num
  linarith

/-- `cor:flux`: `F_e ≥ log(2/η − 7/4) = log 14336.25 > 9.56` at `η = 1/7169`. -/
theorem flux_Fe : 2 / ((1 : ℝ) / 7169) - 7 / 4 = 14336.25 ∧ (9.56 : ℝ) < Real.log 14336.25 := by
  refine ⟨by norm_num, ?_⟩
  have h1 : Real.log 14336.25 = Real.log 16384 + Real.log (14336.25 / 16384) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 : Real.log 16384 = 14 * Real.log 2 := by
    rw [show (16384 : ℝ) = 2 ^ 14 by norm_num, Real.log_pow]; norm_num
  have h3 := Real.one_sub_inv_le_log_of_pos (x := (14336.25 : ℝ) / 16384) (by norm_num)
  have := Real.log_two_gt_d9
  rw [h1, h2]
  have e : (1 : ℝ) - (14336.25 / 16384)⁻¹ ≥ -0.1429 := by norm_num
  linarith

/-- `cor:flux`: the antipodal bound `4 √(2/7169) ≤ 0.066812`. -/
theorem flux_antipodal : 4 * Real.sqrt (2 / 7169) ≤ 0.066812 := by
  have hs : Real.sqrt (2 / 7169) ≤ 0.016703 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

end YangMills.TwoSources
