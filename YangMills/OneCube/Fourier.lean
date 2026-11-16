import Mathlib

/-!
# One-cube criteria: the sector-zero Fourier identity (check L10)

Let `N ≥ 1`, momenta `k ∈ (ℤ/N)³`, and let `Z : (ℤ/N)³ → ℝ` be the twisted partition
functions, symmetric under `k ↦ -k`, with `Z₀ ≠ 0` the untwisted one. The sector
weights are `w_e = N⁻³ Σ_k ω^{-e·k} Z(k)/Z₀`, `ω = e^{2πi/N}`, the image of the
projection `P_e = N⁻³ Σ_k ω^{-e·k} z^k` on the twisted traces. The identity
`w₀ - w_e = N⁻³ Σ_k (1 - cos(2π e·k/N)) Z(k)/Z₀` is a finite character identity;
`w₀ - w_e ≥ 0` follows when `Z ≥ 0`, `Z₀ > 0`. The operator facts that give
`Z(k) = Z(-k) > 0` are not part of this check.
-/

namespace YangMills.OneCube.Fourier

open Complex

variable {N : ℕ} [NeZero N]

/-- The pairing `e·k ∈ ℤ/N` on `(ℤ/N)³`. -/
def dot (e k : Fin 3 → ZMod N) : ZMod N := ∑ i, e i * k i

/-- `ω^{x}` for `x ∈ ℤ/N`, `ω = e^{2πi/N}`. -/
noncomputable def ω (x : ZMod N) : ℂ := (ZMod.toCircle x : ℂ)

theorem ω_apply (x : ZMod N) : ω x = Complex.exp (2 * Real.pi * I * x.val / N) :=
  ZMod.toCircle_apply x

/-- The sector weight `w_e`. -/
noncomputable def w (Z : (Fin 3 → ZMod N) → ℝ) (Z₀ : ℝ) (e : Fin 3 → ZMod N) : ℂ :=
  (1 / (N : ℂ) ^ 3) * ∑ k, ω (-dot e k) * ((Z k / Z₀ : ℝ) : ℂ)

omit [NeZero N] in
theorem dot_neg (e k : Fin 3 → ZMod N) : dot e (-k) = -dot e k := by
  simp [dot, Finset.sum_neg_distrib]

omit [NeZero N] in
theorem dot_zero (k : Fin 3 → ZMod N) : dot 0 k = 0 := by simp [dot]

theorem ω_neg_add (x : ZMod N) : ω (-x) + ω x = 2 * Real.cos (2 * Real.pi * x.val / N) := by
  have hinv : (ZMod.toCircle (-x) : ℂ) = (starRingEnd ℂ) (ZMod.toCircle x : ℂ) := by
    rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rw [ω, ω, hinv, add_comm, Complex.add_conj, ZMod.toCircle_apply]
  have : 2 * (Real.pi : ℂ) * I * (x.val : ℂ) / (N : ℂ) =
      ((2 * Real.pi * x.val / N : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]
  push_cast; ring

/-- **L10.** `w₀ - w_e = N⁻³ Σ_k (1 - cos(2π e·k/N)) Z(k)/Z₀`. -/
theorem L10 (Z : (Fin 3 → ZMod N) → ℝ) (Z₀ : ℝ) (hsym : ∀ k, Z (-k) = Z k)
    (e : Fin 3 → ZMod N) :
    w Z Z₀ 0 - w Z Z₀ e =
      (((1 / (N : ℝ) ^ 3) * ∑ k, (1 - Real.cos (2 * Real.pi * (dot e k).val / N)) * (Z k / Z₀) : ℝ) : ℂ) := by
  set c : (Fin 3 → ZMod N) → ℂ := fun k => ((Z k / Z₀ : ℝ) : ℂ) with hc
  have hrefl : ∑ k, ω (-dot e k) * c k = ∑ k, ω (dot e k) * c k := by
    rw [← Equiv.sum_comp (Equiv.neg _)]
    simp [hc, dot_neg, hsym]
  have hsum : ∑ k, ω (-dot e k) * c k =
      ∑ k, ((Real.cos (2 * Real.pi * (dot e k).val / N) : ℝ) : ℂ) * c k := by
    have h2 : 2 * ∑ k, ω (-dot e k) * c k =
        2 * ∑ k, ((Real.cos (2 * Real.pi * (dot e k).val / N) : ℝ) : ℂ) * c k := by
      calc 2 * ∑ k, ω (-dot e k) * c k
          = ∑ k, ω (-dot e k) * c k + ∑ k, ω (dot e k) * c k := by rw [hrefl]; ring
        _ = ∑ k, (ω (-dot e k) + ω (dot e k)) * c k := by
              rw [← Finset.sum_add_distrib]; simp [add_mul]
        _ = 2 * ∑ k, ((Real.cos (2 * Real.pi * (dot e k).val / N) : ℝ) : ℂ) * c k := by
              rw [Finset.mul_sum]; congr 1; ext k; rw [ω_neg_add]; ring
    exact mul_left_cancel₀ two_ne_zero h2
  simp only [w, dot_zero, neg_zero]
  rw [show ω (0 : ZMod N) = 1 by simp [ω], hsum]
  push_cast
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [hc]; ring

/-- Consequence (with L10 when `Z(-k) = Z(k)`): `w₀ - w_e ≥ 0` whenever all `Z(k) ≥ 0` and `Z₀ > 0`. -/
theorem L10_nonneg (Z : (Fin 3 → ZMod N) → ℝ) (Z₀ : ℝ)
    (hZ : ∀ k, 0 ≤ Z k) (hZ₀ : 0 < Z₀) (e : Fin 3 → ZMod N) :
    0 ≤ ((1 / (N : ℝ) ^ 3) * ∑ k, (1 - Real.cos (2 * Real.pi * (dot e k).val / N)) * (Z k / Z₀)) := by
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (by linarith [Real.cos_le_one (2 * Real.pi * (dot e k).val / N)])
    (div_nonneg (hZ k) hZ₀.le)

end YangMills.OneCube.Fourier
