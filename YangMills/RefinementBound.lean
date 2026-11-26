import Mathlib

/-!
# The refinement bound implies the pressure bound (Theorem `ly:thm:R`)

`X j b` stands for the thermal pressure of the box of side `T_* · 2^j` at
coupling `b`, and `ρ` for the two-loop reference map. The refinement bound
`(R)` is `X (j+1) b ≤ X j (ρ b) + 10⁻⁷ 2⁻ʲ` for `b > 1/3`. It is a hypothesis
here; this file proves what follows from it.

* `geom_sum_lt`: `Σ_{j<n} 10⁻⁷ 2⁻ʲ < 2 · 10⁻⁷`.
* `refine_chain`: along the rungs above `a`,
  `X n β ≤ X 0 (ρ^[n] β) + Σ_{j<n} ε j`.
* `refine_pressure`: with the certificate `X 0 b ≤ 3.36 · 10⁻⁵` on `[0, 1/3]`,
  `(R)` gives `X n β < 3.38 · 10⁻⁵ < 1/28684` at the end of the rungs.
-/

namespace YangMills.RefinementBound

/-- The allowance of the refinement bound at step `j`. -/
noncomputable def eps (j : ℕ) : ℝ := (1 / 10 ^ 7) * (1 / 2) ^ j

/-- `Σ_{j<n} 10⁻⁷ 2⁻ʲ < 2 · 10⁻⁷`. -/
theorem geom_sum_lt (n : ℕ) : ∑ j ∈ Finset.range n, eps j < 2 / 10 ^ 7 := by
  unfold eps
  rw [← Finset.mul_sum]
  have h := geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1) n
  rw [h]
  have hp : 0 < (1 / 2 : ℝ) ^ n := by positivity
  have : ((1 / 2 : ℝ) ^ n - 1) / (1 / 2 - 1) = 2 - 2 * (1 / 2) ^ n := by
    field_simp; ring
  rw [this]
  nlinarith

/-- **The refinement chain.** If `X (j+1) b ≤ X j (ρ b) + ε j` for `b > a`, and the
first `n` iterates of `ρ` from `β` stay above `a`, then
`X n β ≤ X 0 (ρ^[n] β) + Σ_{j<n} ε j`. -/
theorem refine_chain (X : ℕ → ℝ → ℝ) (ρ : ℝ → ℝ) (ε : ℕ → ℝ) (a : ℝ)
    (hR : ∀ j b, a < b → X (j + 1) b ≤ X j (ρ b) + ε j) :
    ∀ n β, (∀ k < n, a < ρ^[k] β) →
      X n β ≤ X 0 (ρ^[n] β) + ∑ j ∈ Finset.range n, ε j := by
  intro n
  induction n with
  | zero => intro β _; simp
  | succ n ih =>
    intro β hall
    have h1 := hR n β (hall 0 (Nat.succ_pos n))
    have h2 := ih (ρ β) (fun k hk => by
      have := hall (k + 1) (Nat.succ_lt_succ hk)
      rwa [Function.iterate_succ_apply] at this)
    rw [Finset.sum_range_succ, Function.iterate_succ_apply]
    linarith

/-- **The refinement bound gives `(P)`.** Assume `(R)` above `1/3` with the
allowance `eps`, and the box certificate `X 0 b ≤ 3.36 · 10⁻⁵` for
`0 ≤ b ≤ 1/3`. If the first `n` iterates stay above `1/3` and the `n`-th lies
in `[0, 1/3]`, then `X n β < 3.38 · 10⁻⁵ < 1/28684`. -/
theorem refine_pressure (X : ℕ → ℝ → ℝ) (ρ : ℝ → ℝ)
    (hR : ∀ j b, 1 / 3 < b → X (j + 1) b ≤ X j (ρ b) + eps j)
    (hC : ∀ b, 0 ≤ b → b ≤ 1 / 3 → X 0 b ≤ 336 / 10 ^ 7)
    (n : ℕ) (β : ℝ) (hall : ∀ k < n, 1 / 3 < ρ^[k] β)
    (hend0 : 0 ≤ ρ^[n] β) (hend : ρ^[n] β ≤ 1 / 3) :
    X n β < 338 / 10 ^ 7 ∧ (338 / 10 ^ 7 : ℝ) < 1 / 28684 := by
  have hc := refine_chain X ρ eps (1 / 3) hR n β hall
  have hs := geom_sum_lt n
  have hb := hC _ hend0 hend
  refine ⟨by linarith, by norm_num⟩

end YangMills.RefinementBound
