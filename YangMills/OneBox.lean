import Mathlib
import YangMills.Ledger

/-!
# The one-box reduction (Subsection `ly:sec:ladder`)

Abstract form of the one-box reduction. `X m β` stands for the normalised
thermal pressure of the datum torus of side `T_* · 2^m` at coupling `β`; the
ladder ends on the single box `m = 0`.

* `gap_of_pressure`: a small pressure bounds the first excitation energy,
  `T E₁ ≥ log (1/(e^x - 1))` (Lemma `ly:lem:pressuregap`).
* `onebox_bound`: the box certificate and the endpoint condition give the
  pressure bound at the top (Theorem `ly:thm:onebox`).
* `onebox_gap`: under the same hypotheses the large box has
  `T E₁ ≥ log (1/(e^x - 1))`.
* `ref_iterate_le`, `onebox_size`: the number of rungs and the side,
  `2^n < 2 N e^{(C+D-β_top)/c₁}`.
* `orb_drop`, `barrier_chain`, `barrier_gap`: a uniform drop on a window ends
  the matched orbit in the band within `j` rungs, and the resulting pressure
  bound is a lower bound on the gap (Theorem `ly:thm:barrier`).
-/

open Real

namespace YangMills.OneBox

/-- **The pressure bounds the gap.** If `log (1 + e^{-t}) ≤ X ≤ x`,
then `t ≥ log (1/(e^x - 1))`; here `t = T E₁`. -/
theorem gap_of_pressure (t x X : ℝ)
    (hlow : Real.log (1 + Real.exp (-t)) ≤ X) (hX : X ≤ x) :
    Real.log (1 / (Real.exp x - 1)) ≤ t := by
  have hpos : 0 < 1 + Real.exp (-t) := by positivity
  have h1 : 1 + Real.exp (-t) ≤ Real.exp x := by
    have := Real.exp_le_exp.mpr (hlow.trans hX)
    rwa [Real.exp_log hpos] at this
  have hex : 0 < Real.exp (-t) := Real.exp_pos _
  have h2 : Real.exp (-t) ≤ Real.exp x - 1 := by linarith
  have h3 : 0 < Real.exp x - 1 := by linarith
  rw [one_div, Real.log_inv, neg_le]
  have := Real.log_le_log hex h2
  rwa [Real.log_exp] at this

/-- **The one-box bound.** If the pressure of the box is continuous, the box
certificate holds on `[0, β_top]`, and the `n`-fold matched coupling exists and
is at most `β_top`, then the pressure of the large box is at most `x`. -/
theorem onebox_bound (X : ℕ → ℝ → ℝ) (hcont : ContinuousOn (X 0) (Set.Ici 0))
    (x βtop : ℝ) (hC : ∀ b, 0 ≤ b → b ≤ βtop → X 0 b ≤ x) (n : ℕ) (β : ℝ)
    (hne : ({b | 0 ≤ b ∧ X n β ≤ X 0 b} : Set ℝ).Nonempty)
    (hE : sInf {b | 0 ≤ b ∧ X n β ≤ X 0 b} ≤ βtop) :
    X n β ≤ x := by
  have hm := YangMills.Ledger.matched_mem (X 0) hcont (X n β) hne
  exact hm.2.trans (hC _ hm.1 hE)

/-- **One box bounds the gap of the large box.** Under the box certificate
and the endpoint condition, the first excitation energy `E₁` of the box of
side `T_* · 2^n` satisfies `T E₁ ≥ log (1/(e^x - 1))`, where `t = T E₁` and
`log (1 + e^{-t}) ≤ X n β` is the lemma that the pressure bounds the gap. -/
theorem onebox_gap (X : ℕ → ℝ → ℝ) (hcont : ContinuousOn (X 0) (Set.Ici 0))
    (x βtop : ℝ) (hC : ∀ b, 0 ≤ b → b ≤ βtop → X 0 b ≤ x) (n : ℕ) (β : ℝ)
    (hne : ({b | 0 ≤ b ∧ X n β ≤ X 0 b} : Set ℝ).Nonempty)
    (hE : sInf {b | 0 ≤ b ∧ X n β ≤ X 0 b} ≤ βtop) (t : ℝ)
    (hlow : Real.log (1 + Real.exp (-t)) ≤ X n β) :
    Real.log (1 / (Real.exp x - 1)) ≤ t :=
  gap_of_pressure t x (X n β) hlow (onebox_bound X hcont x βtop hC n β hne hE)

/-- The endpoint condition `R^{♯(n)} ≤ ρ_n + D` with `ρ_n + D ≤ β_top` gives
the hypothesis `hE` of `onebox_bound`. -/
theorem endpoint_le (R ρn D βtop : ℝ) (hE : R ≤ ρn + D) (hρ : ρn + D ≤ βtop) :
    R ≤ βtop := hE.trans hρ

/-- Iterates of a reference map that drops by at least `c` above `a`. -/
theorem ref_iterate_le (ρ : ℝ → ℝ) (a c : ℝ) (hdrop : ∀ b, a < b → ρ b ≤ b - c)
    (β : ℝ) : ∀ n : ℕ, (∀ k < n, a < ρ^[k] β) → ρ^[n] β ≤ β - n * c := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hall
    have h1 := ih (fun k hk => hall k (Nat.lt_succ_of_lt hk))
    have h2 := hdrop _ (hall n (Nat.lt_succ_self n))
    rw [Function.iterate_succ_apply']
    push_cast
    linarith

/-- **The side of the large box.** If the first `n ≥ 1` iterates stay above
`β_top - D`, the reference map drops by `c₁ log 2` there, and
`β ≤ c₁ log N + C`, then `2^n < 2 N e^{(C+D-β_top)/c₁}`. -/
theorem onebox_size (ρ : ℝ → ℝ) (c₁ βtop C D β : ℝ) (N : ℕ) (hc₁ : 0 < c₁)
    (hN : 1 ≤ N) (hβ : β ≤ c₁ * Real.log N + C)
    (hdrop : ∀ b, βtop - D < b → ρ b ≤ b - c₁ * Real.log 2)
    (n : ℕ) (hn : 1 ≤ n) (hall : ∀ k < n, βtop - D < ρ^[k] β) :
    (2 : ℝ) ^ n < 2 * N * Real.exp ((C + D - βtop) / c₁) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hit := ref_iterate_le ρ (βtop - D) (c₁ * Real.log 2) hdrop β m
    (fun k hk => hall k (Nat.lt_succ_of_lt hk))
  have hlast := hall m (Nat.lt_succ_self m)
  have hm : (m : ℝ) * (c₁ * Real.log 2) < β - (βtop - D) := by linarith
  have hm' : (m : ℝ) * Real.log 2 < Real.log N + (C + D - βtop) / c₁ := by
    have : (m : ℝ) * Real.log 2 < (β - (βtop - D)) / c₁ := by
      rw [lt_div_iff₀ hc₁]; linarith
    have h2 : (β - (βtop - D)) / c₁ ≤ Real.log N + (C + D - βtop) / c₁ := by
      rw [div_le_iff₀ hc₁, add_mul, div_mul_cancel₀ _ hc₁.ne']; nlinarith
    linarith
  have hpow : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos two_pos, mul_comm]
  have hlt : (2 : ℝ) ^ m < N * Real.exp ((C + D - βtop) / c₁) := by
    rw [hpow]
    calc Real.exp ((m : ℝ) * Real.log 2)
        < Real.exp (Real.log N + (C + D - βtop) / c₁) := Real.exp_lt_exp.mpr hm'
      _ = N * Real.exp ((C + D - βtop) / c₁) := by
        rw [Real.exp_add, Real.exp_log hNpos]
  rw [pow_succ]
  linarith

variable (βs : ℝ) (Rs : ℕ → ℝ → ℝ)

/-- Under a uniform drop `Rs m b ≤ b - δ` on `(βs, β₁]`, the matched orbit
started at `β ≤ β₁` never rises, and until it enters the band it has dropped by
at least `k δ` after `k` rungs. -/
theorem orb_drop (β₁ δ : ℝ)
    (hdrop : ∀ m b, βs < b → b ≤ β₁ → Rs m b ≤ b - δ) (hδ : 0 ≤ δ)
    (n : ℕ) (β : ℝ) (hβ : β ≤ β₁) :
    ∀ k : ℕ, YangMills.Ledger.orb βs Rs n β k ≤ β ∧
      (YangMills.Ledger.orb βs Rs n β k ≤ βs ∨
        YangMills.Ledger.orb βs Rs n β k ≤ β - k * δ) := by
  intro k
  induction k with
  | zero => simp [YangMills.Ledger.orb]
  | succ k ih =>
    obtain ⟨hle, hor⟩ := ih
    by_cases h : YangMills.Ledger.orb βs Rs n β k ≤ βs
    · simp only [YangMills.Ledger.orb, if_pos h]; exact ⟨hle, Or.inl h⟩
    · simp only [YangMills.Ledger.orb, if_neg h]
      rw [not_le] at h
      have hk : YangMills.Ledger.orb βs Rs n β k ≤ β - k * δ := hor.resolve_left (not_le.mpr h)
      have hs := hdrop (n - k) _ h (hle.trans hβ)
      push_cast
      refine ⟨by nlinarith, Or.inr (by linarith)⟩

/-- **The barrier chain.** Under a uniform drop on `(βs, β₁]`, if
`β - j δ ≤ βs` and `j ≤ n`, the pressure at the top is bounded by the pressure
at some rung `i ≤ j` that lies in the band. -/
theorem barrier_chain (X : ℕ → ℝ → ℝ)
    (hmatch : ∀ m β, βs < β → X (m + 1) β ≤ X m (Rs (m + 1) β))
    (β₁ δ : ℝ) (hdrop : ∀ m b, βs < b → b ≤ β₁ → Rs m b ≤ b - δ) (hδ : 0 ≤ δ)
    (n j : ℕ) (hj : j ≤ n) (β : ℝ) (hβ : β ≤ β₁) (hjδ : β - j * δ ≤ βs) :
    ∃ i ≤ j, YangMills.Ledger.orb βs Rs n β i ≤ βs ∧
      X n β ≤ X (n - i) (YangMills.Ledger.orb βs Rs n β i) := by
  rcases YangMills.Ledger.orbit_chain βs Rs X hmatch n β j hj with h | ⟨hall, _⟩
  · exact h
  · exfalso
    have h1 := hall j le_rfl
    rcases (orb_drop βs Rs β₁ δ hdrop hδ n β hβ j).2 with h2 | h2 <;> linarith

/-- **The barrier gap bound.** If `e^{-T E} ≤ 2 X` and
`X ≤ K T^4 e^{-(4T/L) log 2}` with `K, T > 0`, then
`E ≥ 4 log 2 / L - log (2 K T^4) / T`. -/
theorem barrier_gap (T E X K L : ℝ) (hT : 0 < T) (hK : 0 < K)
    (h1 : Real.exp (-(T * E)) ≤ 2 * X)
    (h2 : X ≤ K * T ^ 4 * Real.exp (-(4 * T / L) * Real.log 2)) :
    4 * Real.log 2 / L - Real.log (2 * K * T ^ 4) / T ≤ E := by
  have hA : 0 < 2 * K * T ^ 4 := by positivity
  have h3 : Real.exp (-(T * E)) ≤
      Real.exp (Real.log (2 * K * T ^ 4) + (-(4 * T / L) * Real.log 2)) := by
    rw [Real.exp_add, Real.exp_log hA]; nlinarith [Real.exp_pos (-(4 * T / L) * Real.log 2)]
  have h4 := Real.exp_le_exp.mp h3
  have h5 : 4 * Real.log 2 / L * T - Real.log (2 * K * T ^ 4) ≤ E * T := by
    have : -(4 * T / L) * Real.log 2 = -(4 * Real.log 2 / L * T) := by ring
    rw [this] at h4; linarith
  have h6 : (4 * Real.log 2 / L * T - Real.log (2 * K * T ^ 4)) / T ≤ E := by
    rw [div_le_iff₀ hT]; linarith
  have h7 : (4 * Real.log 2 / L * T - Real.log (2 * K * T ^ 4)) / T =
      4 * Real.log 2 / L - Real.log (2 * K * T ^ 4) / T := by
    field_simp
  linarith

end YangMills.OneBox
