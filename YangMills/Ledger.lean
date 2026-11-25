import Mathlib

/-!
# The defect ledger (Subsection `ly:sec:ladder`)

Abstract form of the ladder argument with the ledger condition `(SS_D)`.
`X m β` stands for the normalised thermal pressure of the datum torus of side
`8 · 2^m` at coupling `β`, and `Rs m β` for the coupling assigned to the torus
of half the size. The matched orbit halves the torus and moves the coupling to
`Rs`, until it enters the strong-coupling band `β ≤ βs`.

* `matched_mem`: a continuous pressure attains the infimum that defines the
  pressure-matched coupling (Lemma `ly:lem:Xcont` and the remark after
  Definition `ly:def:matched`).
* `orbit_chain`: the pressures along the matched orbit are non-decreasing,
  rung by rung, until the orbit enters the band.
* `ledger_bound`: a bounded running defect gives the pressure bound at the top
  of the ladder (Theorem `ly:thm:ledger`).
* `ladder_length`, `ladder_size`: the number of rungs and the side of the
  datum torus, `8 · 2^{n₀} ≤ 16 e^{(C+D)/c₁} N`.
* `step_scaling_defect`: the rung-by-rung condition `(SS)` gives a defect at
  most `c₁ log 2` (Lemma `ly:lem:ledgerweak`).
-/

open Real

namespace YangMills.Ledger

/-- The infimum defining the pressure-matched coupling is attained. -/
theorem matched_mem (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ici 0)) (y : ℝ)
    (hne : ({b | 0 ≤ b ∧ y ≤ f b} : Set ℝ).Nonempty) :
    sInf {b | 0 ≤ b ∧ y ≤ f b} ∈ ({b | 0 ≤ b ∧ y ≤ f b} : Set ℝ) := by
  have hcl : IsClosed (Set.Ici (0 : ℝ) ∩ f ⁻¹' Set.Ici y) :=
    hf.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Ici
  have heq : ({b | 0 ≤ b ∧ y ≤ f b} : Set ℝ) = Set.Ici (0 : ℝ) ∩ f ⁻¹' Set.Ici y := by
    ext b; simp
  rw [heq] at hne ⊢
  exact hcl.csInf_mem hne ⟨0, fun b hb => hb.1⟩

variable (βs : ℝ) (Rs : ℕ → ℝ → ℝ)

/-- The matched orbit started on the torus of side `8 · 2^n`: at step `k` the
side is `8 · 2^(n-k)`; once the coupling is in the band it stays put. -/
noncomputable def orb (n : ℕ) (β : ℝ) : ℕ → ℝ
  | 0 => β
  | k + 1 => if orb n β k ≤ βs then orb n β k else Rs (n - k) (orb n β k)

/-- Pressures along the matched orbit. -/
theorem orbit_chain (X : ℕ → ℝ → ℝ)
    (hmatch : ∀ m β, βs < β → X (m + 1) β ≤ X m (Rs (m + 1) β))
    (n : ℕ) (β : ℝ) :
    ∀ k ≤ n,
      (∃ j ≤ k, orb βs Rs n β j ≤ βs ∧ X n β ≤ X (n - j) (orb βs Rs n β j)) ∨
      ((∀ j ≤ k, βs < orb βs Rs n β j) ∧ X n β ≤ X (n - k) (orb βs Rs n β k)) := by
  intro k
  induction k with
  | zero =>
    intro _
    by_cases h : β ≤ βs
    · exact Or.inl ⟨0, le_rfl, by simpa [orb] using h, by simp [orb]⟩
    · refine Or.inr ⟨fun j hj => ?_, by simp [orb]⟩
      have : j = 0 := Nat.le_zero.mp hj
      subst this; simpa [orb] using not_le.mp h
  | succ k ih =>
    intro hk
    rcases ih (Nat.le_of_succ_le hk) with ⟨j, hj, h1, h2⟩ | ⟨hall, hX⟩
    · exact Or.inl ⟨j, Nat.le_succ_of_le hj, h1, h2⟩
    · have hk' : βs < orb βs Rs n β k := hall k le_rfl
      have hstep : orb βs Rs n β (k + 1) = Rs (n - k) (orb βs Rs n β k) := by
        simp [orb, not_le.mpr hk']
      have hnk : n - k = (n - (k + 1)) + 1 := by omega
      have hm := hmatch (n - (k + 1)) (orb βs Rs n β k) hk'
      rw [← hnk] at hm
      have hX' : X n β ≤ X (n - (k + 1)) (orb βs Rs n β (k + 1)) := by
        rw [hstep]; exact hX.trans hm
      by_cases hb : orb βs Rs n β (k + 1) ≤ βs
      · exact Or.inl ⟨k + 1, le_rfl, hb, hX'⟩
      · refine Or.inr ⟨fun j hj => ?_, hX'⟩
        rcases Nat.lt_or_eq_of_le hj with hlt | heq
        · exact hall j (Nat.lt_succ_iff.mp hlt)
        · subst heq; exact not_le.mp hb

/-- **The ledger bound.** If the running defect of the matched orbit is at most
`D`, and the ladder has enough rungs, the pressure at the top is below the
strong-coupling bound `x₀`. -/
theorem ledger_bound (X : ℕ → ℝ → ℝ)
    (hmatch : ∀ m β, βs < β → X (m + 1) β ≤ X m (Rs (m + 1) β))
    (x₀ c D : ℝ) (hbot : ∀ m β, β ≤ βs → X m β < x₀)
    (n : ℕ) (β : ℝ)
    (hledger : (∀ j < n, βs < orb βs Rs n β j) → orb βs Rs n β n ≤ β - n * c + D)
    (hn : β - n * c + D ≤ βs) :
    X n β < x₀ := by
  rcases orbit_chain βs Rs X hmatch n β n le_rfl with ⟨j, _, h1, h2⟩ | ⟨hall, _⟩
  · exact lt_of_le_of_lt h2 (hbot _ _ h1)
  · exfalso
    have h1 := hledger (fun j hj => hall j hj.le)
    have h2 := hall n le_rfl
    linarith

/-- With `n₀ = ⌈(β - βs + D)/c⌉`, the ladder has enough rungs. -/
theorem ladder_length (β c D : ℝ) (hc : 0 < c) :
    β - (⌈(β - βs + D) / c⌉₊ : ℕ) * c + D ≤ βs := by
  have h := Nat.le_ceil ((β - βs + D) / c)
  have : β - βs + D ≤ (⌈(β - βs + D) / c⌉₊ : ℝ) * c := by
    rwa [div_le_iff₀ hc] at h
  linarith

/-- The side of the datum torus: `2^{n₀} ≤ 2 N e^{(C+D)/c₁}` with
`c = c₁ log 2`, for `0 ≤ βs` and `β ≤ c₁ log N + C`. -/
theorem ladder_size (β c₁ C D : ℝ) (N : ℕ) (hc₁ : 0 < c₁) (hβs : 0 ≤ βs)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hN : 1 ≤ N) (hβ : β ≤ c₁ * Real.log N + C) :
    (2 : ℝ) ^ (⌈(β - βs + D) / (c₁ * Real.log 2)⌉₊) ≤ 2 * N * Real.exp ((C + D) / c₁) := by
  set y := (β - βs + D) / (c₁ * Real.log 2) with hy
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp1 : 1 ≤ Real.exp ((C + D) / c₁) :=
    Real.one_le_exp (div_nonneg (by linarith) hc₁.le)
  by_cases hy0 : y ≤ 0
  · have : ⌈y⌉₊ = 0 := Nat.ceil_eq_zero.mpr hy0
    rw [this, pow_zero]
    nlinarith
  · rw [not_le] at hy0
    have hlt : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
    have h1 : (2 : ℝ) ^ (⌈y⌉₊) = Real.exp ((⌈y⌉₊ : ℝ) * Real.log 2) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos two_pos, mul_comm]
    have h2 : Real.exp ((⌈y⌉₊ : ℝ) * Real.log 2) ≤ Real.exp ((y + 1) * Real.log 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlt.le hl2.le)
    have h3 : (y + 1) * Real.log 2 = Real.log 2 + (β - βs + D) / c₁ := by
      rw [hy]; field_simp; ring
    have h4 : (β - βs + D) / c₁ ≤ Real.log N + (C + D) / c₁ := by
      rw [div_le_iff₀ hc₁, add_mul, div_mul_cancel₀ _ hc₁.ne']
      nlinarith
    have h5 : Real.exp (Real.log 2 + (β - βs + D) / c₁) ≤
        Real.exp (Real.log 2 + (Real.log N + (C + D) / c₁)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [h1]
    calc Real.exp ((⌈y⌉₊ : ℝ) * Real.log 2) ≤ Real.exp ((y + 1) * Real.log 2) := h2
      _ = Real.exp (Real.log 2 + (β - βs + D) / c₁) := by rw [h3]
      _ ≤ Real.exp (Real.log 2 + (Real.log N + (C + D) / c₁)) := h5
      _ = 2 * N * Real.exp ((C + D) / c₁) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log two_pos, Real.exp_log hNpos]; ring

/-- **Step scaling gives a bounded ledger.** Under the rung-by-rung condition
`Rs m β ≤ max (β - c) βs` (for `βs < β`), the running defect is at most `c`. -/
theorem step_scaling_defect (c : ℝ)
    (hSS : ∀ m β, βs < β → Rs m β ≤ max (β - c) βs) (n : ℕ) (β : ℝ) :
    ∀ k, orb βs Rs n β k ≤ max (β - k * c) βs := by
  intro k
  induction k with
  | zero => simp [orb]
  | succ k ih =>
    by_cases h : orb βs Rs n β k ≤ βs
    · simp only [orb, if_pos h]; exact le_trans h (le_max_right _ _)
    · simp only [orb, if_neg h]
      rw [not_le] at h
      have hs := hSS (n - k) _ h
      have hmax : max (β - k * c) βs = β - k * c := by
        rcases le_total (β - k * c) βs with h' | h'
        · exfalso; have := lt_of_lt_of_le h (ih.trans (max_le h' le_rfl)); linarith
        · exact max_eq_left h'
      rw [hmax] at ih
      refine hs.trans (max_le_max ?_ le_rfl)
      push_cast; linarith

end YangMills.Ledger
