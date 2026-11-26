import Mathlib

/-!
# No comparison of resolutions gives the refinement bound (Remark `ly:rem:Rcompare`)

`Xf` is the pressure of the fine box at `b`, `Xs` the pressure of the coarse box at
the pressure-matched coupling (the same physical box), `Xc` the pressure of the
coarse box at the reference coupling `ρ b`, and `ε` the allowance `10⁻⁷ 2⁻ʲ`.

* `comparison_insufficient`: a same-physics comparison `Xf ≤ Xs + ε` together with
  `Xc ≤ Xs` (the coarse box of `(R)` is physically larger, so its pressure is
  smaller) does not imply `(R)`, that is `Xf ≤ Xc + ε`.
* `refine_of_small`: since `Xc ≥ 0`, absolute smallness `Xf ≤ ε` gives `(R)`.
* `refine_of_small_all`: the same at every step and coupling.
* `small_forces_gap`: with `log (1 + e^{-t}) ≤ Xf`, the bound `Xf ≤ ε < 1` forces
  `e^{-t} ≤ ε / (1 - ε)`, a lower bound on `t = T E₁`.
-/

namespace YangMills.RefinementCompare

/-- A same-physics comparison and the monotonicity of the pressure in physical size
do not combine to give the refinement bound. -/
theorem comparison_insufficient :
    ¬ ∀ Xf Xs Xc ε : ℝ, 0 ≤ Xc → 0 ≤ ε → Xf ≤ Xs + ε → Xc ≤ Xs → Xf ≤ Xc + ε := by
  intro h
  have := h 2 2 0 1 le_rfl zero_le_one (by norm_num) (by norm_num)
  norm_num at this

/-- Absolute smallness of the fine pressure gives the refinement bound. -/
theorem refine_of_small (Xf Xc ε : ℝ) (hc : 0 ≤ Xc) (hf : Xf ≤ ε) : Xf ≤ Xc + ε := by
  linarith

/-- Absolute smallness at every step gives `(R)` at every step. -/
theorem refine_of_small_all (X : ℕ → ℝ → ℝ) (ρ : ℝ → ℝ) (ε : ℕ → ℝ) (a : ℝ)
    (hnn : ∀ j b, 0 ≤ X j b) (hs : ∀ j b, a < b → X (j + 1) b ≤ ε j) :
    ∀ j b, a < b → X (j + 1) b ≤ X j (ρ b) + ε j := fun j b hb =>
  refine_of_small _ _ _ (hnn j (ρ b)) (hs j b hb)

/-- Smallness of the pressure is a gap bound: `log (1 + e^{-t}) ≤ X ≤ ε < 1` gives
`e^{-t} ≤ ε / (1 - ε)`. -/
theorem small_forces_gap (t X ε : ℝ) (hX : Real.log (1 + Real.exp (-t)) ≤ X)
    (hε : X ≤ ε) (h1 : ε < 1) : Real.exp (-t) ≤ ε / (1 - ε) := by
  have hpos : 0 < Real.exp (-t) := Real.exp_pos _
  have hlog : Real.log (1 + Real.exp (-t)) ≤ ε := le_trans hX hε
  have h2 : 1 + Real.exp (-t) ≤ Real.exp ε := by
    have := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (by linarith)] at this
  -- `exp ε ≤ 1 / (1 - ε)` for `ε < 1`
  have h3 : Real.exp ε ≤ 1 / (1 - ε) := by
    have hk : Real.exp (-ε) * Real.exp ε = 1 := by
      rw [← Real.exp_add]; simp
    have hb : 1 - ε ≤ Real.exp (-ε) := by
      have := Real.add_one_le_exp (-ε); linarith
    rw [le_div_iff₀ (by linarith)]
    nlinarith [Real.exp_pos ε]
  have h4 : Real.exp (-t) ≤ 1 / (1 - ε) - 1 := by linarith
  have hne : (1 - ε) ≠ 0 := by linarith
  have h5 : 1 / (1 - ε) - 1 = ε / (1 - ε) := by
    rw [div_sub_one hne]; ring_nf
  linarith [h5 ▸ h4]

end YangMills.RefinementCompare
