import Mathlib

/-!
# One-cube criteria: the twelve two-gluon singlet states (check L13)

On `(2T)³` the lowest nonzero momenta are `k = ±(π/T) eⱼ`, `j = 1, 2, 3`, each with
two transverse polarisations. A one-gluon mode is `(j, sign, λ)`. The two-gluon
colour-singlet states of zero total momentum built from the lowest shell are
`Σₐ a†_{k,λ,a} a†_{-k,λ',a} Ω`; by boson symmetry such a state depends only on
the unordered pair of modes `{(k, λ), (-k, λ')}`. We count these unordered pairs.
-/

namespace YangMills.OneCube.Counting

/-- A lowest-shell mode: axis `j`, sign of the momentum, polarisation. -/
abbrev Mode := Fin 3 × Bool × Fin 2

/-- Two modes have opposite momenta: same axis, opposite signs. -/
def opposite (m m' : Mode) : Prop := m.1 = m'.1 ∧ m.2.1 ≠ m'.2.1

instance : DecidableRel opposite := fun _ _ => by unfold opposite; infer_instance

theorem opposite_symm (m m' : Mode) : opposite m m' ↔ opposite m' m := by
  unfold opposite; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, Ne.symm h2⟩

/-- Ordered pairs of modes with zero total momentum. -/
theorem ordered_count :
    ((Finset.univ : Finset (Mode × Mode)).filter (fun p => opposite p.1 p.2)).card = 24 := by
  decide

/-- Unordered pairs (boson symmetry): the twelve two-gluon singlet states. -/
theorem L13 :
    ((Finset.univ : Finset (Sym2 Mode)).filter
      (fun z => Sym2.lift ⟨fun m m' => decide (opposite m m'),
        fun m m' => by simp [opposite_symm m m']⟩ z = true)).card = 12 := by
  decide

/-- Equivalently: choosing the representative with positive momentum first. -/
theorem L13_representatives :
    ((Finset.univ : Finset (Mode × Mode)).filter
      (fun p => opposite p.1 p.2 ∧ p.1.2.1 = true)).card = 12 := by
  decide

end YangMills.OneCube.Counting
