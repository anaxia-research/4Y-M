import Mathlib

/-!
# Projected and dyonic data of finite groups at the Potts point

Part (b) of Proposition `ly:prop:finiteproj` of the paper, for an arbitrary finite group `H`,
a subgroup `C` of its centre and a bimultiplicative phase `e` on `C` (for a symmetric
bilinear form `phi` on `C`, `e x y = exp (2 pi i phi(x, y))`). A quadruple is written
`((g1, g2, g3), h)`, its commutators are `c_ab`, and its phase is
`e(c12, c34) e(c13, c24)⁻¹ e(c14, c23)`, the exponential of `2 pi i Pf_phi(c)`.

`dyonic_between`: the sum of the phases over the quadruples with all commutators in `C`
(the dyonic sum `sum_c e^{2 pi i Pf(c)} |Hom_c|`) is a natural number, at least the number of
quadruples whose first three entries commute (the neutral sum `sum_z |Hom_(0,z)|`) and at
most the number of all quadruples with commutators in `C` (the torsion-free sum
`sum_c |Hom_c|`). The proof is the one in the paper: for a fixed triple the fourth entries
form a subgroup on which the phase is a character, so its sum is `0` or the order.

`potts_values`: the arithmetic of the values quoted after the proposition (item (C11)).
-/

namespace YangMills.FiniteProjected

open Finset

variable {H : Type*} [Group H]

/-- The commutator `a b a⁻¹ b⁻¹`. -/
def cm (a b : H) : H := a * b * a⁻¹ * b⁻¹

theorem cm_mul_right (C : Subgroup H) (hC : C ≤ Subgroup.center H) (a h h' : H)
    (h2 : cm a h' ∈ C) : cm a (h * h') = cm a h * cm a h' := by
  have hz := Subgroup.mem_center_iff.mp (hC h2)
  have e1 : cm a (h * h') = cm a h * (h * cm a h' * h⁻¹) := by
    simp only [cm]; group
  rw [e1, hz h]
  group

theorem cm_inv_right (C : Subgroup H) (hC : C ≤ Subgroup.center H) (a h : H)
    (h1 : cm a h ∈ C) : cm a h⁻¹ = (cm a h)⁻¹ := by
  have hz := Subgroup.mem_center_iff.mp (hC (C.inv_mem h1))
  have e1 : cm a h⁻¹ = h⁻¹ * (cm a h)⁻¹ * h := by
    simp only [cm]; group
  rw [e1, hz h⁻¹]
  group

variable (C : Subgroup H)

/-- Triples whose three commutators lie in `C`. -/
abbrev okT (g : H × H × H) : Prop :=
  cm g.1 g.2.1 ∈ C ∧ cm g.1 g.2.2 ∈ C ∧ cm g.2.1 g.2.2 ∈ C

/-- Fourth entries whose commutators with the triple lie in `C`. -/
abbrev okS (g : H × H × H) (h : H) : Prop :=
  cm g.1 h ∈ C ∧ cm g.2.1 h ∈ C ∧ cm g.2.2 h ∈ C

/-- A bimultiplicative phase on `C`. -/
structure Bichar (e : H → H → ℂ) : Prop where
  mul_left : ∀ x ∈ C, ∀ x' ∈ C, ∀ y ∈ C, e (x * x') y = e x y * e x' y
  mul_right : ∀ x ∈ C, ∀ y ∈ C, ∀ y' ∈ C, e x (y * y') = e x y * e x y'
  one_left : ∀ y, e 1 y = 1
  one_right : ∀ x, e x 1 = 1

/-- The phase of a quadruple, `exp (2 pi i Pf_phi(c))`. -/
noncomputable def ph (e : H → H → ℂ) (g : H × H × H) (h : H) : ℂ :=
  e (cm g.1 g.2.1) (cm g.2.2 h) * (e (cm g.1 g.2.2) (cm g.2.1 h))⁻¹ *
    e (cm g.1 h) (cm g.2.1 g.2.2)

variable {C}

theorem okS_mul (hC : C ≤ Subgroup.center H) {g : H × H × H} {h h' : H}
    (hh : okS C g h) (hh' : okS C g h') : okS C g (h * h') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cm_mul_right C hC _ _ _ hh'.1]; exact C.mul_mem hh.1 hh'.1
  · rw [cm_mul_right C hC _ _ _ hh'.2.1]; exact C.mul_mem hh.2.1 hh'.2.1
  · rw [cm_mul_right C hC _ _ _ hh'.2.2]; exact C.mul_mem hh.2.2 hh'.2.2

theorem okS_inv (hC : C ≤ Subgroup.center H) {g : H × H × H} {h : H}
    (hh : okS C g h) : okS C g h⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cm_inv_right C hC _ _ hh.1]; exact C.inv_mem hh.1
  · rw [cm_inv_right C hC _ _ hh.2.1]; exact C.inv_mem hh.2.1
  · rw [cm_inv_right C hC _ _ hh.2.2]; exact C.inv_mem hh.2.2

theorem ph_mul (hC : C ≤ Subgroup.center H) {e : H → H → ℂ} (he : Bichar C e)
    {g : H × H × H} (hg : okT C g) {h h' : H} (hh : okS C g h) (hh' : okS C g h') :
    ph e g (h * h') = ph e g h * ph e g h' := by
  obtain ⟨g1, g2, g3⟩ := g
  simp only [ph] at *
  rw [cm_mul_right C hC g3 h h' hh'.2.2, cm_mul_right C hC g2 h h' hh'.2.1,
    cm_mul_right C hC g1 h h' hh'.1,
    he.mul_right _ hg.1 _ hh.2.2 _ hh'.2.2, he.mul_right _ hg.2.1 _ hh.2.1 _ hh'.2.1,
    he.mul_left _ hh.1 _ hh'.1 _ hg.2.2, mul_inv]
  ring

theorem ph_comm {e : H → H → ℂ} (he : Bichar C e) {g : H × H × H}
    (hg : cm g.1 g.2.1 = 1 ∧ cm g.1 g.2.2 = 1 ∧ cm g.2.1 g.2.2 = 1) (h : H) :
    ph e g h = 1 := by
  simp only [ph, hg.1, hg.2.1, hg.2.2, he.one_left, he.one_right, inv_one, mul_one]

/-- For a triple with central commutators, if the phase is `1` on all fourth entries, the
sum of the phases is the number of fourth entries. -/
theorem inner_sum_one [DecidablePred (· ∈ C)] [Fintype H] {e : H → H → ℂ} {g : H × H × H}
    (hall : ∀ h ∈ univ.filter (okS C g), ph e g h = 1) :
    (∑ h ∈ univ.filter (okS C g), ph e g h) = ((univ.filter (okS C g)).card : ℂ) := by
  rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Otherwise the sum is `0`: the fourth entries form a subgroup on which the phase is a
nontrivial character. -/
theorem inner_sum_zero [DecidablePred (· ∈ C)] [Fintype H] (hC : C ≤ Subgroup.center H)
    {e : H → H → ℂ} (he : Bichar C e) {g : H × H × H} (hg : okT C g)
    (hall : ¬ ∀ h ∈ univ.filter (okS C g), ph e g h = 1) :
    (∑ h ∈ univ.filter (okS C g), ph e g h) = 0 := by
  obtain ⟨h0, h0A, h0ne⟩ : ∃ h0 ∈ univ.filter (okS C g), ph e g h0 ≠ 1 := by
    by_contra hc
    exact hall (fun h hh => by
      by_contra hne
      exact hc ⟨h, hh, hne⟩)
  have h0S : okS C g h0 := (Finset.mem_filter.mp h0A).2
  have key : ph e g h0 * (∑ h ∈ univ.filter (okS C g), ph e g h) =
      ∑ h ∈ univ.filter (okS C g), ph e g h := by
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_nbij' (fun h => h0⁻¹ * h) (fun h => h0 * h) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        okS_mul hC (okS_inv hC h0S) (Finset.mem_filter.mp ha).2⟩
    · intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        okS_mul hC h0S (Finset.mem_filter.mp ha).2⟩
    · intro a _; simp
    · intro a _; simp
    · intro a ha
      have haS : okS C g a := (Finset.mem_filter.mp ha).2
      have hiS : okS C g (h0⁻¹ * a) := okS_mul hC (okS_inv hC h0S) haS
      rw [← ph_mul hC he hg h0S hiS]
      simp
  have h2 : (ph e g h0 - 1) * (∑ h ∈ univ.filter (okS C g), ph e g h) = 0 := by
    rw [sub_mul, key, one_mul, sub_self]
  rcases mul_eq_zero.mp h2 with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) h0ne
  · exact h1

/-- Part (b) of Proposition `ly:prop:finiteproj`: neutral sum `<=` dyonic sum `<=`
torsion-free sum, the dyonic sum being a natural number. -/
theorem dyonic_between [DecidablePred (· ∈ C)] [Fintype H] [DecidableEq H]
    (hC : C ≤ Subgroup.center H) {e : H → H → ℂ} (he : Bichar C e) :
    ∃ n : ℕ,
      (∑ p ∈ univ.filter (fun p : (H × H × H) × H => okT C p.1 ∧ okS C p.1 p.2),
          ph e p.1 p.2) = n ∧
      (univ.filter (fun p : (H × H × H) × H =>
          (cm p.1.1 p.1.2.1 = 1 ∧ cm p.1.1 p.1.2.2 = 1 ∧ cm p.1.2.1 p.1.2.2 = 1) ∧
            okS C p.1 p.2)).card ≤ n ∧
      n ≤ (univ.filter (fun p : (H × H × H) × H => okT C p.1 ∧ okS C p.1 p.2)).card := by
  classical
  let n : H × H × H → ℕ := fun g =>
    if okT C g ∧ ∀ h ∈ univ.filter (okS C g), ph e g h = 1 then
      (univ.filter (okS C g)).card else 0
  refine ⟨∑ g, n g, ?_, ?_, ?_⟩
  · rw [Finset.sum_filter, Fintype.sum_prod_type, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    by_cases hg : okT C g
    · have e1 : (∑ h : H, if okT C (g, h).1 ∧ okS C (g, h).1 (g, h).2 then
            ph e (g, h).1 (g, h).2 else 0) = ∑ h ∈ univ.filter (okS C g), ph e g h := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl (fun h _ => if_congr (and_iff_right hg) rfl rfl)
      rw [e1]
      by_cases hall : ∀ h ∈ univ.filter (okS C g), ph e g h = 1
      · rw [inner_sum_one hall]
        show _ = (((if okT C g ∧ ∀ h ∈ univ.filter (okS C g), ph e g h = 1 then
          (univ.filter (okS C g)).card else 0 : ℕ)) : ℂ)
        rw [if_pos ⟨hg, hall⟩]
      · rw [inner_sum_zero hC he hg hall]
        show _ = (((if okT C g ∧ ∀ h ∈ univ.filter (okS C g), ph e g h = 1 then
          (univ.filter (okS C g)).card else 0 : ℕ)) : ℂ)
        rw [if_neg (fun hh => hall hh.2), Nat.cast_zero]
    · have e0 : (∑ h : H, if okT C (g, h).1 ∧ okS C (g, h).1 (g, h).2 then
            ph e (g, h).1 (g, h).2 else 0) = 0 :=
        Finset.sum_eq_zero (fun h _ => if_neg (fun hh => hg hh.1))
      rw [e0]
      show (0 : ℂ) = (((if okT C g ∧ ∀ h ∈ univ.filter (okS C g), ph e g h = 1 then
          (univ.filter (okS C g)).card else 0 : ℕ)) : ℂ)
      rw [if_neg (fun hh => hg hh.1), Nat.cast_zero]
  · rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_le_sum (fun g _ => ?_)
    by_cases hc : cm g.1 g.2.1 = 1 ∧ cm g.1 g.2.2 = 1 ∧ cm g.2.1 g.2.2 = 1
    · have hg : okT C g := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hc.1]; exact C.one_mem
        · rw [hc.2.1]; exact C.one_mem
        · rw [hc.2.2]; exact C.one_mem
      have hall : ∀ h ∈ univ.filter (okS C g), ph e g h = 1 := fun h _ => ph_comm he hc h
      have e1 : (∑ h : H, if (cm (g, h).1.1 (g, h).1.2.1 = 1 ∧ cm (g, h).1.1 (g, h).1.2.2 = 1 ∧
          cm (g, h).1.2.1 (g, h).1.2.2 = 1) ∧ okS C (g, h).1 (g, h).2 then 1 else 0) =
          (univ.filter (okS C g)).card := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl (fun h _ => if_congr (and_iff_right hc) rfl rfl)
      rw [e1]
      show _ ≤ (if okT C g ∧ ∀ h ∈ univ.filter (okS C g), ph e g h = 1 then
          (univ.filter (okS C g)).card else 0)
      rw [if_pos ⟨hg, hall⟩]
    · have e1 : (∑ h : H, if (cm (g, h).1.1 (g, h).1.2.1 = 1 ∧ cm (g, h).1.1 (g, h).1.2.2 = 1 ∧
          cm (g, h).1.2.1 (g, h).1.2.2 = 1) ∧ okS C (g, h).1 (g, h).2 then 1 else 0) = 0 :=
        Finset.sum_eq_zero (fun h _ => if_neg (fun hh => hc hh.1))
      rw [e1]; exact Nat.zero_le _
  · conv_rhs => rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_le_sum (fun g _ => ?_)
    show (if okT C g ∧ ∀ h ∈ univ.filter (okS C g), ph e g h = 1 then
          (univ.filter (okS C g)).card else 0) ≤ _
    by_cases hg : okT C g
    · have e1 : (∑ h : H, if okT C (g, h).1 ∧ okS C (g, h).1 (g, h).2 then 1 else 0) =
          (univ.filter (okS C g)).card := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl (fun h _ => if_congr (and_iff_right hg) rfl rfl)
      rw [e1]
      split_ifs
      · exact le_refl _
      · exact Nat.zero_le _
    · rw [if_neg (fun hh => hg hh.1)]; exact Nat.zero_le _

/-- The values after Proposition `ly:prop:finiteproj` (item (C11)): the neutral sums of
`Q8 o D8` (order 32) and `2I o D8` (order 480), divided by `8 q`, and the three values in
part (b) for these groups and for `2I` (dyonic and torsion-free values from the counts
`726016, 322560` and `22225920, 1612800` of Proposition `ly:prop:spn`). -/
theorem potts_values :
    188416 = 8 * 32 * 736 ∧ 7334400 = 8 * 480 * 1910 ∧
    726016 - 322560 = 8 * 32 * 1576 ∧ 726016 + 322560 = 8 * 32 * 4096 ∧
    22225920 - 1612800 = 8 * 480 * 5368 ∧ 22225920 + 1612800 = 8 * 480 * 6208 ∧
    736 ≤ 1576 ∧ 1576 ≤ 4096 ∧ 1910 ≤ 5368 ∧ 5368 ≤ 6208 ∧ 83 ≤ 97 := by
  norm_num

end YangMills.FiniteProjected
