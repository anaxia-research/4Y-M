import Mathlib

/-!
# Quasi-Lee–Yang zeros

Finite, algebraic and complex-analytic parts of the section `sec:qly` of the paper.

* `cayley_re`, `cayley_re_neg_iff`, `cayley_re_eq_zero_iff`, `stack_factor`, `vieta_norm`,
  `stack_on_line` : Proposition `ly:prop:stack` (the stack identity).
* `vortex_expansion`, `vortex_weights_sum_one`, `vortex_pos` : Lemma `ly:lem:identities` (c), (d).
* `circle_zero_norm`, `circle_zeros`, `standing_wave`, `radius_gt_one` :
  Proposition `ly:prop:2d` (circle theorem and standing wave).
* `faces_twist`, `knot_invariance`, `knot_bounding`, `twist_time_step`, `twist_space_step`,
  `pair_cobdry`, `knot_independent` : Lemma `ly:lem:knot` (a)–(d).
* `area_bound` : Lemma `ly:lem:areas`.
* `slab_count`, `plaquette_counts` : the counting in Lemma `ly:lem:van`.
* `tail_sum`, `theoremA_tail`, `fluxhalf_log`, `fluxCrit_values` : Theorem `ly:thm:A` and
  Corollary `ly:cor:fluxhalf` (item (C3)).
* `vortex_factor_bound`, `theoremA_domain` : Theorem `ly:thm:Adomain`.
* `borel_caratheodory_disc`, `transport`, `re_log_bound`, `wilson_weight_bound`,
  `partition_bound`, `theoremB`, `one_sub_inv_pow_ge`, `theoremB_zstar`, `zstar_Mcirc` :
  Lemma `ly:lem:BC` and Theorem `ly:thm:B`, for any analytic map of the unit disc into the
  zero-free domain.
* `mobius_disc`, `sinh_halfstrip`, `strip_real` : Corollary `ly:cor:strip`.
* `kp_x`, `kp_constant`, `kappa_bounds`, `c0_le`, `c0_ge`, `eps_rKP`, `z2_disc`,
  `vortex_radius`, `disc_consistency` : Lemma `ly:lem:KP`, Propositions `ly:prop:betadisc`,
  `ly:prop:thetadisc`, Corollary `ly:cor:disc` (items (C1), (C2), (C4)).
* `critical_width`, `sinh_identity` : Proposition `ly:prop:critical` (item (C7)).
* `KN_threshold`, `KN_ed`, `eta_values`, `eta_decreasing`, `re_exp_pos`, `sum_ne_zero_of_re_pos`,
  `z2_datum_gap` : Proposition `ly:prop:N` (item (C5)).
* `coef_tail`, `cover_constants`, `pow_div_one_sub_mono`, `zstar_implies_HZ`,
  `halfplane_model`, `strip_model` : Lemmas `ly:lem:coef`, `ly:lem:models`, Theorem
  `ly:thm:cover` and Proposition `ly:prop:zstarHZ` (item (C8)).
* `stagger`, `stagger_plaquette_odd` : Theorem `ly:thm:even`.
* `onesided_threshold` : Lemma `ly:lem:onesided` and Remark `ly:rem:intensive`.
* `plus_arith` : Theorem `ly:thm:plus`.
* `critflux_width` : Proposition `ly:prop:critflux`.
* `torelon_toy_zero` : Remark `ly:rem:antistokes`.
-/

open Real Complex Finset Metric Filter Asymptotics
open scoped Topology

namespace YangMills.QuasiLeeYang

/-! ## The stack identity -/

/-- The real part of the Cayley transform `θ = (u - 1)/(u + 1)`. -/
theorem cayley_re (u : ℂ) (hu : u ≠ -1) :
    ((u - 1) / (u + 1)).re = (‖u‖ ^ 2 - 1) / ‖u + 1‖ ^ 2 := by
  have h : u + 1 ≠ 0 := fun h => hu (by linear_combination h)
  rw [Complex.div_re, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im, Complex.add_im,
    Complex.one_im]
  rw [← add_div]
  congr 1
  ring

/-- Proposition `ly:prop:stack` (ii): `|u| < 1` if and only if `Re θ < 0`. -/
theorem cayley_re_neg_iff (u : ℂ) (hu : u ≠ -1) :
    ‖u‖ < 1 ↔ ((u - 1) / (u + 1)).re < 0 := by
  have h : 0 < ‖u + 1‖ ^ 2 := by
    have : u + 1 ≠ 0 := fun h => hu (by linear_combination h)
    positivity
  rw [cayley_re u hu, div_neg_iff]
  constructor
  · intro h1
    right
    exact ⟨by nlinarith [norm_nonneg u], h⟩
  · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · linarith
    · nlinarith [norm_nonneg u]

/-- Proposition `ly:prop:stack` (ii): `|u| = 1` if and only if `Re θ = 0`. -/
theorem cayley_re_eq_zero_iff (u : ℂ) (hu : u ≠ -1) :
    ‖u‖ = 1 ↔ ((u - 1) / (u + 1)).re = 0 := by
  have h : ‖u + 1‖ ^ 2 ≠ 0 := by
    have : u + 1 ≠ 0 := fun h => hu (by linear_combination h)
    positivity
  rw [cayley_re u hu, div_eq_zero_iff, or_iff_left h, sub_eq_zero]
  constructor
  · intro h1; rw [h1]; norm_num
  · intro h1
    have h0 := norm_nonneg u
    nlinarith

/-- The factorisation of Proposition `ly:prop:stack`: for `θ ≠ 1` and `u = (1+θ)/(1-θ)`,
`∑_{Y ⊆ Q} ((1+θ)/2)^{m-|Y|} ((1-θ)/2)^{|Y|} c_Y = ((1-θ)/2)^m ∑_{Y ⊆ Q} c_Y u^{m-|Y|}`. -/
theorem stack_factor {α : Type*} (Q : Finset α) (c : Finset α → ℂ) (θ : ℂ) (hθ : θ ≠ 1) :
    ∑ Y ∈ Q.powerset, ((1 + θ) / 2) ^ (Q.card - Y.card) * ((1 - θ) / 2) ^ Y.card * c Y =
      ((1 - θ) / 2) ^ Q.card *
        ∑ Y ∈ Q.powerset, c Y * ((1 + θ) / (1 - θ)) ^ (Q.card - Y.card) := by
  have h1 : (1 - θ) / 2 ≠ 0 := by
    have : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
    exact div_ne_zero this two_ne_zero
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y hY => ?_
  have hYc : Y.card ≤ Q.card := Finset.card_le_card (Finset.mem_powerset.mp hY)
  have hu : (1 + θ) / 2 = ((1 + θ) / (1 - θ)) * ((1 - θ) / 2) := by
    have : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
    field_simp
  rw [hu, mul_pow]
  have : ((1 - θ) / 2) ^ Q.card = ((1 - θ) / 2) ^ (Q.card - Y.card) * ((1 - θ) / 2) ^ Y.card := by
    rw [← pow_add, Nat.sub_add_cancel hYc]
  rw [this]
  ring

/-- Proposition `ly:prop:stack` (i), Vieta's formula in norms: for a nonzero complex
polynomial, the product of the moduli of its roots, with multiplicity, is
`|g(0)| / |leading coefficient|`. -/
theorem vieta_norm (g : Polynomial ℂ) (hg : g ≠ 0) :
    (g.roots.map (fun u => ‖u‖)).prod = ‖g.coeff 0‖ / ‖g.leadingCoeff‖ := by
  have hl : ‖g.leadingCoeff‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact Polynomial.leadingCoeff_ne_zero.mpr hg
  rw [(IsAlgClosed.splits g).coeff_zero_eq_leadingCoeff_mul_prod_roots, norm_mul, norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul, mul_div_cancel_left₀ _ hl]
  simpa using Multiset.prod_hom g.roots (normHom (α := ℂ))

/-- Proposition `ly:prop:stack` (iii): if every root has modulus one, then
`|g(0)| = |leading coefficient|`, that is `Z_z = Z`. -/
theorem stack_on_line (g : Polynomial ℂ) (hg : g ≠ 0) (h : ∀ u ∈ g.roots, ‖u‖ = 1) :
    ‖g.coeff 0‖ = ‖g.leadingCoeff‖ := by
  have hl : ‖g.leadingCoeff‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact Polynomial.leadingCoeff_ne_zero.mpr hg
  have h1 : (g.roots.map (fun u => ‖u‖)).prod = 1 := by
    rw [Multiset.map_congr rfl h, Multiset.map_const', Multiset.prod_replicate, one_pow]
  rw [vieta_norm g hg] at h1
  field_simp at h1
  exact h1

/-! ## The vortex polynomial: Lemma `ly:lem:identities` (c), (d) -/

/-- Lemma `ly:lem:identities` (c): the expansion of `∏_p (a_p + b_p)` over subsets. -/
theorem vortex_expansion {P : Type*} [Fintype P] [DecidableEq P] (a b : P → ℝ) :
    ∏ p, (a p + b p) = ∑ F ∈ (Finset.univ : Finset P).powerset,
      (∏ p ∈ F, b p) * ∏ p ∈ Finset.univ \ F, a p := by
  rw [show (fun p => a p + b p) = (fun p => b p + a p) from funext fun p => add_comm _ _]
  exact Finset.prod_add b a Finset.univ

/-- Lemma `ly:lem:identities` (d): for `θ_p ∈ [-1,1]` the weights
`∏_{p∈F} (1-θ_p)/2 ∏_{p∉F} (1+θ_p)/2` are nonnegative and sum to one. -/
theorem vortex_weights_sum_one {P : Type*} [Fintype P] [DecidableEq P] (θ : P → ℝ) :
    ∑ F ∈ (Finset.univ : Finset P).powerset,
      (∏ p ∈ F, (1 - θ p) / 2) * ∏ p ∈ Finset.univ \ F, (1 + θ p) / 2 = 1 := by
  rw [← vortex_expansion]
  simp only [show ∀ p, (1 + θ p) / 2 + (1 - θ p) / 2 = 1 from fun p => by ring,
    Finset.prod_const_one]

/-- Lemma `ly:lem:identities` (d): `Z(θ) > 0` for `θ ∈ [-1,1]^P`, since `Z(θ)` is a convex
combination of the positive twisted partition functions `Z_{ζ_F}`. -/
theorem vortex_pos {P : Type*} [Fintype P] [DecidableEq P] (θ : P → ℝ)
    (hθ : ∀ p, -1 ≤ θ p ∧ θ p ≤ 1) (Zf : Finset P → ℝ) (hZ : ∀ F, 0 < Zf F) :
    0 < ∑ F ∈ (Finset.univ : Finset P).powerset,
      (∏ p ∈ F, (1 - θ p) / 2) * (∏ p ∈ Finset.univ \ F, (1 + θ p) / 2) * Zf F := by
  have hw : ∀ F, 0 ≤ (∏ p ∈ F, (1 - θ p) / 2) * ∏ p ∈ Finset.univ \ F, (1 + θ p) / 2 :=
    fun F => mul_nonneg (Finset.prod_nonneg fun p _ => by linarith [(hθ p).2])
      (Finset.prod_nonneg fun p _ => by linarith [(hθ p).1])
  have hmpos : 0 < (Finset.univ : Finset (Finset P)).inf' Finset.univ_nonempty Zf := by
      obtain ⟨F, _, hF⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty Zf
      rw [hF]; exact hZ F
  calc (0 : ℝ) < 1 * (Finset.univ : Finset (Finset P)).inf' Finset.univ_nonempty Zf := by
        rw [one_mul]; exact hmpos
    _ = ∑ F ∈ (Finset.univ : Finset P).powerset,
          (∏ p ∈ F, (1 - θ p) / 2) * (∏ p ∈ Finset.univ \ F, (1 + θ p) / 2) *
            (Finset.univ : Finset (Finset P)).inf' Finset.univ_nonempty Zf := by
        rw [← Finset.sum_mul, vortex_weights_sum_one]
    _ ≤ _ := Finset.sum_le_sum fun F _ =>
        mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ F)) (hw F)

/-! ## Two dimensions: circle theorem and standing wave -/

/-- Proposition `ly:prop:2d`: every zero of `E + θ^F O` with `E, O > 0` has `|θ|^F = E/O`,
so all zeros lie on one circle. -/
theorem circle_zero_norm (E O : ℝ) (hE : 0 < E) (hO : 0 < O) (F : ℕ) (θ : ℂ)
    (h : (E : ℂ) + θ ^ F * O = 0) : ‖θ‖ ^ F = E / O := by
  have h1 : θ ^ F * (O : ℂ) = -E := by linear_combination h
  have h2 : ‖θ ^ F * (O : ℂ)‖ = ‖(-(E : ℂ))‖ := by rw [h1]
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hO] at h2
  rw [abs_of_pos hE] at h2
  rw [eq_div_iff hO.ne', h2]


/-- Proposition `ly:prop:2d`: with `ρ^F O = E`, each point `ρ e^{iπ(2k+1)/F}` is a zero of
`E + θ^F O`. -/
theorem circle_zeros (E O ρ : ℝ) (F : ℕ) (hF : 0 < F) (hρ : ρ ^ F * O = E) (k : ℕ) :
    (E : ℂ) + ((ρ : ℂ) * Complex.exp (↑(π * (2 * k + 1) / F) * Complex.I)) ^ F * O = 0 := by
  have hF' : (F : ℂ) ≠ 0 := by exact_mod_cast hF.ne'
  rw [mul_pow, ← Complex.exp_nat_mul]
  have h1 : (F : ℂ) * (↑(π * (2 * k + 1) / F) * Complex.I) = ↑(k : ℤ) * (2 * π * Complex.I) +
      π * Complex.I := by
    push_cast
    field_simp
  rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_pi_mul_I]
  rw [← hρ]
  push_cast
  ring

/-- The standing wave `(ly:eq:standing)`: `|E + E e^{ix}| = 2E |cos(x/2)|`. -/
theorem standing_wave (E x : ℝ) (hE : 0 ≤ E) :
    ‖(E : ℂ) + E * Complex.exp (x * Complex.I)‖ = 2 * E * |Real.cos (x / 2)| := by
  have h : (E : ℂ) + E * Complex.exp (x * Complex.I) =
      (2 * E * Real.cos (x / 2) : ℝ) * Complex.exp ((x / 2 : ℝ) * Complex.I) := by
    have hx : Complex.exp (x * Complex.I) = Complex.exp ((x / 2 : ℝ) * Complex.I) ^ 2 := by
      rw [← Complex.exp_nat_mul]; push_cast; ring_nf
    rw [hx, Complex.exp_mul_I]
    push_cast
    have hs := Complex.sin_sq_add_cos_sq ((x : ℂ) / 2)
    linear_combination (-(E : ℂ)) * hs + (E : ℂ) * Complex.sin ((x : ℂ) / 2) ^ 2 * Complex.I_sq
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_nonneg hE, abs_two]

/-- Proposition `ly:prop:2d`: on the circle `ρ^F O = E` the synchronous polynomial is the
standing wave `|E + (ρ e^{iφ})^F O| = 2E |cos(Fφ/2)|`. -/
theorem standing_wave_poly (E O ρ φ : ℝ) (F : ℕ) (hE : 0 ≤ E) (hρ : ρ ^ F * O = E) :
    ‖(E : ℂ) + ((ρ : ℂ) * Complex.exp (φ * Complex.I)) ^ F * O‖ =
      2 * E * |Real.cos (F * φ / 2)| := by
  have h : ((ρ : ℂ) * Complex.exp (φ * Complex.I)) ^ F * O =
      E * Complex.exp ((F * φ : ℝ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul, ← hρ]
    push_cast
    ring_nf
  rw [h, standing_wave E (F * φ) hE]

/-- Proposition `ly:prop:2d`: if `E > O > 0` then the Lee–Yang radius exceeds one. -/
theorem radius_gt_one (E O ρ : ℝ) (F : ℕ) (hO : 0 < O) (hEO : O < E)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ^ F * O = E) : 1 < ρ := by
  by_contra h
  push Not at h
  have : ρ ^ F ≤ 1 := pow_le_one₀ hρ0 h
  nlinarith

/-! ## Twists are cocycles: the knot lemma -/

section Knot

variable (L : Fin 4 → ℕ) [∀ μ, NeZero (L μ)]

/-- Sites of the four-torus `∏_μ ℤ/L_μ`; the direction `3` is time. -/
abbrev Site := (μ : Fin 4) → ZMod (L μ)

/-- A cell: a base point and the set of directions it spans. Plaquettes span two directions
and elementary cubes three. -/
abbrev Cell := Site L × Finset (Fin 4)

/-- An oriented link: a base point and a direction. -/
abbrev Link := Site L × Fin 4

/-- The indicator, in `ZMod 2`, of the twist sheet `F_j(c)`: the plaquettes `(x; j, 3)` with
`x_j = c_j` and `x_3 = c_3`. -/
def twist (j : Fin 4) (cj : ZMod (L j)) (c3 : ZMod (L 3)) (p : Cell L) : ZMod 2 :=
  if {j, 3} ⊆ p.2 ∧ p.1 j = cj ∧ p.1 3 = c3 then 1 else 0

/-- The faces of the cell `q = (x, C)` as a `ZMod 2`-chain: for each `c ∈ C`, the two faces
`(x, C \ {c})` and `(x + e_c, C \ {c})`. -/
def faces (q : Cell L) (p : Cell L) : ZMod 2 :=
  ∑ c ∈ q.2, ((if p = (q.1, q.2.erase c) then 1 else 0) +
    (if p = (q.1 + Pi.single c 1, q.2.erase c) then 1 else 0))

/-- The intersection number `I_j(S) = |S ∩ F_j(c)| mod 2` of a `ZMod 2`-chain `S`. -/
def inter (j : Fin 4) (cj : ZMod (L j)) (c3 : ZMod (L 3)) (S : Cell L → ZMod 2) : ZMod 2 :=
  ∑ p, S p * twist L j cj c3 p

/-- The boundary `∂V` of a set `V` of cubes, as a `ZMod 2`-chain. -/
def bdry (V : Cell L → ZMod 2) (p : Cell L) : ZMod 2 :=
  ∑ q, V q * faces L q p

theorem two_eq_zero (t : ZMod 2) : t + t = 0 := by
  fin_cases t <;> decide

/-- Lemma `ly:lem:knot` (a): every cell meets the twist sheet in an even number of faces,
that is, `F_j` is a `ℤ₂` 2-cocycle. -/
theorem faces_twist (j : Fin 4) (cj : ZMod (L j)) (c3 : ZMod (L 3)) (q : Cell L) :
    inter L j cj c3 (faces L q) = 0 := by
  classical
  unfold inter faces
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun c hc => ?_
  simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have heq : twist L j cj c3 (q.1 + Pi.single c 1, q.2.erase c) =
      twist L j cj c3 (q.1, q.2.erase c) := by
    unfold twist
    by_cases h : {j, 3} ⊆ q.2.erase c
    · have hj : j ∈ q.2.erase c := h (by simp)
      have h3 : (3 : Fin 4) ∈ q.2.erase c := h (by simp)
      have hcj : c ≠ j := fun e => by rw [e] at hj; simp at hj
      have hc3 : c ≠ 3 := fun e => by rw [e] at h3; simp at h3
      have e1 : (q.1 + Pi.single c 1 : Site L) j = q.1 j := by
        simp [Pi.single_eq_of_ne (Ne.symm hcj)]
      have e2 : (q.1 + Pi.single c 1 : Site L) 3 = q.1 3 := by
        simp [Pi.single_eq_of_ne (Ne.symm hc3)]
      dsimp only
      simp only [e1, e2]
    · simp [h]
  rw [heq, two_eq_zero]

/-- Lemma `ly:lem:knot` (b): `I_j(S + ∂V) = I_j(S)`. -/
theorem knot_invariance (j : Fin 4) (cj : ZMod (L j)) (c3 : ZMod (L 3))
    (S V : Cell L → ZMod 2) : inter L j cj c3 (S + bdry L V) = inter L j cj c3 S := by
  have hb : inter L j cj c3 (bdry L V) = 0 := by
    unfold inter bdry
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [← Finset.mul_sum]
    have h := faces_twist L j cj c3 q
    unfold inter at h
    rw [h, mul_zero]
  have hadd : inter L j cj c3 (S + bdry L V) =
      inter L j cj c3 S + inter L j cj c3 (bdry L V) := by
    unfold inter
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [add_mul]
  rw [hadd, hb, add_zero]

/-- Lemma `ly:lem:knot` (c): a vortex sheet that bounds, however knotted, meets every twist
sheet an even number of times. -/
theorem knot_bounding (j : Fin 4) (cj : ZMod (L j)) (c3 : ZMod (L 3)) (V : Cell L → ZMod 2) :
    inter L j cj c3 (bdry L V) = 0 := by
  simpa [inter] using knot_invariance L j cj c3 0 V

/-- The far corner `x + ∑_{ν ∈ P} e_ν`. -/
def shift (x : Site L) (P : Finset (Fin 4)) : Site L := x + ∑ ν ∈ P, Pi.single ν 1

/-- The coboundary of a `ZMod 2`-chain `B` of links on the cell `(x, P)`: the sum of `B` over
the links `(x; μ)` and `(x + ∑_{ν ∈ P \ {μ}} e_ν; μ)`, `μ ∈ P`; for a plaquette these are its
four links. -/
def cobdry (B : Link L → ZMod 2) (p : Cell L) : ZMod 2 :=
  ∑ μ ∈ p.2, (B (p.1, μ) + B (shift L p.1 (p.2.erase μ), μ))

/-- The boundary of a `ZMod 2`-chain of cells, the transpose of `cobdry`. -/
def bdry2 (S : Cell L → ZMod 2) (ℓ : Link L) : ZMod 2 :=
  ∑ p, S p * cobdry L (fun ℓ' => if ℓ' = ℓ then 1 else 0) p

/-- `cobdry` is linear: `δB = ∑_ℓ B(ℓ) δ(ℓ)`. -/
theorem cobdry_linear (B : Link L → ZMod 2) (p : Cell L) :
    cobdry L B p = ∑ ℓ, B ℓ * cobdry L (fun ℓ' => if ℓ' = ℓ then 1 else 0) p := by
  unfold cobdry
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp [mul_add, Finset.sum_add_distrib]

/-- Adjointness: `⟨S, δB⟩ = ⟨∂S, B⟩`. In particular a cycle pairs to zero with every
coboundary. -/
theorem pair_cobdry (S : Cell L → ZMod 2) (B : Link L → ZMod 2)
    (hS : ∀ ℓ, bdry2 L S ℓ = 0) : ∑ p, S p * cobdry L B p = 0 := by
  simp_rw [cobdry_linear L B, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun ℓ _ => ?_
  have h := hS ℓ
  unfold bdry2 at h
  calc ∑ p, S p * (B ℓ * cobdry L (fun ℓ' => if ℓ' = ℓ then 1 else 0) p)
      = B ℓ * ∑ p, S p * cobdry L (fun ℓ' => if ℓ' = ℓ then 1 else 0) p := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
    _ = 0 := by rw [h, mul_zero]

omit [∀ μ, NeZero (L μ)] in
theorem shift_apply_of_not_mem (x : Site L) (P : Finset (Fin 4)) (μ : Fin 4) (h : μ ∉ P) :
    shift L x P μ = x μ := by
  unfold shift
  rw [Pi.add_apply, Finset.sum_apply]
  rw [Finset.sum_eq_zero fun ν hν => Pi.single_eq_of_ne (fun e => h (by rw [e]; exact hν)) _]
  rw [add_zero]

omit [∀ μ, NeZero (L μ)] in
theorem shift_apply_of_mem (x : Site L) (P : Finset (Fin 4)) (μ : Fin 4) (h : μ ∈ P) :
    shift L x P μ = x μ + 1 := by
  unfold shift
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_single μ]
  · simp
  · intro ν _ hν; exact Pi.single_eq_of_ne (Ne.symm hν) _
  · intro h'; exact absurd h h'

omit [∀ μ, NeZero (L μ)] in
/-- The twist sheets at neighbouring times differ by a coboundary:
`F_j(c_j, c_3) + F_j(c_j, c_3 + 1) = δB`, with `B` the `j`-links at `x_j = c_j`,
`x_3 = c_3 + 1`. -/
theorem twist_time_step (j : Fin 4) (hj : j ≠ 3) (cj : ZMod (L j)) (c3 : ZMod (L 3))
    (p : Cell L) :
    twist L j cj c3 p + twist L j cj (c3 + 1) p =
      cobdry L (fun ℓ => if ℓ.2 = j ∧ ℓ.1 j = cj ∧ ℓ.1 3 = c3 + 1 then 1 else 0) p := by
  obtain ⟨x, P⟩ := p
  unfold cobdry twist
  dsimp only
  by_cases hjP : j ∈ P
  · rw [Finset.sum_eq_single j]
    · simp only [true_and]
      have hj' : j ∉ P.erase j := by simp
      rw [shift_apply_of_not_mem L x (P.erase j) j hj']
      by_cases h3P : (3 : Fin 4) ∈ P
      · have h3' : (3 : Fin 4) ∈ P.erase j := Finset.mem_erase.mpr ⟨Ne.symm hj, h3P⟩
        rw [shift_apply_of_mem L x (P.erase j) 3 h3']
        have hsub : ({j, 3} : Finset (Fin 4)) ⊆ P := by
          intro μ hμ; simp at hμ; rcases hμ with rfl | rfl <;> assumption
        simp only [hsub, true_and, add_left_inj]
        split_ifs <;> simp_all
      · have h3' : (3 : Fin 4) ∉ P.erase j := fun h => h3P (Finset.mem_of_mem_erase h)
        rw [shift_apply_of_not_mem L x (P.erase j) 3 h3']
        have hsub : ¬ ({j, 3} : Finset (Fin 4)) ⊆ P := fun h => h3P (h (by simp))
        simp only [hsub, false_and, if_false, add_zero]
        rw [two_eq_zero]
    · intro μ _ hμ
      simp [hμ]
    · intro h; exact absurd hjP h
  · have hsub : ¬ ({j, 3} : Finset (Fin 4)) ⊆ P := fun h => hjP (h (by simp))
    simp only [hsub, false_and, if_false, add_zero]
    symm
    refine Finset.sum_eq_zero fun μ hμ => ?_
    have : μ ≠ j := fun e => hjP (e ▸ hμ)
    simp [this]

omit [∀ μ, NeZero (L μ)] in
/-- The twist sheets at neighbouring positions differ by a coboundary:
`F_j(c_j, c_3) + F_j(c_j + 1, c_3) = δB`, with `B` the time links at `x_j = c_j + 1`,
`x_3 = c_3`. -/
theorem twist_space_step (j : Fin 4) (hj : j ≠ 3) (cj : ZMod (L j)) (c3 : ZMod (L 3))
    (p : Cell L) :
    twist L j cj c3 p + twist L j (cj + 1) c3 p =
      cobdry L (fun ℓ => if ℓ.2 = 3 ∧ ℓ.1 j = cj + 1 ∧ ℓ.1 3 = c3 then 1 else 0) p := by
  obtain ⟨x, P⟩ := p
  unfold cobdry twist
  dsimp only
  by_cases h3P : (3 : Fin 4) ∈ P
  · rw [Finset.sum_eq_single 3]
    · simp only [true_and]
      have h3' : (3 : Fin 4) ∉ P.erase 3 := by simp
      rw [shift_apply_of_not_mem L x (P.erase 3) 3 h3']
      by_cases hjP : j ∈ P
      · have hj' : j ∈ P.erase 3 := Finset.mem_erase.mpr ⟨hj, hjP⟩
        rw [shift_apply_of_mem L x (P.erase 3) j hj']
        have hsub : ({j, 3} : Finset (Fin 4)) ⊆ P := by
          intro μ hμ; simp at hμ; rcases hμ with rfl | rfl <;> assumption
        simp only [hsub, true_and, add_left_inj]
        split_ifs <;> simp_all
      · have hj' : j ∉ P.erase 3 := fun h => hjP (Finset.mem_of_mem_erase h)
        rw [shift_apply_of_not_mem L x (P.erase 3) j hj']
        have hsub : ¬ ({j, 3} : Finset (Fin 4)) ⊆ P := fun h => hjP (h (by simp))
        simp only [hsub, false_and, if_false, add_zero]
        rw [two_eq_zero]
    · intro μ _ hμ
      simp [hμ]
    · intro h; exact absurd h3P h
  · have hsub : ¬ ({j, 3} : Finset (Fin 4)) ⊆ P := fun h => h3P (h (by simp))
    simp only [hsub, false_and, if_false, add_zero]
    symm
    refine Finset.sum_eq_zero fun μ hμ => ?_
    have : μ ≠ 3 := fun e => h3P (e ▸ hμ)
    simp [this]

/-- Lemma `ly:lem:knot` (d): for a `ℤ₂` 2-cycle `S`, the parity of `|S ∩ F_j(c)|` does not
depend on `c`. -/
theorem knot_independent (j : Fin 4) (hj : j ≠ 3) (S : Cell L → ZMod 2)
    (hS : ∀ ℓ, bdry2 L S ℓ = 0) (cj cj' : ZMod (L j)) (c3 c3' : ZMod (L 3)) :
    inter L j cj c3 S = inter L j cj' c3' S := by
  have step3 : ∀ (a : ZMod (L j)) (b : ZMod (L 3)), inter L j a (b + 1) S = inter L j a b S := by
    intro a b
    have h := pair_cobdry L S
      (fun ℓ => if ℓ.2 = j ∧ ℓ.1 j = a ∧ ℓ.1 3 = b + 1 then 1 else 0) hS
    simp only [← twist_time_step L j hj a b, mul_add, Finset.sum_add_distrib] at h
    unfold inter
    linear_combination h - two_eq_zero (∑ p, S p * twist L j a b p)
  have stepj : ∀ (a : ZMod (L j)) (b : ZMod (L 3)), inter L j (a + 1) b S = inter L j a b S := by
    intro a b
    have h := pair_cobdry L S
      (fun ℓ => if ℓ.2 = 3 ∧ ℓ.1 j = a + 1 ∧ ℓ.1 3 = b then 1 else 0) hS
    simp only [← twist_space_step L j hj a b, mul_add, Finset.sum_add_distrib] at h
    unfold inter
    linear_combination h - two_eq_zero (∑ p, S p * twist L j a b p)
  have iter3 : ∀ (a : ZMod (L j)) (b : ZMod (L 3)) (k : ℕ),
      inter L j a (b + k) S = inter L j a b S := by
    intro a b k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, ← add_assoc, step3, ih]
  have iterj : ∀ (a : ZMod (L j)) (b : ZMod (L 3)) (k : ℕ),
      inter L j (a + k) b S = inter L j a b S := by
    intro a b k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, ← add_assoc, stepj, ih]
  have e3 : c3' = c3 + ((c3' - c3).val : ZMod (L 3)) := by
    rw [ZMod.natCast_zmod_val]; ring
  have ej : cj' = cj + ((cj' - cj).val : ZMod (L j)) := by
    rw [ZMod.natCast_zmod_val]; ring
  rw [e3, iter3, ej, iterj]

/-- Lemma `ly:lem:areas`: a `ℤ₂` 2-cycle that meets one twist sheet `F_j(c)` an odd number of
times has at least `L_j L_3` cells. On `Λ₁(T)`, with `L_j = 2T` and `L_3 = T`, this is
`2T²`. -/
theorem area_bound (j : Fin 4) (hj : j ≠ 3) (S : Cell L → ZMod 2)
    (hS : ∀ ℓ, bdry2 L S ℓ = 0) (cj : ZMod (L j)) (c3 : ZMod (L 3))
    (hodd : inter L j cj c3 S ≠ 0) :
    L j * L 3 ≤ (Finset.univ.filter fun p => S p ≠ 0).card := by
  classical
  have hex : ∀ c : ZMod (L j) × ZMod (L 3), ∃ p : Cell L, S p * twist L j c.1 c.2 p ≠ 0 := by
    intro c
    have h : inter L j c.1 c.2 S ≠ 0 := by
      rwa [knot_independent L j hj S hS c.1 cj c.2 c3]
    unfold inter at h
    obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ⟨p, hp⟩
  choose f hf using hex
  have hfS : ∀ c, S (f c) ≠ 0 := fun c h => hf c (by rw [h, zero_mul])
  have hft : ∀ c, (f c).1 j = c.1 ∧ (f c).1 3 = c.2 := by
    intro c
    have h := hf c
    unfold twist at h
    split_ifs at h with h'
    · exact ⟨h'.2.1, h'.2.2⟩
    · simp at h
  let g : ZMod (L j) × ZMod (L 3) → {p // p ∈ Finset.univ.filter fun p => S p ≠ 0} :=
    fun c => ⟨f c, by simp [hfS c]⟩
  have hg : Function.Injective g := by
    intro c c' h
    have h' : f c = f c' := congrArg Subtype.val h
    ext
    · rw [← (hft c).1, ← (hft c').1, h']
    · rw [← (hft c).2, ← (hft c').2, h']
  have := Fintype.card_le_of_injective g hg
  rw [Fintype.card_prod, ZMod.card, ZMod.card, Fintype.card_coe] at this
  exact this

end Knot

/-! ## Vanishing order `4T`: the counting -/

/-- The slab count of Lemma `ly:lem:van`: if `g n ≤ m < 4T`, then `n < T` when `g = 4` and
`n < 2T` when `g ≥ 3`. -/
theorem slab_count (T m n g : ℕ) (hm : m < 4 * T) (hg : g * n ≤ m) :
    (g = 4 → n < T) ∧ (3 ≤ g → n < 2 * T) := by
  refine ⟨fun h => by subst h; omega, fun h => ?_⟩
  have : 3 * n ≤ g * n := Nat.mul_le_mul_right n h
  omega

/-- The datum tori: `|V(Λ₁(T))| = 8T⁴`, `|V(Λ₂(T))| = 16T⁴ = 2|V(Λ₁(T))|`, and with six
plaquettes per site `|P(Λ₁)| = 48T⁴`, `|P(Λ₂)| = 96T⁴`. -/
theorem plaquette_counts (T : ℕ) :
    (2 * T) ^ 3 * T = 8 * T ^ 4 ∧ (2 * T) ^ 4 = 2 * ((2 * T) ^ 3 * T) ∧
      6 * ((2 * T) ^ 3 * T) = 48 * T ^ 4 ∧ 6 * (2 * T) ^ 4 = 96 * T ^ 4 := by
  refine ⟨by ring, by ring, by ring, by ring⟩

/-! ## Theorem A -/

/-- The tail sum of Theorem `ly:thm:A`:
`∑_{k ≥ A} R^{-k}/k ≤ (1/A) R^{-A}/(1 - R^{-1})`. -/
theorem tail_sum (R : ℝ) (hR : 1 < R) (A : ℕ) (hA : 0 < A) :
    ∑' k : ℕ, R⁻¹ ^ (k + A) / ((k : ℝ) + A) ≤ R⁻¹ ^ A / A / (1 - R⁻¹) := by
  have hr0 : 0 ≤ R⁻¹ := inv_nonneg.mpr (by linarith)
  have hr1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hA' : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hgeom : HasSum (fun k : ℕ => R⁻¹ ^ A / A * R⁻¹ ^ k) (R⁻¹ ^ A / A * (1 - R⁻¹)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left _
  have hle : ∀ k : ℕ, R⁻¹ ^ (k + A) / ((k : ℝ) + A) ≤ R⁻¹ ^ A / A * R⁻¹ ^ k := by
    intro k
    rw [pow_add, div_mul_eq_mul_div, mul_comm (R⁻¹ ^ k)]
    apply div_le_div_of_nonneg_left (by positivity) hA'
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hsum : Summable (fun k : ℕ => R⁻¹ ^ (k + A) / ((k : ℝ) + A)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hle hgeom.summable
  calc _ ≤ R⁻¹ ^ A / A * (1 - R⁻¹)⁻¹ := hasSum_le hle hsum.hasSum hgeom
    _ = _ := by rw [div_eq_mul_inv (R⁻¹ ^ A / A)]

/-- Theorem `ly:thm:A`, the estimate: if the power sums of the zeros of `𝒫` and `𝒫_ζ` are
bounded by `|P| R^{-k}` and agree below `A`, the difference series is bounded by
`(2|P|/A) R^{-A}/(1 - R^{-1})`. Here `d k = q_k - p_k`. -/
theorem theoremA_tail (R N : ℝ) (hR : 1 < R) (A : ℕ) (hA : 0 < A) (d : ℕ → ℂ)
    (hd : ∀ k, ‖d k‖ ≤ 2 * N * R⁻¹ ^ k) :
    ‖∑' k : ℕ, d (k + A) / ((k : ℂ) + A)‖ ≤ 2 * N / A * R⁻¹ ^ A / (1 - R⁻¹) := by
  have hr0 : 0 ≤ R⁻¹ := inv_nonneg.mpr (by linarith)
  have hN : 0 ≤ N := by
    have := (norm_nonneg (d 0)).trans (hd 0)
    simp at this
    linarith
  have hb : ∀ k : ℕ, ‖d (k + A) / ((k : ℂ) + A)‖ ≤ 2 * N * (R⁻¹ ^ (k + A) / ((k : ℝ) + A)) := by
    intro k
    rw [norm_div]
    have h1 : ‖((k : ℂ) + A)‖ = (k : ℝ) + A := by
      have : ((k : ℂ) + A) = (((k : ℝ) + A : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h1, mul_div_assoc']
    exact div_le_div_of_nonneg_right (hd _) (by positivity)
  have hsum : Summable (fun k : ℕ => R⁻¹ ^ (k + A) / ((k : ℝ) + A)) := by
    have hr1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (R⁻¹ ^ A))
    rw [pow_add, mul_comm (R⁻¹ ^ k)]
    apply div_le_self (by positivity)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : (1 : ℝ) ≤ A := by exact_mod_cast hA
    linarith
  have hsn : Summable (fun k : ℕ => ‖d (k + A) / ((k : ℂ) + A)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hsum.mul_left _)
  calc ‖∑' k : ℕ, d (k + A) / ((k : ℂ) + A)‖
      ≤ ∑' k : ℕ, ‖d (k + A) / ((k : ℂ) + A)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' k : ℕ, 2 * N * (R⁻¹ ^ (k + A) / ((k : ℝ) + A)) :=
        hsn.tsum_le_tsum hb (hsum.mul_left _)
    _ = 2 * N * ∑' k : ℕ, R⁻¹ ^ (k + A) / ((k : ℝ) + A) := tsum_mul_left
    _ ≤ 2 * N * (R⁻¹ ^ A / A / (1 - R⁻¹)) :=
        mul_le_mul_of_nonneg_left (tail_sum R hR A hA) (by positivity)
    _ = _ := by ring

/-- Corollary `ly:cor:fluxhalf`, the last step: `-log(1 - (7/8)/7169) ≤ 7/57345 < 1/8192`. -/
theorem fluxhalf_log : (7 : ℝ) / 8 * (1 / 7169) = 7 / 57352 ∧
    -Real.log (1 - 7 / 57352) ≤ 7 / 57345 ∧ (7 : ℝ) / 57345 < 1 / 8192 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 - 7 / 57352 by norm_num)
  have : 1 - (1 - (7 : ℝ) / 57352)⁻¹ = -(7 / 57345) := by norm_num
  linarith

/-- The flux-half criterion of Corollary `ly:cor:fluxhalf` at `(T₀, R)`. -/
def FluxCrit (T0 : ℕ) (R : ℝ) : Prop :=
  48 * (T0 : ℝ) ^ 2 * R⁻¹ ^ (2 * T0 ^ 2) / (1 - R⁻¹) ≤ 1 / 7169

/-- The criterion follows from `48 T₀² · 7169 · R ≤ R^{2T₀²} (R - 1)`. -/
theorem fluxCrit_of (T0 : ℕ) (R : ℝ) (hR : 1 < R)
    (h : 48 * (T0 : ℝ) ^ 2 * 7169 * R ≤ R ^ (2 * T0 ^ 2) * (R - 1)) : FluxCrit T0 R := by
  unfold FluxCrit
  have hR0 : 0 < R := by linarith
  have hpos : 0 < R ^ (2 * T0 ^ 2) := by positivity
  have h1 : 0 < 1 - R⁻¹ := by have := inv_lt_one_of_one_lt₀ hR; linarith
  rw [div_le_div_iff₀ h1 (by norm_num), inv_pow, ← sub_nonneg]
  have e : 1 * (1 - R⁻¹) - 48 * (T0 : ℝ) ^ 2 * (R ^ (2 * T0 ^ 2))⁻¹ * 7169 =
      (R ^ (2 * T0 ^ 2) * (R - 1) - 48 * (T0 : ℝ) ^ 2 * 7169 * R) / (R * R ^ (2 * T0 ^ 2)) := by
    field_simp
  rw [e]
  exact div_nonneg (by linarith) (by positivity)

/-- The same with the power split as `R^{ka} ≥ q^a` for a rational `q ≤ R^k`. -/
theorem fluxCrit_split (T0 k a : ℕ) (R q : ℝ) (hR : 1 < R) (hka : 2 * T0 ^ 2 = k * a)
    (hq0 : 0 ≤ q) (hq : q ≤ R ^ k) (h : 48 * (T0 : ℝ) ^ 2 * 7169 * R ≤ q ^ a * (R - 1)) :
    FluxCrit T0 R := by
  apply fluxCrit_of T0 R hR
  rw [hka, pow_mul]
  calc _ ≤ q ^ a * (R - 1) := h
    _ ≤ (R ^ k) ^ a * (R - 1) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq a) (by linarith)

/-- Item (C3): the radii quoted in Corollary `ly:cor:fluxhalf` satisfy the criterion. -/
theorem fluxCrit_values : FluxCrit 3 2.3652 ∧ FluxCrit 4 1.6713 ∧ FluxCrit 5 1.4107 ∧
    FluxCrit 6 1.2814 ∧ FluxCrit 8 1.1591 ∧ FluxCrit 10 1.1037 ∧ FluxCrit 12 1.0735 ∧
    FluxCrit 16 1.0429 ∧ FluxCrit 20 1.0284 ∧ FluxCrit 30 1.0134 ∧ FluxCrit 50 1.0052 ∧
    FluxCrit 100 1.0015 := by
  refine ⟨fluxCrit_of 3 _ (by norm_num) (by norm_num), fluxCrit_of 4 _ (by norm_num) (by norm_num),
    fluxCrit_of 5 _ (by norm_num) (by norm_num), fluxCrit_of 6 _ (by norm_num) (by norm_num),
    fluxCrit_of 8 _ (by norm_num) (by norm_num), fluxCrit_of 10 _ (by norm_num) (by norm_num),
    fluxCrit_split 12 144 2 _ (5451613 / 200) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num),
    fluxCrit_split 16 128 4 _ (135189 / 625) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num),
    fluxCrit_split 20 200 4 _ (1353267 / 5000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num),
    fluxCrit_split 30 200 9 _ (71639 / 5000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num),
    fluxCrit_split 50 200 25 _ (3527 / 1250) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num),
    fluxCrit_split 100 200 100 _ (26991 / 20000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)⟩

/-- Theorem `ly:thm:Adomain`, the factor bound: `|w₊ + θ w₋| ≤ (1 + |θ|) w₊` when `|w₋| ≤ w₊`. -/
theorem vortex_factor_bound (wp wm : ℝ) (θ : ℂ) (h : |wm| ≤ wp) :
    ‖(wp : ℂ) + θ * wm‖ ≤ (1 + ‖θ‖) * wp := by
  have hwp : 0 ≤ wp := (abs_nonneg _).trans h
  calc ‖(wp : ℂ) + θ * wm‖ ≤ ‖(wp : ℂ)‖ + ‖θ‖ * ‖(wm : ℂ)‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ = wp + ‖θ‖ * |wm| := by
        rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hwp]
    _ ≤ wp + ‖θ‖ * wp := by gcongr
    _ = (1 + ‖θ‖) * wp := by ring

/-! ## Theorem B -/

/-- Lemma `ly:lem:BC` (Borel–Carathéodory on the unit disc). -/
theorem borel_caratheodory_disc {f : ℂ → ℂ} {M : ℝ} (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hre : ∀ v ∈ ball (0 : ℂ) 1, (f v).re ≤ M)
    (h0 : f 0 = 0) {v : ℂ} (hv : v ∈ ball (0 : ℂ) 1) :
    ‖f v‖ ≤ 2 * M * ‖v‖ / (1 - ‖v‖) :=
  Complex.borelCaratheodory_zero hM hf (fun w hw => hre w hw) one_pos hv h0

/-- `t ↦ t/(1-t)` is monotone on `[0,1)`. -/
theorem ratio_mono {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    a / (1 - a) ≤ b / (1 - b) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- A function vanishing to order `n + 1` at the origin vanishes there. -/
theorem eq_zero_of_isLittleO {F : ℂ → ℂ} {n : ℕ} (h : F =o[𝓝 0] fun v => ‖v‖ ^ n) :
    F 0 = 0 := by
  have key : ∀ ε : ℝ, 0 < ε → ‖F 0‖ ≤ ε * ‖‖(0 : ℂ)‖ ^ n‖ := fun ε hε =>
    (h.def hε).self_of_nhds
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [pow_zero, norm_one, mul_one] at key
    exact norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => by simpa using key ε hε)
  · have := key 1 one_pos
    simp [zero_pow hn.ne'] at this
    exact this

/-- The transport step of Theorem `ly:thm:B`: if `F` is analytic on the unit disc with
`|F(v)| ≤ K|v|/(1-|v|)` and vanishes to order `n+1` at `0`, then for `|z| ≤ ρ < 1`,
`|F(z)| ≤ K ρ/(1-ρ) (|z|/ρ)^{n+1}` (Schwarz's lemma of order `n+1` on the disc `|v| < ρ`). -/
theorem transport {F : ℂ → ℂ} {K ρ : ℝ} {n : ℕ} (hK : 0 ≤ K)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hbound : ∀ v ∈ ball (0 : ℂ) 1, ‖F v‖ ≤ K * ‖v‖ / (1 - ‖v‖))
    (hvan : F =o[𝓝 0] fun v => ‖v‖ ^ n) {z : ℂ} (hz : ‖z‖ ≤ ρ) (hρ : ρ < 1) :
    ‖F z‖ ≤ K * (ρ / (1 - ρ)) * (‖z‖ / ρ) ^ (n + 1) := by
  have hF0 : F 0 = 0 := eq_zero_of_isLittleO hvan
  have hρ0 : 0 ≤ ρ := (norm_nonneg z).trans hz
  have hz1 : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (lt_of_le_of_lt hz hρ)
  rcases eq_or_lt_of_le hz with h | h
  · -- `|z| = ρ`: the Borel–Carathéodory bound itself
    rcases eq_or_lt_of_le hρ0 with h0 | h0
    · have : z = 0 := norm_eq_zero.mp (h.trans h0.symm)
      rw [this, hF0, norm_zero]
      rw [← h0]; simp
    · rw [h, div_self h0.ne', one_pow, mul_one]
      have := hbound z hz1
      rw [h] at this
      calc ‖F z‖ ≤ K * ρ / (1 - ρ) := this
        _ = K * (ρ / (1 - ρ)) := by ring
  · -- `|z| < ρ`: Schwarz's lemma of order `n + 1` on the disc of radius `ρ`
    have hmaps : Set.MapsTo F (ball 0 ρ) (closedBall (F 0) (K * (ρ / (1 - ρ)))) := by
      intro w hw
      rw [mem_ball_zero_iff] at hw
      rw [mem_closedBall, hF0, dist_zero_right]
      have hw1 : w ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hw.trans hρ)
      calc ‖F w‖ ≤ K * ‖w‖ / (1 - ‖w‖) := hbound w hw1
        _ = K * (‖w‖ / (1 - ‖w‖)) := by ring
        _ ≤ K * (ρ / (1 - ρ)) :=
          mul_le_mul_of_nonneg_left (ratio_mono hw.le hρ) hK
    have hvan' : (fun w => F w - F 0) =o[𝓝 0] fun w => ‖w - 0‖ ^ n := by
      simpa [hF0] using hvan
    have := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
      (hF.mono (ball_subset_ball hρ.le)) hmaps hvan' (mem_ball_zero_iff.mpr h)
    simpa [hF0, dist_zero_right] using this

/-- The real part of `g = log Z - Pβ` in Theorem `ly:thm:B`: if `e^g = Z e^{-Pβ}`,
`|Z| ≤ e^{P |Re β|}` and `Re β ≥ -s` with `s ≥ 0`, then `Re g ≤ 2 s P`. -/
theorem re_log_bound {g Z β : ℂ} {P s : ℝ} (hP : 0 ≤ P) (hs0 : 0 ≤ s) (hs : -s ≤ β.re)
    (hg : Complex.exp g = Z * Complex.exp (-((P : ℂ) * β)))
    (hZ : ‖Z‖ ≤ Real.exp (P * |β.re|)) : g.re ≤ 2 * s * P := by
  have h1 : Real.exp g.re = ‖Z‖ * Real.exp (-(P * β.re)) := by
    rw [← Complex.norm_exp, hg, norm_mul, Complex.norm_exp]
    simp [Complex.mul_re]
  have h2 : Real.exp g.re ≤ Real.exp (P * |β.re| - P * β.re) := by
    rw [h1, Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
    exact mul_le_mul_of_nonneg_right hZ (Real.exp_pos _).le
  have h3 := Real.exp_le_exp.mp h2
  have h4 : P * |β.re| - P * β.re ≤ 2 * s * P := by
    rcases le_or_gt 0 β.re with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_neg h]; nlinarith
  linarith

/-- The Wilson weight bound `|∏_p e^{β c_p}| ≤ e^{|P| |Re β|}` for `|c_p| ≤ 1`, which gives
`|Z_Λ(β)| ≤ e^{|P| |Re β|}` after integration against a probability measure. -/
theorem wilson_weight_bound {ι : Type*} (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ s, |c i| ≤ 1)
    (β : ℂ) : ‖∏ i ∈ s, Complex.exp (β * c i)‖ ≤ Real.exp (s.card * |β.re|) := by
  rw [Complex.norm_prod]
  calc ∏ i ∈ s, ‖Complex.exp (β * c i)‖ ≤ ∏ i ∈ s, Real.exp |β.re| := by
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => ?_
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        have : (β * (c i : ℂ)).re = β.re * c i := by simp [Complex.mul_re]
        rw [this]
        calc β.re * c i ≤ |β.re * c i| := le_abs_self _
          _ = |β.re| * |c i| := abs_mul _ _
          _ ≤ |β.re| * 1 := mul_le_mul_of_nonneg_left (hc i hi) (abs_nonneg _)
          _ = |β.re| := mul_one _
    _ = Real.exp (s.card * |β.re|) := by
        rw [Finset.prod_const, ← Real.exp_nat_mul]

/-- The partition-function bound: for a probability measure and an integrand bounded by
`e^{|P| |Re β|}`, `|Z| ≤ e^{|P| |Re β|}`. -/
theorem partition_bound {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (f : Ω → ℂ) (C : ℝ) (hf : ∀ ω, ‖f ω‖ ≤ C) :
    ‖∫ ω, f ω ∂μ‖ ≤ C := by
  have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall hf)
  simpa using this

/-- Theorem `ly:thm:B`, first bound, for any analytic map `φ` of the unit disc into the
zero-free domain `D` with `φ 0 = 0` (for instance the inverse of a Riemann map, or a universal
covering map of a multiply connected zero-free region). Here `g_i = log Z_{Λ_i} - |P_i| β`
are the branches on `D` with `g_i(0) = 0`, and `ψ_T = 2 g₁ - g₂`. -/
theorem theoremB {D : Set ℂ} {g₁ g₂ φ : ℂ → ℂ} {s P₁ P₂ ρ : ℝ} {n : ℕ} {v₁ : ℂ}
    (hs : 0 < s) (hP₁ : 0 < P₁) (hP₂ : 0 < P₂)
    (hφ : DifferentiableOn ℂ φ (ball 0 1)) (hφD : Set.MapsTo φ (ball 0 1) D) (hφ0 : φ 0 = 0)
    (hg₁ : DifferentiableOn ℂ g₁ D) (hg₂ : DifferentiableOn ℂ g₂ D)
    (hg₁0 : g₁ 0 = 0) (hg₂0 : g₂ 0 = 0)
    (hre₁ : ∀ β ∈ D, (g₁ β).re ≤ 2 * s * P₁) (hre₂ : ∀ β ∈ D, (g₂ β).re ≤ 2 * s * P₂)
    (hvan : (fun β => 2 * g₁ β - g₂ β) =o[𝓝 0] fun β => ‖β‖ ^ n)
    (hv₁ : ‖v₁‖ ≤ ρ) (hρ : ρ < 1) :
    ‖2 * g₁ (φ v₁) - g₂ (φ v₁)‖ ≤
      (8 * s * P₁ + 4 * s * P₂) * (ρ / (1 - ρ)) * (‖v₁‖ / ρ) ^ (n + 1) := by
  set G₁ := g₁ ∘ φ
  set G₂ := g₂ ∘ φ
  have hG₁ : DifferentiableOn ℂ G₁ (ball 0 1) := hg₁.comp hφ hφD
  have hG₂ : DifferentiableOn ℂ G₂ (ball 0 1) := hg₂.comp hφ hφD
  have hG₁0 : G₁ 0 = 0 := by simp [G₁, hφ0, hg₁0]
  have hG₂0 : G₂ 0 = 0 := by simp [G₂, hφ0, hg₂0]
  have hb₁ : ∀ v ∈ ball (0 : ℂ) 1, ‖G₁ v‖ ≤ 2 * (2 * s * P₁) * ‖v‖ / (1 - ‖v‖) :=
    fun v hv => borel_caratheodory_disc (by positivity) hG₁
      (fun w hw => hre₁ _ (hφD hw)) hG₁0 hv
  have hb₂ : ∀ v ∈ ball (0 : ℂ) 1, ‖G₂ v‖ ≤ 2 * (2 * s * P₂) * ‖v‖ / (1 - ‖v‖) :=
    fun v hv => borel_caratheodory_disc (by positivity) hG₂
      (fun w hw => hre₂ _ (hφD hw)) hG₂0 hv
  set F : ℂ → ℂ := fun v => 2 * G₁ v - G₂ v with hFdef
  have hF : DifferentiableOn ℂ F (ball 0 1) :=
    (hG₁.const_mul 2).sub hG₂
  have hFb : ∀ v ∈ ball (0 : ℂ) 1,
      ‖F v‖ ≤ (8 * s * P₁ + 4 * s * P₂) * ‖v‖ / (1 - ‖v‖) := by
    intro v hv
    have h1 := hb₁ v hv
    have h2 := hb₂ v hv
    have hv1 : 0 < 1 - ‖v‖ := by rw [mem_ball_zero_iff] at hv; linarith
    calc ‖F v‖ ≤ ‖2 * G₁ v‖ + ‖G₂ v‖ := norm_sub_le _ _
      _ = 2 * ‖G₁ v‖ + ‖G₂ v‖ := by rw [norm_mul]; norm_num
      _ ≤ 2 * (2 * (2 * s * P₁) * ‖v‖ / (1 - ‖v‖)) + 2 * (2 * s * P₂) * ‖v‖ / (1 - ‖v‖) := by
          linarith
      _ = (8 * s * P₁ + 4 * s * P₂) * ‖v‖ / (1 - ‖v‖) := by ring
  -- the vanishing order survives composition with `φ`
  have hφd : DifferentiableAt ℂ φ 0 := hφ.differentiableAt (ball_mem_nhds 0 one_pos)
  have hφO : φ =O[𝓝 0] fun v => v := by
    have := hφd.hasFDerivAt.isBigO_sub
    simpa [hφ0] using this
  have hφt : Filter.Tendsto φ (𝓝 0) (𝓝 0) := by
    have := hφd.continuousAt.tendsto
    rwa [hφ0] at this
  have hFvan : F =o[𝓝 0] fun v => ‖v‖ ^ n := by
    have h1 : F =o[𝓝 0] fun v => ‖φ v‖ ^ n := by
      have := hvan.comp_tendsto hφt
      simpa [F, G₁, G₂, Function.comp_def] using this
    have h2 : (fun v => ‖φ v‖ ^ n) =O[𝓝 0] fun v : ℂ => ‖v‖ ^ n :=
      hφO.norm_norm.pow n
    exact h1.trans_isBigO h2
  have := transport (by positivity) hF hFb hFvan hv₁ hρ
  simpa [F, G₁, G₂] using this

/-- `(1 - 1/k)^k ≥ 1/4` for every integer `k ≥ 2`. -/
theorem one_sub_inv_pow_ge (k : ℕ) (hk : 2 ≤ k) : (1 / 4 : ℝ) ≤ (1 - 1 / (k : ℝ)) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hx : (2 : ℝ) ≤ k := by exact_mod_cast hk
    set x : ℝ := (k : ℝ) with hxdef
    have hx2 : 0 < x ^ 2 - 1 := by nlinarith
    have hb : 1 + (k : ℝ) * (1 / (x ^ 2 - 1)) ≤ (1 + 1 / (x ^ 2 - 1)) ^ k :=
      one_add_mul_le_pow (by have : 0 ≤ 1 / (x ^ 2 - 1) := by positivity
                             linarith) k
    have e1 : (1 - 1 / ((k + 1 : ℕ) : ℝ)) = x / (x + 1) := by
      push_cast; field_simp; ring
    have e2 : x / (x + 1) = (1 - 1 / x) * (1 + 1 / (x ^ 2 - 1)) := by
      field_simp; ring
    rw [e1, pow_succ, e2, mul_pow]
    have hpos : 0 ≤ (1 - 1 / x) ^ k := by
      apply pow_nonneg; rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have hkey : 1 ≤ (1 + (k : ℝ) * (1 / (x ^ 2 - 1))) * ((1 - 1 / x) * (1 + 1 / (x ^ 2 - 1))) := by
      rw [← hxdef]
      rw [show (1 + x * (1 / (x ^ 2 - 1))) * ((1 - 1 / x) * (1 + 1 / (x ^ 2 - 1))) =
        x * (x ^ 2 + x - 1) / ((x + 1) * (x ^ 2 - 1)) by field_simp; ring]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    calc (1 / 4 : ℝ) ≤ (1 - 1 / x) ^ k := ih
      _ ≤ (1 - 1 / x) ^ k *
          ((1 + (k : ℝ) * (1 / (x ^ 2 - 1))) * ((1 - 1 / x) * (1 + 1 / (x ^ 2 - 1)))) :=
          le_mul_of_one_le_right hpos hkey
      _ ≤ (1 - 1 / x) ^ k * ((1 + 1 / (x ^ 2 - 1)) ^ k * ((1 - 1 / x) * (1 + 1 / (x ^ 2 - 1)))) := by
          apply mul_le_mul_of_nonneg_left _ hpos
          apply mul_le_mul_of_nonneg_right hb
          apply mul_nonneg
          · rw [sub_nonneg, div_le_one (by linarith)]; linarith
          · positivity
      _ = (1 - 1 / x) ^ k * (1 + 1 / (x ^ 2 - 1)) ^ k * ((1 - 1 / x) * (1 + 1 / (x ^ 2 - 1))) := by
          ring

/-- Theorem `ly:thm:B`, second bound: with `|P₁| = 48T⁴`, `|P₂| = 96T⁴`, vanishing order `4T`
and `ω = |v₁| ≤ 1 - 1/(4T)`, `|ψ_T(β₁)| ≤ 12288 s T⁵ ω^{4T}`. -/
theorem theoremB_zstar {D : Set ℂ} {g₁ g₂ φ : ℂ → ℂ} {s : ℝ} {T : ℕ} {v₁ : ℂ}
    (hT : 1 ≤ T) (hs : 0 < s)
    (hφ : DifferentiableOn ℂ φ (ball 0 1)) (hφD : Set.MapsTo φ (ball 0 1) D) (hφ0 : φ 0 = 0)
    (hg₁ : DifferentiableOn ℂ g₁ D) (hg₂ : DifferentiableOn ℂ g₂ D)
    (hg₁0 : g₁ 0 = 0) (hg₂0 : g₂ 0 = 0)
    (hre₁ : ∀ β ∈ D, (g₁ β).re ≤ 2 * s * (48 * (T : ℝ) ^ 4))
    (hre₂ : ∀ β ∈ D, (g₂ β).re ≤ 2 * s * (96 * (T : ℝ) ^ 4))
    (hvan : (fun β => 2 * g₁ β - g₂ β) =o[𝓝 0] fun β => ‖β‖ ^ (4 * T - 1))
    (hω : ‖v₁‖ ≤ 1 - 1 / (4 * (T : ℝ))) :
    ‖2 * g₁ (φ v₁) - g₂ (φ v₁)‖ ≤ 12288 * s * (T : ℝ) ^ 5 * ‖v₁‖ ^ (4 * T) := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set ρ : ℝ := 1 - 1 / (4 * (T : ℝ)) with hρdef
  have hρ1 : ρ < 1 := by rw [hρdef]; have : 0 < 1 / (4 * (T : ℝ)) := by positivity
                         linarith
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    have : 1 / (4 * (T : ℝ)) ≤ 1 / 4 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
    linarith
  have hB := theoremB hs (by positivity : (0 : ℝ) < 48 * (T : ℝ) ^ 4)
    (by positivity : (0 : ℝ) < 96 * (T : ℝ) ^ 4) hφ hφD hφ0 hg₁ hg₂ hg₁0 hg₂0 hre₁ hre₂ hvan
    hω hρ1
  have hn : 4 * T - 1 + 1 = 4 * T := by omega
  rw [hn] at hB
  have hratio : ρ / (1 - ρ) ≤ 4 * T := by
    rw [hρdef, sub_sub_cancel, div_le_iff₀ (by positivity)]
    field_simp
    linarith
  have hpow : (1 / 4 : ℝ) ≤ ρ ^ (4 * T) := by
    have := one_sub_inv_pow_ge (4 * T) (by omega)
    rw [hρdef]; push_cast at this ⊢; exact this
  have hdiv : (‖v₁‖ / ρ) ^ (4 * T) ≤ 4 * ‖v₁‖ ^ (4 * T) := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have : 0 ≤ ‖v₁‖ ^ (4 * T) := by positivity
    nlinarith
  calc ‖2 * g₁ (φ v₁) - g₂ (φ v₁)‖
      ≤ (8 * s * (48 * (T : ℝ) ^ 4) + 4 * s * (96 * (T : ℝ) ^ 4)) * (ρ / (1 - ρ)) *
          (‖v₁‖ / ρ) ^ (4 * T) := hB
    _ ≤ (8 * s * (48 * (T : ℝ) ^ 4) + 4 * s * (96 * (T : ℝ) ^ 4)) * (4 * T) *
          (4 * ‖v₁‖ ^ (4 * T)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hdiv
          (by positivity) (by positivity)
    _ = 12288 * s * (T : ℝ) ^ 5 * ‖v₁‖ ^ (4 * T) := by ring

/-- Theorem `ly:thm:Adomain`: for an analytic map `φ` of the unit disc into the zero-free
domain `D` with `φ 0 = 0`, and branches `f, f_ζ` of `log(𝒫/𝒫(0))`, `log(𝒫_ζ/𝒫(0))` on `D`
with real parts at most `M = |P| log(1 + Θ)` and difference vanishing to order `A = n + 1`,
`|f_ζ(φ v₁) - f(φ v₁)| ≤ 4 M ρ/(1-ρ) (|v₁|/ρ)^A`. -/
theorem theoremA_domain {D : Set ℂ} {f fζ φ : ℂ → ℂ} {M ρ : ℝ} {n : ℕ} {v₁ : ℂ}
    (hM : 0 < M)
    (hφ : DifferentiableOn ℂ φ (ball 0 1)) (hφD : Set.MapsTo φ (ball 0 1) D) (hφ0 : φ 0 = 0)
    (hf : DifferentiableOn ℂ f D) (hfζ : DifferentiableOn ℂ fζ D)
    (hf0 : f 0 = 0) (hfζ0 : fζ 0 = 0)
    (hre : ∀ θ ∈ D, (f θ).re ≤ M) (hreζ : ∀ θ ∈ D, (fζ θ).re ≤ M)
    (hvan : (fun θ => fζ θ - f θ) =o[𝓝 0] fun θ => ‖θ‖ ^ n)
    (hv₁ : ‖v₁‖ ≤ ρ) (hρ : ρ < 1) :
    ‖fζ (φ v₁) - f (φ v₁)‖ ≤ 4 * M * (ρ / (1 - ρ)) * (‖v₁‖ / ρ) ^ (n + 1) := by
  set G := f ∘ φ
  set Gζ := fζ ∘ φ
  have hG : DifferentiableOn ℂ G (ball 0 1) := hf.comp hφ hφD
  have hGζ : DifferentiableOn ℂ Gζ (ball 0 1) := hfζ.comp hφ hφD
  have hG0 : G 0 = 0 := by simp [G, hφ0, hf0]
  have hGζ0 : Gζ 0 = 0 := by simp [Gζ, hφ0, hfζ0]
  have hb : ∀ v ∈ ball (0 : ℂ) 1, ‖G v‖ ≤ 2 * M * ‖v‖ / (1 - ‖v‖) :=
    fun v hv => borel_caratheodory_disc hM hG (fun w hw => hre _ (hφD hw)) hG0 hv
  have hbζ : ∀ v ∈ ball (0 : ℂ) 1, ‖Gζ v‖ ≤ 2 * M * ‖v‖ / (1 - ‖v‖) :=
    fun v hv => borel_caratheodory_disc hM hGζ (fun w hw => hreζ _ (hφD hw)) hGζ0 hv
  set F : ℂ → ℂ := fun v => Gζ v - G v with hFdef
  have hF : DifferentiableOn ℂ F (ball 0 1) := hGζ.sub hG
  have hFb : ∀ v ∈ ball (0 : ℂ) 1, ‖F v‖ ≤ 4 * M * ‖v‖ / (1 - ‖v‖) := by
    intro v hv
    have h1 := hb v hv
    have h2 := hbζ v hv
    calc ‖F v‖ ≤ ‖Gζ v‖ + ‖G v‖ := norm_sub_le _ _
      _ ≤ 2 * M * ‖v‖ / (1 - ‖v‖) + 2 * M * ‖v‖ / (1 - ‖v‖) := add_le_add h2 h1
      _ = 4 * M * ‖v‖ / (1 - ‖v‖) := by ring
  have hφd : DifferentiableAt ℂ φ 0 := hφ.differentiableAt (ball_mem_nhds 0 one_pos)
  have hφO : φ =O[𝓝 0] fun v => v := by
    have := hφd.hasFDerivAt.isBigO_sub
    simpa [hφ0] using this
  have hφt : Filter.Tendsto φ (𝓝 0) (𝓝 0) := by
    have := hφd.continuousAt.tendsto
    rwa [hφ0] at this
  have hFvan : F =o[𝓝 0] fun v => ‖v‖ ^ n := by
    have h1 : F =o[𝓝 0] fun v => ‖φ v‖ ^ n := by
      have := hvan.comp_tendsto hφt
      simpa [F, G, Gζ, Function.comp_def] using this
    exact h1.trans_isBigO (hφO.norm_norm.pow n)
  have := transport (by positivity) hF hFb hFvan hv₁ hρ
  simpa [F, G, Gζ] using this

/-- Theorem `ly:thm:B`, last sentence: `Z*(T, β₁)` gives `ψ_T(β₁) ≤ 1/4097`. -/
theorem zstar_Mcirc {ψ s ω : ℝ} {T : ℕ} (hψ : ψ ≤ 12288 * s * (T : ℝ) ^ 5 * ω ^ (4 * T))
    (hZ : 12288 * s * (T : ℝ) ^ 5 * ω ^ (4 * T) ≤ 1 / 4097) : ψ ≤ 1 / 4097 :=
  hψ.trans hZ

/-! ## Half-strips: Corollary `ly:cor:strip` -/

/-- The Möbius map `S ↦ (S - S₀)/(S + S₀)`, `S₀ > 0`, sends the right half-plane into the unit
disc. -/
theorem mobius_disc (S : ℂ) {S₀ : ℝ} (h0 : 0 < S₀) (hS : 0 < S.re) :
    ‖(S - S₀) / (S + S₀)‖ < 1 := by
  have hne : S + S₀ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hne)]
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.sub_im,
    Complex.add_im, Complex.ofReal_im, sub_zero, add_zero]
  nlinarith

/-- The inverse Möbius map: every point of the unit disc is attained from the right
half-plane. -/
theorem mobius_onto (w : ℂ) {S₀ : ℝ} (h0 : 0 < S₀) (hw : ‖w‖ < 1) :
    0 < (S₀ * (1 + w) / (1 - w)).re ∧ (S₀ * (1 + w) / (1 - w) - S₀) / (S₀ * (1 + w) / (1 - w) + S₀) = w := by
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw; exact lt_irrefl _ hw
  constructor
  · rw [Complex.div_re]
    have hn : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr hne
    have hw2 : w.re ^ 2 + w.im ^ 2 < 1 := by
      have := Complex.sq_norm w
      rw [Complex.normSq_apply] at this
      nlinarith [norm_nonneg w]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, zero_mul, sub_zero, zero_add]
    rw [← add_div]
    apply div_pos _ hn
    nlinarith
  · have h2 : (S₀ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    field_simp
    ring

/-- `sinh` maps the half-strip `Re ξ > 0`, `|Im ξ| < π/2` into the right half-plane. -/
theorem sinh_halfstrip (ξ : ℂ) (h1 : 0 < ξ.re) (h2 : |ξ.im| < π / 2) :
    0 < (Complex.sinh ξ).re := by
  have hξ : ξ = (ξ.re : ℂ) + (ξ.im : ℂ) * Complex.I := (Complex.re_add_im ξ).symm
  have hre : (Complex.sinh ξ).re = Real.sinh ξ.re * Real.cos ξ.im := by
    rw [hξ, Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I]
    simp [Complex.mul_re, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  rw [hre]
  apply mul_pos (Real.sinh_pos_iff.mpr h1)
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> [linarith [neg_abs_le ξ.im]; linarith [le_abs_self ξ.im]]

/-- Corollary `ly:cor:strip` on the real axis: for `S > S₀ > 0`, the value
`ω = (S - S₀)/(S + S₀)` lies in `(0,1)` and `1 - ω = 2 S₀/(S + S₀)`. -/
theorem strip_real {S S₀ : ℝ} (h0 : 0 < S₀) (h : S₀ < S) :
    0 < (S - S₀) / (S + S₀) ∧ (S - S₀) / (S + S₀) < 1 ∧
      1 - (S - S₀) / (S + S₀) = 2 * S₀ / (S + S₀) := by
  have hp : 0 < S + S₀ := by linarith
  refine ⟨div_pos (by linarith) hp, (div_lt_one hp).mpr (by linarith), ?_⟩
  field_simp
  ring

/-! ## Strong coupling: Lemma `ly:lem:KP`, Proposition `ly:prop:betadisc`,
Corollary `ly:cor:disc` -/

/-- Lemma `ly:lem:KP`: with `e^{1+d} = 1/(25 e ε)`, the ratio `x = 20 e ε e^{1+d}` is `4/5`. -/
theorem kp_x (ε : ℝ) (hε : 0 < ε) :
    20 * Real.exp 1 * ε * (1 / (25 * Real.exp 1 * ε)) = 4 / 5 := by
  have : 0 < Real.exp 1 := Real.exp_pos 1
  field_simp
  norm_num

/-- Lemma `ly:lem:KP`: the Kotecký–Preiss constant
`24 (4/5)^5/(1 - 4/5)/(20e) < 0.7233 < 1`. -/
theorem kp_constant : 24 * ((4 / 5 : ℝ) ^ 5 / (1 - 4 / 5)) / (20 * Real.exp 1) < 0.7233 := by
  have h := Real.exp_one_gt_d9
  rw [div_lt_iff₀ (by positivity)]
  norm_num
  linarith

/-- `κ = 1/(25 e²)` lies in `(0.0054134, 0.0054135)`. -/
theorem kappa_bounds : 0.0054134 < 1 / (25 * Real.exp 1 ^ 2) ∧
    1 / (25 * Real.exp 1 ^ 2) < 0.0054135 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have hp : 0 < Real.exp 1 := Real.exp_pos 1
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- The series `c₀(r) = ∑_m (r/2)^{2m}/(m!(m+1)!) = 2 I₁(r)/r`. -/
noncomputable def c0 (r : ℝ) : ℝ :=
  ∑' m : ℕ, (r / 2) ^ (2 * m) / ((m.factorial : ℝ) * (m + 1).factorial)

theorem c0_term_le (r : ℝ) (m : ℕ) :
    (r / 2) ^ (2 * m) / ((m.factorial : ℝ) * (m + 1).factorial) ≤ (r ^ 2 / 4) ^ m := by
  have h : (r / 2) ^ (2 * m) = (r ^ 2 / 4) ^ m := by rw [pow_mul]; ring
  rw [h]
  apply div_le_self (by positivity)
  have h1 : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have h2 : (1 : ℝ) ≤ (m + 1).factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  nlinarith

theorem c0_summable (r : ℝ) (hr : r ^ 2 / 4 < 1) :
    Summable (fun m : ℕ => (r / 2) ^ (2 * m) / ((m.factorial : ℝ) * (m + 1).factorial)) :=
  Summable.of_nonneg_of_le (fun m => by rw [pow_mul]; positivity) (c0_term_le r)
    (summable_geometric_of_lt_one (by positivity) hr)

/-- `c₀(r) ≤ 1/(1 - r²/4)`. -/
theorem c0_le (r : ℝ) (hr : r ^ 2 / 4 < 1) : c0 r ≤ 1 / (1 - r ^ 2 / 4) := by
  rw [one_div]
  exact hasSum_le (c0_term_le r) (c0_summable r hr).hasSum
    (hasSum_geometric_of_lt_one (by positivity) hr)

/-- `c₀(r) ≥ 1 + r²/8`. -/
theorem c0_ge (r : ℝ) (hr : r ^ 2 / 4 < 1) : 1 + r ^ 2 / 8 ≤ c0 r := by
  have := (c0_summable r hr).sum_le_tsum (Finset.range 2)
    (fun m _ => by rw [pow_mul]; positivity)
  have e : ∑ m ∈ Finset.range 2, (r / 2) ^ (2 * m) / ((m.factorial : ℝ) * (m + 1).factorial) =
      1 + r ^ 2 / 8 := by
    simp [Finset.sum_range_succ, Nat.factorial]; ring
  rw [e] at this
  exact this

/-- Proposition `ly:prop:betadisc`, item (C1): `ε(0.00539) ≤ κ`, where
`ε(r) = (e^r + c₀(r) - 2)/(2 - c₀(r))` and `κ = 1/(25e²)`. -/
theorem eps_rKP :
    (Real.exp 0.00539 + c0 0.00539 - 2) / (2 - c0 0.00539) ≤ 1 / (25 * Real.exp 1 ^ 2) ∧
      0 < 2 - c0 0.00539 := by
  have hr : (0.00539 : ℝ) ^ 2 / 4 < 1 := by norm_num
  have hc := c0_le 0.00539 hr
  have hc' := c0_ge 0.00539 hr
  have he := Real.exp_bound' (x := 0.00539) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at he
  have hk := kappa_bounds.1
  have hd : 0 < 2 - c0 0.00539 := by
    have : 1 / (1 - (0.00539 : ℝ) ^ 2 / 4) < 2 := by norm_num
    linarith
  refine ⟨?_, hd⟩
  rw [div_le_iff₀ hd]
  have : (1 : ℝ) / (1 - 0.00539 ^ 2 / 4) ≤ 1.0000073 := by norm_num
  nlinarith

/-- The `ℤ₂` disc of Corollary `ly:cor:z2pinch`, item (C1): `r/(1 - r²/2) ≤ κ` at `r = 0.0054`. -/
theorem z2_disc : (0.0054 : ℝ) / (1 - 0.0054 ^ 2 / 2) ≤ 1 / (25 * Real.exp 1 ^ 2) := by
  have hk := kappa_bounds.1
  have : (0.0054 : ℝ) / (1 - 0.0054 ^ 2 / 2) ≤ 0.0054134 := by norm_num
  linarith

/-- Proposition `ly:prop:thetadisc`, item (C2): `c₀(β)(1+κ) > e^β` for `0 ≤ β ≤ 0.0054`,
so `R(β) > 1` there. -/
theorem vortex_radius (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 0.0054) :
    Real.exp β < c0 β * (1 + 1 / (25 * Real.exp 1 ^ 2)) := by
  have hr : β ^ 2 / 4 < 1 := by nlinarith
  have hc' := c0_ge β hr
  have he := Real.exp_bound' (x := β) h0 (by linarith) (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at he
  have hk := kappa_bounds.1
  have hβ3 : β ^ 3 ≤ 0.0054 * β ^ 2 := by nlinarith
  have hβ2 : β ^ 2 ≤ 0.0054 * β := by nlinarith
  nlinarith

/-- Corollary `ly:cor:disc`, item (C4): `12288 · 0.00539 · T⁵ · 2^{-4T} ≤ 1/4097` for all
`T ≥ 9`. -/
theorem disc_consistency (T : ℕ) (hT : 9 ≤ T) :
    12288 * 0.00539 * (T : ℝ) ^ 5 / 2 ^ (4 * T) ≤ 1 / 4097 := by
  have key : ∀ T : ℕ, 9 ≤ T → 12288 * 539 * T ^ 5 * 4097 ≤ 100000 * 16 ^ T := by
    intro T hT
    induction T, hT using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have h1 : (k + 1) ^ 5 ≤ 16 * k ^ 5 := by
        have h2 : 2 * (k + 1) ≤ 3 * k := by omega
        have h3 : (2 * (k + 1)) ^ 5 ≤ (3 * k) ^ 5 := Nat.pow_le_pow_left h2 5
        rw [mul_pow, mul_pow] at h3
        omega
      rw [pow_succ 16]
      nlinarith
  have h := key T hT
  have h' : (12288 * 539 * (T : ℝ) ^ 5 * 4097) ≤ 100000 * 16 ^ T := by exact_mod_cast h
  have h16 : (2 : ℝ) ^ (4 * T) = 16 ^ T := by rw [pow_mul]; norm_num
  rw [h16, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-! ## Criticality: Proposition `ly:prop:critical` -/

/-- The one-loop threshold: `δ_* = π c₁/2 = 11/(6π)` for `c₁ = 11/(3π²)`, and
`0.58356 < δ_* < 0.58357`. -/
theorem critical_width :
    π * (11 / (3 * π ^ 2)) / 2 = 11 / (6 * π) ∧ 0.58356 < 11 / (6 * π) ∧
      11 / (6 * π) < 0.58357 := by
  have hp := Real.pi_pos
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  refine ⟨by field_simp; ring, ?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- Item (C7): `4 sinh(π/2) e^{-π/2} = 2(1 - e^{-π})`. -/
theorem sinh_identity : 4 * Real.sinh (π / 2) * Real.exp (-(π / 2)) = 2 * (1 - Real.exp (-π)) := by
  rw [Real.sinh_eq]
  have : Real.exp (π / 2) * Real.exp (-(π / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : Real.exp (-(π / 2)) * Real.exp (-(π / 2)) = Real.exp (-π) := by
    rw [← Real.exp_add]; ring_nf
  linear_combination 2 * this - 2 * h2

/-! ## Necessity: Proposition `ly:prop:N` -/

/-- Proposition `ly:prop:N` (i): `Re K ≥ K_N = ½ log(50 e²)` exactly when
`|e^{-2K}| ≤ 1/(50e²)`, and then `e^d ≥ 2` in Lemma `ly:lem:KP`. -/
theorem KN_threshold (K : ℂ) :
    (1 / 2 * Real.log (50 * Real.exp 1 ^ 2) ≤ K.re ↔
      ‖Complex.exp (-2 * K)‖ ≤ 1 / (50 * Real.exp 1 ^ 2)) := by
  have hp : 0 < 50 * Real.exp 1 ^ 2 := by positivity
  rw [Complex.norm_exp]
  have : (-2 * K).re = -2 * K.re := by simp
  have e : 1 / (50 * Real.exp 1 ^ 2) = Real.exp (-Real.log (50 * Real.exp 1 ^ 2)) := by
    rw [Real.exp_neg, Real.exp_log hp, one_div]
  rw [this, e, Real.exp_le_exp]
  constructor <;> intro h <;> linarith

theorem KN_ed (ε : ℝ) (hε : 0 < ε) (h : ε ≤ 1 / (50 * Real.exp 1 ^ 2)) :
    2 * Real.exp 1 ≤ 1 / (25 * Real.exp 1 * ε) := by
  have hp : 0 < Real.exp 1 := Real.exp_pos 1
  rw [le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith

/-- Item (C5): the numbers `η = 2|P| 2^{-A}` for `Λ₁(3)` and `Λ₂(3)` are below `π/2`, and
`η(Λ₁(T)) = 96 T⁴ 2^{-2T²}` decreases in `T ≥ 3`. -/
theorem eta_values : (2 * 3888 : ℝ) / 2 ^ 18 < π / 2 ∧ (2 * 7776 : ℝ) / 2 ^ 36 < π / 2 ∧
    48 * 3 ^ 4 = 3888 ∧ 96 * 3 ^ 4 = 7776 := by
  have h := Real.pi_gt_three
  refine ⟨by norm_num; linarith, by norm_num; linarith, by norm_num, by norm_num⟩

theorem eta_decreasing (T : ℕ) (hT : 3 ≤ T) :
    96 * (T + 1) ^ 4 * 2 ^ (2 * T ^ 2) ≤ 96 * T ^ 4 * 2 ^ (2 * (T + 1) ^ 2) := by
  have h1 : (T + 1) ^ 4 ≤ 2 ^ 14 * T ^ 4 := by
    have h2 : T + 1 ≤ 2 * T := by omega
    have h3 : (T + 1) ^ 4 ≤ (2 * T) ^ 4 := Nat.pow_le_pow_left h2 4
    rw [mul_pow] at h3
    omega
  have h4 : 2 ^ (2 * (T + 1) ^ 2) = 2 ^ (2 * T ^ 2) * 2 ^ (4 * T + 2) := by
    rw [← pow_add]; congr 1; ring
  have h5 : 2 ^ 14 ≤ 2 ^ (4 * T + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [h4]
  calc 96 * (T + 1) ^ 4 * 2 ^ (2 * T ^ 2) ≤ 96 * (2 ^ 14 * T ^ 4) * 2 ^ (2 * T ^ 2) := by
        gcongr
    _ ≤ 96 * (2 ^ (4 * T + 2) * T ^ 4) * 2 ^ (2 * T ^ 2) := by gcongr
    _ = 96 * T ^ 4 * (2 ^ (2 * T ^ 2) * 2 ^ (4 * T + 2)) := by ring

/-- In Proposition `ly:prop:N`: if `|z| < π/2` then `Re e^z > 0`. -/
theorem re_exp_pos (z : ℂ) (hz : ‖z‖ < π / 2) : 0 < (Complex.exp z).re := by
  rw [Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have := Complex.abs_im_le_norm z
  constructor <;> [linarith [neg_abs_le z.im]; linarith [le_abs_self z.im]]

/-- In Proposition `ly:prop:N`: a nonempty finite sum of complex numbers with positive real
parts is nonzero. -/
theorem sum_ne_zero_of_re_pos {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (w : ι → ℂ)
    (hw : ∀ i ∈ s, 0 < (w i).re) : ∑ i ∈ s, w i ≠ 0 := by
  intro h
  have h1 : (∑ i ∈ s, w i).re = ∑ i ∈ s, (w i).re := Complex.re_sum s w
  rw [h, Complex.zero_re] at h1
  have h2 : 0 < ∑ i ∈ s, (w i).re := Finset.sum_pos hw hs
  linarith

/-- Item (C5): `log(2/1.001) > 0.6921`, the size of `ψ_T` for `ℤ₂` in Proposition `ly:prop:N`
(ii), as `exp 0.6921 < 2/1.001`. -/
theorem z2_datum_gap : Real.exp 0.6921 < 2 / 1.001 := by
  have := Real.exp_bound' (x := 0.6921) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at this
  norm_num at this ⊢
  linarith

/-! ### The bounds with the zeros anywhere, evenness and the projected datum -/

section Cover


/-- Lemma `ly:lem:coef`, the summation step: if all Taylor coefficients are bounded by `C`
and those of order `< m` vanish, the series is at most `C |v|^m / (1 - |v|)` on the disc. -/
theorem coef_tail (c : ℕ → ℂ) (C : ℝ) (m : ℕ) (v : ℂ) (hv : ‖v‖ < 1)
    (hc : ∀ k, ‖c k‖ ≤ C) (hz : ∀ k < m, c k = 0) :
    ‖∑' k, c k * v ^ k‖ ≤ C * ‖v‖ ^ m / (1 - ‖v‖) := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hc 0)
  have hr0 : 0 ≤ ‖v‖ := norm_nonneg v
  have hgeo : Summable (fun k : ℕ => C * ‖v‖ ^ k) :=
    (summable_geometric_of_lt_one hr0 hv).mul_left C
  have hb : ∀ k, ‖c k * v ^ k‖ ≤ C * ‖v‖ ^ k := by
    intro k; rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hc k) (pow_nonneg hr0 k)
  have hs : Summable (fun k => c k * v ^ k) :=
    Summable.of_norm_bounded hgeo hb
  have hsplit := hs.sum_add_tsum_nat_add m
  have hzero : ∑ i ∈ range m, c i * v ^ i = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hz i (Finset.mem_range.mp hi), zero_mul])
  rw [hzero, zero_add] at hsplit
  rw [← hsplit]
  have hs2 : Summable (fun k : ℕ => C * ‖v‖ ^ m * ‖v‖ ^ k) :=
    (summable_geometric_of_lt_one hr0 hv).mul_left (C * ‖v‖ ^ m)
  calc ‖∑' i, c (i + m) * v ^ (i + m)‖
      ≤ ∑' i, C * ‖v‖ ^ m * ‖v‖ ^ i := by
        refine tsum_of_norm_bounded hs2.hasSum (fun i => ?_)
        calc ‖c (i + m) * v ^ (i + m)‖ ≤ C * ‖v‖ ^ (i + m) := hb _
          _ = C * ‖v‖ ^ m * ‖v‖ ^ i := by ring
    _ = C * ‖v‖ ^ m / (1 - ‖v‖) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hv]; ring

/-- The integer constants of Theorems `ly:thm:cover`, `ly:thm:fluxcover` and
Proposition `ly:prop:zstarHZ` (item (C8)). -/
theorem cover_constants :
    2 * (2 * 96 + 192) = 768 ∧ 4 * 768 = 3072 ∧ 12288 / 4 = 3072 ∧ 2 * (96 + 96) = 384 ∧
    2 * 48 = 96 ∧ 2 * 96 = 192 := by norm_num

/-- `x ↦ x^n/(1-x)` is increasing on `[0,1)`. -/
theorem pow_div_one_sub_mono (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    x ^ n / (1 - x) ≤ y ^ n / (1 - y) := by
  have h1 : 0 < 1 - y := by linarith
  have h2 : 0 < 1 - x := by linarith
  rw [div_le_div_iff₀ h2 h1]
  have := pow_le_pow_left₀ hx hxy n
  have hyn : 0 ≤ y ^ n := pow_nonneg (le_trans hx hxy) n
  nlinarith

/-- Proposition `ly:prop:zstarHZ`: the left side of (HZ) at a smaller modulus is at most
a quarter of the quantity of `Z*`. -/
theorem zstar_implies_HZ (s : ℝ) (hs : 0 ≤ s) (T : ℕ) (hT : 1 ≤ T) {w wD : ℝ}
    (hw : 0 ≤ w) (hle : w ≤ wD) (hD : wD ≤ 1 - 1 / (4 * T)) :
    768 * s * (T:ℝ) ^ 4 * (w ^ (4 * T) / (1 - w)) ≤ 3072 * s * (T:ℝ) ^ 5 * wD ^ (4 * T) := by
  have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
  have h4T : 0 < 4 * (T:ℝ) := by linarith
  have hwD1 : wD < 1 := by
    have : 0 < 1 / (4 * (T:ℝ)) := by positivity
    linarith
  have hmono := pow_div_one_sub_mono (4 * T) hw hle hwD1
  have hden : 1 / (4 * (T:ℝ)) ≤ 1 - wD := by linarith
  have hpos : 0 < 1 - wD := by linarith
  have hinv : 1 / (1 - wD) ≤ 4 * T := by
    rw [div_le_iff₀ hpos]
    have := mul_le_mul_of_nonneg_left hden (le_of_lt h4T)
    rw [mul_one_div_cancel (ne_of_gt h4T)] at this
    linarith
  have hwDn : 0 ≤ wD ^ (4 * T) := pow_nonneg (le_trans hw hle) _
  calc 768 * s * (T:ℝ) ^ 4 * (w ^ (4 * T) / (1 - w))
      ≤ 768 * s * (T:ℝ) ^ 4 * (wD ^ (4 * T) / (1 - wD)) := by
        apply mul_le_mul_of_nonneg_left hmono; positivity
    _ = 768 * s * (T:ℝ) ^ 4 * wD ^ (4 * T) * (1 / (1 - wD)) := by ring
    _ ≤ 768 * s * (T:ℝ) ^ 4 * wD ^ (4 * T) * (4 * T) := by
        apply mul_le_mul_of_nonneg_left hinv; positivity
    _ = 3072 * s * (T:ℝ) ^ 5 * wD ^ (4 * T) := by ring

/-- Lemma `ly:lem:models`(c): the Möbius map `β ↦ β/(β+2s)` sends the half-plane
`Re β > -s` into the unit disc. -/
theorem halfplane_model (s : ℝ) (hs : 0 < s) (β : ℂ) (hβ : -s < β.re) :
    ‖β / (β + 2 * s)‖ < 1 := by
  have hne : β + 2 * s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hne)]
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp
  nlinarith

/-- Lemma `ly:lem:models`(b): `1 - tanh(x/2) = 2/(e^x+1) < 2 e^{-x}` for real `x`. -/
theorem strip_model (x : ℝ) :
    1 - (Real.exp x - 1) / (Real.exp x + 1) = 2 / (Real.exp x + 1) ∧
    2 / (Real.exp x + 1) < 2 * Real.exp (-x) := by
  have he : 0 < Real.exp x := Real.exp_pos x
  constructor
  · field_simp; ring
  · rw [Real.exp_neg, div_lt_iff₀ (by linarith)]
    field_simp
    nlinarith

/-- Theorem `ly:thm:even`: the staggered centre gauge transformation `η_{(x,μ)} = z₀^{Σ_{ρ<μ} x_ρ}`
multiplies every plaquette `(x;μ,ν)`, `μ < ν`, by `z₀`: the four exponents add up to `1` mod `2`. -/
def stagger {d : ℕ} (x : Fin d → ZMod 2) (μ : Fin d) : ZMod 2 :=
  ∑ ρ ∈ univ.filter (· < μ), x ρ

theorem stagger_plaquette_odd {d : ℕ} (x : Fin d → ZMod 2) {μ ν : Fin d} (h : μ < ν) :
    stagger x μ + stagger (x + Pi.single μ 1) ν + stagger (x + Pi.single ν 1) μ
      + stagger x ν = 1 := by
  unfold stagger
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
  have h1 : μ ∈ univ.filter (· < ν) := by simp [h]
  have h2 : ν ∉ univ.filter (· < μ) := by simp [not_lt.mpr (le_of_lt h)]
  rw [if_pos h1, if_neg h2]
  have two : (2 : ZMod 2) = 0 := rfl
  linear_combination (∑ ρ ∈ univ.filter (· < μ), x ρ + ∑ ρ ∈ univ.filter (· < ν), x ρ) * two

/-- Lemma `ly:lem:onesided` and Remark `ly:rem:intensive`: `2Mx/(1+x) < 1/4097` exactly when
`x < 1/(8194 M - 1)`. -/
theorem onesided_threshold (M x : ℝ) (hM : 1 / 8194 < M) (hx : 0 ≤ x) :
    2 * M * x / (1 + x) < 1 / 4097 ↔ x < 1 / (8194 * M - 1) := by
  have h1 : 0 < 8194 * M - 1 := by
    have := mul_lt_mul_of_pos_left hM (by norm_num : (0:ℝ) < 8194); norm_num at this; linarith
  rw [div_lt_div_iff₀ (by linarith) (by norm_num), lt_div_iff₀ h1]
  constructor <;> intro h <;> nlinarith

/-- Theorem `ly:thm:plus`: the arithmetic of the split. With `η = 1/14341`, the flux correction
`(7η/8)/(1-7η/8) = 7/114721 < 1/16388`, and `1/8194 + 2/16388 = 1/4097`. -/
theorem plus_arith :
    (7 * (1 / 14341 : ℚ) / 8) / (1 - 7 * (1 / 14341) / 8) = 7 / 114721 ∧
    (7 : ℚ) / 114721 < 1 / 16388 ∧ (1 : ℚ) / 8194 + 2 / 16388 = 1 / 4097 := by
  norm_num

/-- Proposition `ly:prop:critflux`: the flux half has critical half-width
`π c₁/4 = 11/(12π) = δ*/2`. -/
theorem critflux_width :
    Real.pi * (11 / (3 * Real.pi ^ 2)) / 4 = 11 / (12 * Real.pi) ∧
    11 / (12 * Real.pi) = (11 / (6 * Real.pi)) / 2 := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor <;> field_simp <;> ring

/-- Remark `ly:rem:antistokes`: the dilute torelon model `1 + e^{-u}` vanishes exactly when
`u = iπ(2j+1)`; in particular at `u = iπ`. -/
theorem torelon_toy_zero : 1 + Complex.exp (-(Complex.I * Real.pi)) = 0 := by
  rw [show -(Complex.I * Real.pi) = -(Real.pi * Complex.I) by ring, Complex.exp_neg,
    Complex.exp_pi_mul_I]
  norm_num


end Cover

end YangMills.QuasiLeeYang
