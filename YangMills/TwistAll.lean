/-
  Twisted boxes for every group (Proposition ly:prop:twistall of the next version):
  the finite algebra of the proof.

  * the cocycle step of part (d): on a joint eigenspace of the commuting operators
    `Ad(h_mu)`, with scalars `a mu = 1 - chi mu`, a cocycle of the Koszul complex is a
    coboundary as soon as one `a mu0` is nonzero, and the coboundary map is injective;
  * the Koszul complex is a complex for commuting operators;
  * part (e): the orbit `lambda * zeta^k` of a primitive root is injective, eigenspace
    dimensions are forced to be one, the clock and shift matrices satisfy `P Q = omega Q P`
    and `P^m Q = omega^m Q P^m`, a nonzero temporal twist for a prime `N` has a unimodular
    row, and conjugation by `x` multiplies products and powers of the `y`'s by the product of
    the central factors;
  * the bookkeeping of the exponents of `b` and of the constant in parts (a), (c), (d).
-/
import Mathlib

namespace YangMills.TwistAll

open Matrix BigOperators

/-! ### The cocycle step (part (d)) -/

/-- On a joint eigenspace, with `a mu = 1 - chi mu`, a Koszul 1-cocycle `Y` (that is
`a nu • Y mu = a mu • Y nu`) is the coboundary of `(a mu0)⁻¹ • Y mu0` if `a mu0 ≠ 0`. -/
theorem cocycle_coboundary {ι K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (a : ι → K) (Y : ι → M) (h : ∀ μ ν, a ν • Y μ = a μ • Y ν) (μ0 : ι) (h0 : a μ0 ≠ 0) :
    ∀ μ, Y μ = a μ • ((a μ0)⁻¹ • Y μ0) := by
  intro μ
  have h1 := h μ μ0
  calc Y μ = (a μ0)⁻¹ • (a μ0 • Y μ) := by rw [smul_smul, inv_mul_cancel₀ h0, one_smul]
    _ = (a μ0)⁻¹ • (a μ • Y μ0) := by rw [h1]
    _ = a μ • ((a μ0)⁻¹ • Y μ0) := by rw [smul_comm]

/-- The coboundary map `Z ↦ (a mu • Z)` is injective if some `a mu0 ≠ 0`. -/
theorem coboundary_injective {ι K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (a : ι → K) (Z : M) (μ0 : ι) (h0 : a μ0 ≠ 0) (hZ : ∀ μ, a μ • Z = 0) : Z = 0 := by
  have := hZ μ0
  rcases smul_eq_zero.mp this with h | h
  · exact absurd h h0
  · exact h

/-- The Koszul complex of commuting operators is a complex:
`(1 - B)((1 - A) Z) - (1 - A)((1 - B) Z) = 0`. -/
theorem koszul_comp_zero {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (A B : Module.End R M) (hAB : Commute A B) (Z : M) :
    (1 - B) ((1 - A) Z) - (1 - A) ((1 - B) Z) = 0 := by
  have hc : Commute (1 - A) (1 - B) :=
    (Commute.one_right (1 - A)).sub_right ((Commute.one_left B).sub_left hAB)
  have h2 := congrArg (fun f : Module.End R M => f Z) hc.eq
  simp only [Module.End.mul_apply] at h2
  rw [h2, sub_self]

/-! ### Part (e): irreducible pairs, clock and shift -/

/-- The `N` numbers `lambda * zeta^k`, `k < N`, are distinct for a primitive `N`-th root
`zeta` and `lambda ≠ 0`. -/
theorem orbit_injective {K : Type*} [Field K] {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    {l : K} (hl : l ≠ 0) : Function.Injective (fun k : Fin N => l * ζ ^ (k : ℕ)) := by
  intro i j hij
  have h : ζ ^ (i : ℕ) = ζ ^ (j : ℕ) := mul_left_cancel₀ hl hij
  exact Fin.ext (hζ.pow_inj i.isLt j.isLt h)

/-- `N` eigenspaces of positive dimension inside a space of dimension `N` all have
dimension one. -/
theorem eigen_dims_one {N : ℕ} (f : Fin N → ℕ) (hpos : ∀ k, 1 ≤ f k)
    (hsum : ∑ k, f k ≤ N) : ∀ k, f k = 1 := by
  intro k
  by_contra hk
  have hk2 : 2 ≤ f k := by have := hpos k; omega
  have hle : ∑ j : Fin N, (1 : ℕ) + 1 ≤ ∑ j, f j := by
    have hsplit : ∑ j, f j = f k + ∑ j ∈ Finset.univ.erase k, f j :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
    have hsplit1 : ∑ j : Fin N, (1 : ℕ) = 1 + ∑ j ∈ Finset.univ.erase k, (1 : ℕ) :=
      (Finset.add_sum_erase _ (fun _ => (1 : ℕ)) (Finset.mem_univ k)).symm
    have hrest : ∑ j ∈ Finset.univ.erase k, (1 : ℕ) ≤ ∑ j ∈ Finset.univ.erase k, f j :=
      Finset.sum_le_sum (fun j _ => hpos j)
    omega
  simp at hle
  omega

/-- The clock matrix `diag(omega^k)`. -/
noncomputable def clock (N : ℕ) [NeZero N] (ω : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal (fun k => ω ^ (k : ℕ))

/-- The cyclic shift `e_j ↦ e_(j+1)`. -/
def shift (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i = j + 1 then 1 else 0

/-- `P Q = omega Q P` for the clock and shift matrices when `omega^N = 1`. -/
theorem clock_shift_comm (N : ℕ) [NeZero N] (ω : ℂ) (hω : ω ^ N = 1) :
    clock N ω * shift N = ω • (shift N * clock N ω) := by
  ext i j
  simp only [clock, shift, diagonal_mul, mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j + 1
  · subst hij
    have hv : ((j + 1 : Fin N) : ℕ) = ((j : ℕ) + 1 % N) % N := by
      rw [Fin.val_add]; simp
    simp only [if_true, mul_one, one_mul]
    rw [hv, ← pow_eq_pow_mod _ hω, pow_add, ← pow_eq_pow_mod 1 hω, pow_one, mul_comm]
  · simp [hij]

/-- `P^m Q = omega^m Q P^m`: conjugation by the shift multiplies `P^m` by `omega^(-m)`,
which gives the temporal twists `h_j = P^(-z_j)`, `h_4 = Q` of part (e). -/
theorem clock_pow_shift (N : ℕ) [NeZero N] (ω : ℂ) (hω : ω ^ N = 1) (m : ℕ) :
    clock N ω ^ m * shift N = ω ^ m • (shift N * clock N ω ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Matrix.mul_assoc, clock_shift_comm N ω hω, Matrix.mul_smul,
      ← Matrix.mul_assoc, ih, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, ← pow_succ,
      pow_succ ω m, mul_comm (ω ^ m) ω]

/-- For a prime `N`, a nonzero temporal twist `z` has a unimodular row:
some combination `sum a_j z_j` equals `1` in `Z_N`. -/
theorem prime_unimodular (p : ℕ) [Fact p.Prime] (z : Fin 3 → ZMod p) (hz : z ≠ 0) :
    ∃ a : Fin 3 → ZMod p, ∑ j, a j * z j = 1 := by
  obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hz (funext h)
  refine ⟨Pi.single j (z j)⁻¹, ?_⟩
  rw [Finset.sum_eq_single j]
  · simp [inv_mul_cancel₀ hj]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Conjugation by `x` is multiplicative on the `y`'s with central factors. -/
theorem conj_mul {G : Type*} [Group G] (x y1 y2 c1 c2 : G) (hc2 : ∀ g, c2 * g = g * c2)
    (h1 : x * y1 * x⁻¹ = c1 * y1) (h2 : x * y2 * x⁻¹ = c2 * y2) :
    x * (y1 * y2) * x⁻¹ = (c1 * c2) * (y1 * y2) := by
  calc x * (y1 * y2) * x⁻¹ = (x * y1 * x⁻¹) * (x * y2 * x⁻¹) := by group
    _ = (c1 * y1) * (c2 * y2) := by rw [h1, h2]
    _ = c1 * (c2 * y1) * y2 := by rw [hc2 y1]; group
    _ = (c1 * c2) * (y1 * y2) := by group

/-- Conjugation by `x` multiplies `y^n` by `c^n` when `x y x⁻¹ = c y` with `c` central. -/
theorem conj_pow {G : Type*} [Group G] (x y c : G) (hc : ∀ g, c * g = g * c)
    (h : x * y * x⁻¹ = c * y) (n : ℕ) : x * y ^ n * x⁻¹ = c ^ n * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact conj_mul x (y ^ n) y (c ^ n) c hc ih h

/-! ### Bookkeeping of the exponents and constants -/

/-- Part (a): the coefficient of `log b` is `d`. -/
theorem exp_upper (d V : ℝ) : -(d / 2) * (3 * V - 3) + d / 2 * (3 * V - 1) = d := by ring

/-- Part (c): the coefficient of `log b` is `-2d`. -/
theorem exp_ball (d V : ℝ) : -(d / 2) * (3 * V + 1) + d / 2 * (3 * V - 3) = -(2 * d) := by ring

/-- Part (d): the tube around the flat set gives `-3d/2`. -/
theorem exp_tube (d V : ℝ) : -(3 * d / 2) - d / 2 * (3 * V - 3) + d / 2 * (3 * V - 3) =
    -(3 * d / 2) := by ring

/-- Part (d): `d - 3d/2 = -d/2`, the exponent of a rigid twist. -/
theorem exp_rigid (d : ℝ) : d - 3 * d / 2 = -(d / 2) := by ring

/-- The codimension of a rigid twisted flat set: `4d - d = 3d`. -/
theorem codim_rigid (d : ℕ) : 4 * d - d = 3 * d := by omega

/-- The constant of part (a): `K''_G V + k''_G`. -/
theorem const_upper (V lC lk l2 d : ℝ) :
    (3 * V - 3) * (lC + d / 2 * l2) + 12 * V - (3 * V + 1) * lk + (6 * V - 4) * d * l2 =
      (12 + 3 * (lC - lk) + 15 / 2 * d * l2) * V + (-3 * lC - lk - 11 / 2 * d * l2) := by ring

/-- The constant of part (c). -/
theorem const_lower (V lC lk l2 d : ℝ) :
    -12 * V + (3 * V + 1) * lk - (3 * V + 1) * (2 * d * l2) - (3 * V - 3) * (lC + d / 2 * l2) =
      -((12 + 3 * (lC - lk) + 15 / 2 * d * l2) * V) + (lk + 3 * lC - d / 2 * l2) := by ring

end YangMills.TwistAll
