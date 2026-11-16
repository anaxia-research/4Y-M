import Mathlib

/-!
# One-cube criteria: the Model-A Jacobi determinant identity (check L16)

`∏_{j=0}^{n-1} (x - 2 cos(2πj/n)) = 2 (T_n(x/2) - 1)` for every `n ≥ 1` and every
real (or complex) `x`, with `T_n` the Chebyshev polynomial of the first kind.
The paper needs it for `n = 3, …, 9`; it is proved here for all `n ≥ 1`.

Proof: write `x = z + z⁻¹` (`z = e^{iθ}` with `cos θ = x/2`), so that
`2 T_n(x/2) = zⁿ + z⁻ⁿ`; with `ζ = e^{2πi/n}`,
`x - (ζʲ + ζ⁻ʲ) = (z - ζʲ)(z - ζ⁻ʲ)/z`, and `∏ⱼ (z - ζʲ) = ∏ⱼ (z - ζ⁻ʲ) = zⁿ - 1`.
-/

namespace YangMills.OneCube.Chebyshev

open Polynomial Complex Finset

/-- `∏_{j<n} (z - ζʲ) = zⁿ - 1` for a primitive `n`-th root of unity `ζ`. -/
theorem prod_sub_pow {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (z : ℂ) :
    ∏ j ∈ range n, (z - ζ ^ j) = z ^ n - 1 := by
  have h := X_pow_sub_C_eq_prod hζ hn (one_pow n)
  have := congrArg (Polynomial.eval z) h
  simpa [Polynomial.eval_prod] using this.symm

theorem prod_identity_complex (n : ℕ) (hn : 0 < n) (x : ℂ) :
    ∏ j ∈ range n, (x - 2 * Complex.cos (2 * (Real.pi : ℂ) * j / n)) =
      2 * ((Chebyshev.T ℂ n).eval (x / 2) - 1) := by
  obtain ⟨θ, hθ⟩ := Complex.cos_surjective (x / 2)
  set z := Complex.exp (θ * I) with hz
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hzinv : z⁻¹ = Complex.exp (-θ * I) := by
    rw [hz, ← Complex.exp_neg]; ring_nf
  have hx : x = z + z⁻¹ := by
    have : x = 2 * Complex.cos θ := by rw [hθ]; ring
    rw [this, Complex.cos, hzinv, hz]; ring_nf
  -- Chebyshev side
  have hT : 2 * (Chebyshev.T ℂ n).eval (x / 2) = z ^ n + (z ^ n)⁻¹ := by
    have h1 := Polynomial.Chebyshev.T_complex_cos θ n
    rw [hθ] at h1
    push_cast at h1
    have hzn : z ^ n = Complex.exp (n * θ * I) := by rw [hz, ← Complex.exp_nat_mul]; ring_nf
    have hzninv : (z ^ n)⁻¹ = Complex.exp (-(n * θ) * I) := by
      rw [hzn, ← Complex.exp_neg]; ring_nf
    rw [h1, Complex.cos, hzninv, hzn]; ring
  -- roots of unity side
  set ζ := Complex.exp (2 * (Real.pi : ℂ) * I / n) with hζdef
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hζ' : IsPrimitiveRoot ζ⁻¹ n := hζ.inv
  have hcos : ∀ j : ℕ, 2 * Complex.cos (2 * (Real.pi : ℂ) * j / n) = ζ ^ j + (ζ⁻¹) ^ j := by
    intro j
    rw [Complex.cos, hζdef, ← Complex.exp_nat_mul, inv_pow, ← Complex.exp_nat_mul,
      ← Complex.exp_neg]
    ring_nf
  have hfac : ∀ j : ℕ, x - 2 * Complex.cos (2 * (Real.pi : ℂ) * j / n) =
      (z - ζ ^ j) * (z - (ζ⁻¹) ^ j) * z⁻¹ := by
    intro j
    have hw : ζ ^ j * (ζ⁻¹) ^ j = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (hζ.ne_zero hn.ne'), one_pow]
    rw [hcos j, hx]
    field_simp
    linear_combination (-1) * hw
  rw [Finset.prod_congr rfl (fun j _ => hfac j), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_sub_pow hn hζ, prod_sub_pow hn hζ', Finset.prod_const, Finset.card_range]
  have hR : 2 * ((Chebyshev.T ℂ n).eval (x / 2) - 1) = z ^ n + (z ^ n)⁻¹ - 2 := by
    rw [mul_sub, hT]; ring
  rw [hR, inv_pow]
  have hzn : z ^ n ≠ 0 := pow_ne_zero _ hz0
  field_simp
  ring

/-- The identity for real `x`. -/
theorem prod_identity (n : ℕ) (hn : 0 < n) (x : ℝ) :
    ∏ j ∈ range n, (x - 2 * Real.cos (2 * Real.pi * j / n)) =
      2 * ((Chebyshev.T ℝ n).eval (x / 2) - 1) := by
  have h := prod_identity_complex n hn (x : ℂ)
  apply Complex.ofReal_injective
  push_cast
  rw [h]

/-- The cases `n = 3, …, 9` used for Model A. -/
theorem L16 : ∀ n ∈ Finset.Icc 3 9, ∀ x : ℝ,
    ∏ j ∈ range n, (x - 2 * Real.cos (2 * Real.pi * j / n)) =
      2 * ((Chebyshev.T ℝ n).eval (x / 2) - 1) := by
  intro n hn x
  exact prod_identity n (by simp at hn; omega) x

end YangMills.OneCube.Chebyshev
