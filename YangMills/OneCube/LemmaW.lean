import Mathlib

/-!
# One-cube criteria: the algebra of Lemma W (check L11)

An element of `SU(2)` is a unit quaternion. We write `P = a + i b·σ` with
`(a, b) ∈ ℝ × ℝ³`; under `iσₖ ↦ -eₖ` (the quaternion units `i, j, k`) this is the
quaternion `a - b₁ i - b₂ j - b₃ k`, and `Tr P = 2 Re P`. Inverses of unit
quaternions are conjugates, so `Tr P⁻¹ = Tr P*`.

Checked here, as polynomial identities valid for all real coordinates (the
unit-norm constraint is not needed):
* the trace identities `Tr Pₖ = 2aₖ`, `Tr PᵢPⱼ^{±1} = 2(aᵢaⱼ ∓ gᵢⱼ)`,
  `Tr P₁P₂P₃ = 2(s+d)`, `Tr P₁⁻¹P₂⁻¹P₃⁻¹ = 2(s-d)`;
* the Gram expansion `Φ = A + (4/3)Σ aᵢ²aⱼ² + (4/3)S + s² + d²` and `d² = det G`;
* `Φ = 1` at the three configurations (i), (ii), (iii), and along the curve
  `(cos t + i sin t σ₃, iσ₁, iσ₂)`, which shows that the equality set of
  `Φ ≥ 1` is not a finite set of points.

The inequality `Φ ≥ 1` itself is not formalised here.
-/

set_option linter.unusedSimpArgs false

namespace YangMills.OneCube.LemmaW


/-- The quaternion of `a + i b·σ`. -/
def quat (a : ℝ) (b : Fin 3 → ℝ) : Quaternion ℝ := ⟨a, -b 0, -b 1, -b 2⟩

/-- `Tr` of the `2×2` matrix of a quaternion. -/
def tr (q : Quaternion ℝ) : ℝ := 2 * q.re

variable (a : Fin 3 → ℝ) (b : Fin 3 → Fin 3 → ℝ)

/-- `gᵢⱼ = bᵢ·bⱼ`. -/
def g (i j : Fin 3) : ℝ := b i 0 * b j 0 + b i 1 * b j 1 + b i 2 * b j 2

/-- `d = det(b₁, b₂, b₃)`. -/
def d : ℝ :=
  b 0 0 * (b 1 1 * b 2 2 - b 1 2 * b 2 1) - b 0 1 * (b 1 0 * b 2 2 - b 1 2 * b 2 0) +
    b 0 2 * (b 1 0 * b 2 1 - b 1 1 * b 2 0)

/-- `s = a₁a₂a₃ - a₁g₂₃ - a₂g₁₃ - a₃g₁₂`. -/
def s : ℝ := a 0 * a 1 * a 2 - a 0 * g b 1 2 - a 1 * g b 0 2 - a 2 * g b 0 1

def P (k : Fin 3) : Quaternion ℝ := quat (a k) (b k)

theorem tr_P (k : Fin 3) : tr (P a b k) = 2 * a k := by
  simp [tr, P, quat]

theorem tr_PP (i j : Fin 3) : tr (P a b i * P a b j) = 2 * (a i * a j - g b i j) := by
  simp only [tr, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  simp [P, quat, g]; ring

theorem tr_PPinv (i j : Fin 3) : tr (P a b i * star (P a b j)) = 2 * (a i * a j + g b i j) := by
  simp only [tr, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  simp [P, quat, g]; ring

theorem tr_PPP : tr (P a b 0 * P a b 1 * P a b 2) = 2 * (s a b + d b) := by
  simp only [tr, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  simp [P, quat, s, g, d]; ring

theorem tr_PPPinv :
    tr (star (P a b 0) * star (P a b 1) * star (P a b 2)) = 2 * (s a b - d b) := by
  simp only [tr, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  simp [P, quat, s, g, d]; ring

/-- The weighted sum `Φ` of squared traces of the eleven charged words. -/
noncomputable def Φ : ℝ :=
  (1 / 4) * ∑ k : Fin 3, tr (P a b k) ^ 2 +
  (1 / 6) * ((tr (P a b 0 * P a b 1)) ^ 2 + (tr (P a b 0 * star (P a b 1))) ^ 2 +
             (tr (P a b 0 * P a b 2)) ^ 2 + (tr (P a b 0 * star (P a b 2))) ^ 2 +
             (tr (P a b 1 * P a b 2)) ^ 2 + (tr (P a b 1 * star (P a b 2))) ^ 2) +
  (1 / 8) * ((tr (P a b 0 * P a b 1 * P a b 2)) ^ 2 +
             (tr (star (P a b 0) * star (P a b 1) * star (P a b 2))) ^ 2)

def A : ℝ := a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2
def S : ℝ := g b 0 1 ^ 2 + g b 0 2 ^ 2 + g b 1 2 ^ 2

/-- The Gram expansion of `Φ`. -/
theorem gram_expansion :
    Φ a b = A a + (4 / 3) * (a 0 ^ 2 * a 1 ^ 2 + a 0 ^ 2 * a 2 ^ 2 + a 1 ^ 2 * a 2 ^ 2) +
      (4 / 3) * S b + s a b ^ 2 + d b ^ 2 := by
  simp only [Φ, tr_P, tr_PP, tr_PPinv, tr_PPP, tr_PPPinv, Fin.sum_univ_three, A, S]
  ring

/-- `d² = det G` with `G = (gᵢⱼ)` the Gram matrix of `b₁, b₂, b₃`. -/
theorem d_sq_eq_det_gram :
    d b ^ 2 = g b 0 0 * g b 1 1 * g b 2 2 + 2 * g b 0 1 * g b 0 2 * g b 1 2 -
      g b 0 0 * g b 1 2 ^ 2 - g b 1 1 * g b 0 2 ^ 2 - g b 2 2 * g b 0 1 ^ 2 := by
  simp only [d, g]; ring

/-! ## The equality configurations -/

/-- (i) `(iσ₁, iσ₂, iσ₃)`. -/
theorem phi_config_i : Φ ![0, 0, 0] ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] = 1 := by
  rw [gram_expansion]; simp [A, S, s, g, d]

/-- (ii) `(1, iσ₁, iσ₂)`. -/
theorem phi_config_ii : Φ ![1, 0, 0] ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0]] = 1 := by
  rw [gram_expansion]; simp [A, S, s, g, d]

/-- (iii) coplanar unit vectors at mutual angles `2π/3`. -/
theorem phi_config_iii :
    Φ ![0, 0, 0] ![![1, 0, 0], ![-1 / 2, Real.sqrt 3 / 2, 0], ![-1 / 2, -(Real.sqrt 3 / 2), 0]] = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [gram_expansion]
  simp [A, S, s, g, d]
  nlinarith [h3]

/-- The configurations above are in `SU(2)³`: unit norm. -/
theorem config_iii_unit :
    (-1 / 2 : ℝ) ^ 2 + (Real.sqrt 3 / 2) ^ 2 = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [h3]

/-- `Φ = 1` along the curve `(cos t + i sin t σ₃, iσ₁, iσ₂)`, which joins (ii) to a
permutation of (i): the equality set is a continuum. -/
theorem phi_curve (t : ℝ) :
    Φ ![Real.cos t, 0, 0] ![![0, 0, Real.sin t], ![1, 0, 0], ![0, 1, 0]] = 1 := by
  rw [gram_expansion]
  simp only [A, S, s, g, d]
  simp [Real.sin_sq_add_cos_sq]

end YangMills.OneCube.LemmaW
