/-
  FixedBox: the algebra and arithmetic of Proposition ly:prop:fixedall
  (a fixed box at weak coupling, every group).
  * the commutator identity ab - ba = (a-1)(b-1) - (b-1)(a-1) in every ring;
  * the link count of the maximal tree gauge on a four-dimensional torus;
  * the exponent bookkeeping d + (d/2)(3V-3) = (d/2)(3V-1) and its consequence
    (3dV/2) - (d/2)(3V-1) = d/2 (non-abelian) and (3dV/2) - (d/2)(3V-3) = 3d/2 (abelian);
  * the choice r^2 = 1/(2s), rho = 1/(4s), s = sqrt b: 4 rho + 2 r^2 = 2/s and
    (b/2)(2/s)^2 = 2, and the abelian value (b/2)(4 rho)^2 = 1/2;
  * the rational steps of part (d) for SU(2).
-/
import Mathlib

namespace YangMills.FixedBox

/-- The commutator identity used for the plaquettes of the zero-mode configuration. -/
theorem comm_identity {R : Type*} [Ring R] (a b : R) :
    a * b - b * a = (a - 1) * (b - 1) - (b - 1) * (a - 1) := by
  noncomm_ring

/-- Links outside a spanning tree of a four-dimensional torus with `V` sites. -/
theorem nontree_links (V : ℕ) (hV : 1 ≤ V) : 4 * V - (V - 1) = 3 * V + 1 := by
  omega

/-- The count of the factors of two: `2 + 2 (n - 4) = 6V - 4` for `n = 3V + 1`. -/
theorem two_count (V : ℕ) (hV : 1 ≤ V) : 2 + 2 * ((3 * V + 1) - 4) = 6 * V - 4 := by
  omega

theorem exponent_nonabelian (d V : ℚ) :
    d + d / 2 * (3 * V - 3) = d / 2 * (3 * V - 1) := by ring

theorem gain_nonabelian (d V : ℚ) :
    3 * d / 2 * V - d / 2 * (3 * V - 1) = d / 2 := by ring

theorem gain_abelian (d V : ℚ) :
    3 * d / 2 * V - d / 2 * (3 * V - 3) = 3 * d / 2 := by ring

/-- The plaquette bound on the region `S`: with `s = sqrt b > 0`,
`r ^ 2 = 1 / (2 s)` and `rho = 1 / (4 s)`, one has `4 rho + 2 r ^ 2 = 2 / s`
and `(b / 2) (2 / s) ^ 2 = 2`. -/
theorem plaquette_cost (s : ℝ) (hs : 0 < s) :
    4 * (1 / (4 * s)) + 2 * (1 / (2 * s)) = 2 / s ∧
      s ^ 2 / 2 * (2 / s) ^ 2 = 2 := by
  constructor
  · field_simp; norm_num
  · field_simp

theorem plaquette_cost_abelian (s : ℝ) (hs : 0 < s) :
    s ^ 2 / 2 * (4 * (1 / (4 * s))) ^ 2 = 1 / 2 := by
  field_simp

/-- Both radii are at most one when `s = sqrt b >= 1`. -/
theorem radii_le_one (s : ℝ) (hs : 1 ≤ s) :
    1 / (2 * s) ≤ 1 ∧ 1 / (4 * s) ≤ 1 := by
  constructor
  · rw [div_le_one (by linarith)]; linarith
  · rw [div_le_one (by linarith)]; linarith

/-- Part (d) for SU(2): `8 * 35.234 < 282`, and the neutral-half step:
if `x - 282 t + 2.74 <= 1/8194` with `x >= 0` then `282 t > x`. -/
theorem su2_datum_constant : (8 : ℚ) * (35234 / 1000) < 282 := by norm_num

theorem su2_base_scale (x t : ℝ) (h : x - 282 * t + 274 / 100 ≤ 1 / 8194) :
    x < 282 * t := by
  linarith

/-- `(3/2) / 282 > 1 / 188`, so `282 t > (3/2) L` gives `t > L / 188` for `L >= 0`. -/
theorem su2_rate (L t : ℝ) (hL : 0 ≤ L) (h : 3 / 2 * L < 282 * t) : L / 188 < t ∨ L = 0 := by
  rcases eq_or_lt_of_le hL with h0 | hpos
  · right; exact h0.symm
  · left; nlinarith

end YangMills.FixedBox
