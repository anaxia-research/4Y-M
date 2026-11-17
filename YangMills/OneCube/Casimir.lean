import Mathlib

/-!
# L18: the adjoint Casimir of su(2) in the normalisation of the OpenAI construction

The Lie algebra su(2) is identified with the imaginary quaternions; the 2×2 matrix of a
quaternion `q` has real trace `2 Re q`, so the inner product `⟨X,Y⟩ = -(1/2) Re Tr XY` of the
construction is `-Re (X Y)`, and the three quaternion units are orthonormal for it. The adjoint
Casimir `C_A = -(1/dim) Σ_a tr(ad e_a ∘ ad e_a)` equals `8 = 2·2²`, so the slope
`11 C_A / (24 π²)` is `11·2²/(12 π²)`, the one-loop asymptotic-freedom value for SU(2).
The value `C_A = 2 N²` for N = 2, …, 5 is also checked in exact arithmetic by J15.
-/

namespace YangMills.OneCube.Casimir

/-- Hamilton product of integer quaternions, coordinates (1, i, j, k). -/
def mulQ (a b : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![a 0 * b 0 - a 1 * b 1 - a 2 * b 2 - a 3 * b 3,
    a 0 * b 1 + a 1 * b 0 + a 2 * b 3 - a 3 * b 2,
    a 0 * b 2 - a 1 * b 3 + a 2 * b 0 + a 3 * b 1,
    a 0 * b 3 + a 1 * b 2 - a 2 * b 1 + a 3 * b 0]

/-- The quaternion units i, j, k. -/
def unit (a : Fin 3) : Fin 4 → ℤ := fun c => if c = a.succ then 1 else 0

/-- The commutator `[e_a, e_b]`. -/
def comm (a b : Fin 3) : Fin 4 → ℤ := fun c => mulQ (unit a) (unit b) c - mulQ (unit b) (unit a) c

/-- The matrix of `ad e_a` in the basis `e_1, e_2, e_3`. -/
def adMat (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℤ := fun c b => comm a b c.succ

/-- The units are orthonormal for `⟨X,Y⟩ = -Re (X Y)`. -/
theorem units_orthonormal :
    ∀ a b : Fin 3, -(mulQ (unit a) (unit b) 0) = if a = b then 1 else 0 := by decide

/-- Commutators of units are imaginary, so `ad e_a` maps su(2) to itself. -/
theorem comm_imaginary : ∀ a b : Fin 3, comm a b 0 = 0 := by decide

/-- `Σ_a tr(ad e_a ∘ ad e_a) = -24`. -/
theorem sum_trace_ad_sq : (∑ a : Fin 3, (adMat a * adMat a).trace) = -24 := by decide

/-- `C_A = 8 = 2·2²`. -/
theorem casimir_su2 : (-(∑ a : Fin 3, (adMat a * adMat a).trace) : ℚ) / 3 = 2 * 2 ^ 2 := by
  rw [sum_trace_ad_sq]; norm_num

/-- The slope `11 C_A / (24 π²)` with `C_A = 8` is `11·2²/(12 π²)`. -/
theorem slope_su2 : (11 : ℝ) * 8 / (24 * Real.pi ^ 2) = 11 * 2 ^ 2 / (12 * Real.pi ^ 2) := by
  have : Real.pi ^ 2 ≠ 0 := by positivity
  field_simp; ring

end YangMills.OneCube.Casimir
