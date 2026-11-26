/-
  FractionalInstanton: the finite algebra of Proposition ly:prop:fracinst
  (the twist of an almost commuting quadruple).
  * the inverse Cartan matrices of E6 and E7 (scaled by 3 and 2): the square lengths 4/3 and
    3/2 of the minuscule coweights;
  * the square lengths (N-1)/N for SU(N) and N/2 for Sp(N);
  * the coefficient (1/(8 pi^2)) (2 pi)^2 2 = 1 of the constant-curvature model;
  * the number of twists c in (Z/3)^6 and (Z/2)^6 with Pf(c) = 0 (261 and 36), i.e. the twists
    that the proposition allows for E6 (and SU(3)) and E7 (and SU(2));
  * the consistency checks: q = 1/2 for SU(2) = Sp(1), q = 1 for Sp(2) = Spin(5),
    q = 3/4 for SU(4) = Spin(6), and nondegeneracy of a a' q mod 1 for E6 and E7.
-/
import Mathlib

namespace YangMills.FractionalInstanton

/-- The Cartan matrix of `E6` (Bourbaki numbering 1,...,6 as 0,...,5). -/
def cartanE6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 0, -1, 0, 0, 0; 0, 2, 0, -1, 0, 0; -1, 0, 2, -1, 0, 0;
     0, -1, -1, 2, -1, 0; 0, 0, 0, -1, 2, -1; 0, 0, 0, 0, -1, 2]

/-- Three times the inverse Cartan matrix of `E6`. -/
def invE6x3 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4;
     6, 9, 12, 18, 12, 6; 4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]

theorem e6_inverse : cartanE6 * invE6x3 = 3 • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-- The minuscule coweights of `E6` (nodes 1 and 6) have square length `4/3`: with
`e6_inverse` the diagonal entries of the inverse Cartan matrix there are `4/3`. -/
theorem e6_minuscule : invE6x3 0 0 = 4 ∧ invE6x3 5 5 = 4 := by decide

def cartanE7 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![2, 0, -1, 0, 0, 0, 0; 0, 2, 0, -1, 0, 0, 0; -1, 0, 2, -1, 0, 0, 0;
     0, -1, -1, 2, -1, 0, 0; 0, 0, 0, -1, 2, -1, 0; 0, 0, 0, 0, -1, 2, -1;
     0, 0, 0, 0, 0, -1, 2]

/-- Twice the inverse Cartan matrix of `E7`. -/
def invE7x2 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![4, 4, 6, 8, 6, 4, 2; 4, 7, 8, 12, 9, 6, 3; 6, 8, 12, 16, 12, 8, 4;
     8, 12, 16, 24, 18, 12, 6; 6, 9, 12, 18, 15, 10, 5; 4, 6, 8, 12, 10, 8, 4;
     2, 3, 4, 6, 5, 4, 3]

theorem e7_inverse : cartanE7 * invE7x2 = 2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-- The minuscule coweight of `E7` (node 7) has square length `3/2`. -/
theorem e7_minuscule : invE7x2 6 6 = 3 := by decide

/-- `SU(N)`: `lambda = diag(1/N, ..., 1/N, 1/N - 1)` has square length `(N-1)/N`. -/
theorem su_square_length (N : ℚ) (hN : N ≠ 0) :
    (N - 1) * (1 / N) ^ 2 + (1 / N - 1) ^ 2 = (N - 1) / N := by
  field_simp; ring

/-- `Sp(N)`: `lambda = (1/2) diag(1_N, -1_N)` has square length `N/2`. -/
theorem sp_square_length (N : ℚ) : 2 * N * (1 / 2) ^ 2 = N / 2 := by ring

/-- The constant-curvature model: `(1/(8 pi^2)) (2 pi)^2 * 2 = 1`. -/
theorem model_coefficient (π' : ℝ) (h : π' ≠ 0) : 1 / (8 * π' ^ 2) * (2 * π') ^ 2 * 2 = 1 := by
  field_simp; ring

/-- The Pfaffian of a twist `c = (c12, c13, c14, c23, c24, c34)`. -/
def pf {R : Type*} [CommRing R] (c : Fin 6 → R) : R := c 0 * c 5 - c 1 * c 4 + c 2 * c 3

set_option maxRecDepth 20000 in
/-- The twists allowed for `E6` (and `SU(3)`): `Pf(c) = 0` in `Z/3`. -/
theorem allowed_mod3 : (Finset.univ.filter (fun c : Fin 6 → ZMod 3 => pf c = 0)).card = 261 := by
  decide

/-- The twists allowed for `E7` (and `SU(2)`, `Sp(N)` with `N` odd): `Pf(c) = 0` in `Z/2`. -/
theorem allowed_mod2 : (Finset.univ.filter (fun c : Fin 6 → ZMod 2 => pf c = 0)).card = 36 := by
  decide

/-- Nondegeneracy: `a q` is not an integer for `a = 1, 2` and `q = 4/3`, nor for `a = 1`,
`q = 3/2`; and the coincidences of the low-rank isomorphisms. -/
theorem nondegenerate :
    (¬ ∃ n : ℤ, (4 / 3 : ℚ) = n) ∧ (¬ ∃ n : ℤ, (8 / 3 : ℚ) = n) ∧ (¬ ∃ n : ℤ, (3 / 2 : ℚ) = n) := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro ⟨n, hn⟩
  · have h1 : (3 : ℚ) * n = 4 := by linarith [hn]
    have h2 : (3 : ℤ) * n = 4 := by exact_mod_cast h1
    omega
  · have h1 : (3 : ℚ) * n = 8 := by linarith [hn]
    have h2 : (3 : ℤ) * n = 8 := by exact_mod_cast h1
    omega
  · have h1 : (2 : ℚ) * n = 3 := by linarith [hn]
    have h2 : (2 : ℤ) * n = 3 := by exact_mod_cast h1
    omega

theorem low_rank : ((2 : ℚ) - 1) / 2 = 1 / 2 ∧ (1 : ℚ) / 2 = 1 / 2 ∧ (2 : ℚ) / 2 = 1 ∧
    ((4 : ℚ) - 1) / 4 = 3 / 4 := by norm_num

end YangMills.FractionalInstanton
