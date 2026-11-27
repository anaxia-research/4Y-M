/-
  A larger zero-free disc (Lemma ly:lem:peel and Proposition ly:prop:largedisc of the next
  version): the rational arithmetic of the proof.

  * the maxima `M_H = max (x, y/x, x/v, x/y) = 13/10` and `M_I = max (v, 1, y/v) = 11/10`
    for the potentials `x = 9/10`, `y = 117/100`, `v = 11/10`;
  * with the upper bounds `c_H = 36383/500000`, `c_I = 19653/10^7` on `e^(a+d) ||f_h||_6` and
    `e^(a+d) ||f_i||_6` at `|beta_W| <= 0.09` (computed in ball arithmetic by the script
    `larger_disc.py`), the three step inequalities of Lemma ly:lem:peel(ii): odd links,
    single links, even links;
  * the root sum `R < 0.0429 < a/4` with `a = 1/5`, hence the Kotecky-Preiss criterion
    `4 R < a`;
  * for even sets with all activities `w = 0.1459` the step inequalities hold with
    `x = 28/25`, `y = 157/125` (the growth bound quoted after the proposition);
  * the sixth moment of the spin-1/2 character is the Catalan number `C_3 = 5`.
-/
import Mathlib

namespace YangMills.LargerDisc

open Finset

/-- Potentials and cost bounds of the proof. -/
def x : ℚ := 9 / 10
def y : ℚ := 117 / 100
def v : ℚ := 11 / 10
def cH : ℚ := 36383 / 500000
def cI : ℚ := 19653 / 10000000
def MH : ℚ := 13 / 10
def MI : ℚ := 11 / 10

theorem MH_eq : max (max (max x (y / x)) (x / v)) (x / y) = MH := by
  norm_num [x, y, v, MH]

theorem MI_eq : max (max v 1) (y / v) = MI := by
  norm_num [y, v, MI]

def wH : ℚ := cH * MH ^ 3
def wI : ℚ := cI * MI ^ 3

/-- The step sum `S_N(P)` of Lemma ly:lem:peel(ii). -/
def S (N : ℕ) (P : ℕ → ℕ → Bool) : ℚ :=
  ∑ h ∈ range (N + 1), ∑ i ∈ range (N + 1 - h),
    if P h i then (N.choose h : ℚ) * ((N - h).choose i : ℚ) * wH ^ h * wI ^ i else 0

/-- Odd links: an odd number of new plaquettes of `H`, at most five candidates. -/
theorem step_odd : S 5 (fun h _ => h % 2 == 1) ≤ x := by
  simp only [S, sum_range_succ, sum_range_zero, wH, wI, cH, cI, MH, MI, x]
  norm_num [Nat.choose]

/-- Single links: an even number of new plaquettes of `H`, at least one new plaquette. -/
theorem step_single : S 5 (fun h i => h % 2 == 0 && 1 ≤ h + i) ≤ v := by
  simp only [S, sum_range_succ, sum_range_zero, wH, wI, cH, cI, MH, MI, v]
  norm_num [Nat.choose]

/-- Even links: an even number of new plaquettes of `H`, at most four candidates. -/
theorem step_even : S 4 (fun h _ => h % 2 == 0) ≤ y := by
  simp only [S, sum_range_succ, sum_range_zero, wH, wI, cH, cI, MH, MI, y]
  norm_num [Nat.choose]

/-- The root sum `R` of Lemma ly:lem:peel(ii). -/
def R : ℚ :=
  ∑ h ∈ range 7, ∑ i ∈ range (7 - h),
    if h % 2 == 0 && 2 ≤ h + i then
      ((6 : ℕ).choose h : ℚ) * ((6 - h).choose i : ℚ) * (cH * x ^ 3) ^ h * (cI * v ^ 3) ^ i
    else 0

theorem root_bound : R < 429 / 10000 := by
  simp only [R, sum_range_succ, sum_range_zero, cH, cI, x, v]
  norm_num [Nat.choose]

/-- The Kotecky-Preiss criterion `4 |gamma| R <= a |gamma|` with `a = 1/5`. -/
theorem kp_criterion : 4 * R < 1 / 5 := by
  have := root_bound
  linarith

/-- Even sets with all activities `w = 0.1459`: the odd-link and even-link inequalities. -/
theorem even_sets_growth :
    let w : ℚ := 1459 / 10000
    let x0 : ℚ := 28 / 25
    let y0 : ℚ := 157 / 125
    let q : ℚ := w * (y0 / x0) ^ 3
    max (max x0 (y0 / x0)) (x0 / y0) = y0 / x0 ∧
      5 * q + 10 * q ^ 3 + q ^ 5 ≤ x0 ∧ 1 + 6 * q ^ 2 + q ^ 4 ≤ y0 := by
  norm_num

/-- The sixth moment of the spin-1/2 character: the number of invariants in the sixth tensor
power of the defining representation is the Catalan number `C_3 = 5`. -/
theorem sixth_moment_half : catalan 3 = 5 :=
  catalan_three

end YangMills.LargerDisc
