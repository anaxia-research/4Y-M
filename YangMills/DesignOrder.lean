import Mathlib

/-!
# Moments of the binary icosahedral group

Arithmetic of Proposition `ly:prop:jordan` of the paper (bounded design order) in the case
of the binary icosahedral group `2I ⊂ SU(2)`. A finite subgroup `H ⊂ U(n)` is a unitary
`k`-group when the average of `|tr h|^(2k)` over `H` equals the Haar integral; for `SU(2)`
that integral is the Catalan number `C_k`. The traces of `2I` on its classes are
`±2, ±φ, ±(φ - 1), ±1, 0` with class sizes `1, 1, 12, 12, 12, 12, 20, 20, 30`, where
`φ = (1 + √5)/2` and `φ - 1 = -(1 - √5)/2`. The representation theory (Haar moments, the
classes of `2I`) is not formalised here; the theorems check the arithmetic.

* `lucas_binet` : the Lucas numbers satisfy `L n = φ^n + ψ^n`, `ψ = (1 - √5)/2`.
* `moment_eq_lucas` : the class sum of `tr^(2k)` over `2I` equals `2·4^k + 24 L(2k) + 40`.
* `moment_k` (`k = 1, ..., 6`) : the class sum is `120 C_k` for `k ≤ 5` (so `2I` is a
  unitary 5-group) and `120 (C_6 + 1)` for `k = 6`.
* `catalan_values` : `C_1, ..., C_6 = 1, 2, 5, 14, 42, 132`.
-/

namespace YangMills.DesignOrder

open Real

/-- Lucas numbers. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

theorem lucas_binet (n : ℕ) : (lucas n : ℝ) = goldenRatio ^ n + goldenConj ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => norm_num [lucas]
    | 1, _ => simp [lucas, goldenRatio, goldenConj]
    | (m + 2), ih =>
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      simp only [lucas, Nat.cast_add, h1, h0]
      have g := goldenRatio_sq
      have c := goldenConj_sq
      calc goldenRatio ^ (m + 1) + goldenConj ^ (m + 1) + (goldenRatio ^ m + goldenConj ^ m)
          = goldenRatio ^ m * (goldenRatio + 1) + goldenConj ^ m * (goldenConj + 1) := by ring
        _ = goldenRatio ^ m * goldenRatio ^ 2 + goldenConj ^ m * goldenConj ^ 2 := by rw [g, c]
        _ = goldenRatio ^ (m + 2) + goldenConj ^ (m + 2) := by ring

/-- Class sum of `tr^(2k)` over `2I`: traces `±2` (one element each), `±φ` and `±(φ-1)`
(twelve each), `±1` (twenty each), `0` (thirty). -/
noncomputable def momentSum (k : ℕ) : ℝ :=
  2 * 2 ^ (2 * k) + 12 * (2 * goldenRatio ^ (2 * k)) + 12 * (2 * (goldenRatio - 1) ^ (2 * k))
    + 20 * (2 * 1 ^ (2 * k)) + 30 * 0 ^ (2 * k)

theorem moment_eq_lucas (k : ℕ) (hk : 1 ≤ k) :
    momentSum k = 2 * 4 ^ k + 24 * (lucas (2 * k) : ℝ) + 40 := by
  have h1 : goldenRatio - 1 = -goldenConj := by
    simp [goldenRatio, goldenConj]; ring
  have h2 : (2 : ℝ) ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
  have h3 : (0 : ℝ) ^ (2 * k) = 0 := zero_pow (by omega)
  have h4 : (-goldenConj) ^ (2 * k) = goldenConj ^ (2 * k) := by
    rw [pow_mul, pow_mul, neg_sq]
  rw [momentSum, h1, h2, h3, h4, lucas_binet]
  ring

theorem lucas_values : lucas 2 = 3 ∧ lucas 4 = 7 ∧ lucas 6 = 18 ∧ lucas 8 = 47 ∧
    lucas 10 = 123 ∧ lucas 12 = 322 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem catalan_values : catalan 1 = 1 ∧ catalan 2 = 2 ∧ catalan 3 = 5 ∧ catalan 4 = 14 ∧
    catalan 5 = 42 ∧ catalan 6 = 132 := by
  simp only [catalan_eq_centralBinom_div, Nat.centralBinom]
  decide

theorem moment_1 : momentSum 1 = 120 * catalan 1 := by
  rw [moment_eq_lucas 1 le_rfl, catalan_values.1, lucas_values.1]; norm_num

theorem moment_2 : momentSum 2 = 120 * catalan 2 := by
  rw [moment_eq_lucas 2 (by norm_num), catalan_values.2.1, lucas_values.2.1]; norm_num

theorem moment_3 : momentSum 3 = 120 * catalan 3 := by
  rw [moment_eq_lucas 3 (by norm_num), catalan_values.2.2.1, lucas_values.2.2.1]; norm_num

theorem moment_4 : momentSum 4 = 120 * catalan 4 := by
  rw [moment_eq_lucas 4 (by norm_num), catalan_values.2.2.2.1, lucas_values.2.2.2.1]; norm_num

theorem moment_5 : momentSum 5 = 120 * catalan 5 := by
  rw [moment_eq_lucas 5 (by norm_num), catalan_values.2.2.2.2.1, lucas_values.2.2.2.2.1]
  norm_num

theorem moment_6 : momentSum 6 = 120 * (catalan 6 + 1) := by
  rw [moment_eq_lucas 6 (by norm_num), catalan_values.2.2.2.2.2, lucas_values.2.2.2.2.2]
  norm_num

end YangMills.DesignOrder
