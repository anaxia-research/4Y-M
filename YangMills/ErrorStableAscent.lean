import Mathlib
import YangMills.GapFree

/-!
# Error-stable quadratic ascent

These are arithmetic theorems about real sequences. They do not assert that
Yang--Mills partition functions satisfy the recurrence or the error bounds.
The intended normalization is `z n = A * y n`, with `A = 16.83` in the
quadratic majorant of Theorem 7.56 of the current paper.

An error exponential in `2 ^ n` is exponential in physical time when the
time at step `n` is `2 ^ n * T₀`. A merely geometric error in `n` does not
satisfy this sufficient error budget.
-/

namespace YangMills.ErrorStableAscent

/-- The envelope used by the ascent squares under a single time doubling. -/
theorem dyadic_power_succ (q : ℝ) (n : ℕ) :
    q ^ (2 ^ (n + 1)) = (q ^ (2 ^ n)) ^ 2 := by
  rw [pow_succ, pow_mul]

/-- A variable coefficient version of the ascent. The admissible coefficients
`b n` can themselves obey a quadratic recurrence with an error budget `η n`.
No upper bound on `q` or `b` is needed for this algebraic statement. -/
theorem variable_budget_ascent
    (z ε b η : ℕ → ℝ) (q : ℝ)
    (hz : ∀ n, 0 ≤ z n) (hb : ∀ n, 0 ≤ b n) (hq : 0 ≤ q)
    (hbase : z 0 ≤ b 0 * q)
    (hrec : ∀ n, z (n + 1) ≤ z n ^ 2 + ε n)
    (herr : ∀ n, ε n ≤ η n * q ^ (2 ^ (n + 1)))
    (hbudget : ∀ n, b n ^ 2 + η n ≤ b (n + 1)) :
    ∀ n, z n ≤ b n * q ^ (2 ^ n) := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
      have hp : 0 ≤ q ^ (2 ^ n) := pow_nonneg hq _
      have hprod :
          0 ≤ (b n * q ^ (2 ^ n) - z n) *
            (b n * q ^ (2 ^ n) + z n) :=
        mul_nonneg (by linarith) (add_nonneg (mul_nonneg (hb n) hp) (hz n))
      have hsq : z n ^ 2 ≤ b n ^ 2 * (q ^ (2 ^ n)) ^ 2 := by
        nlinarith
      have he := herr n
      have hr := hrec n
      have hbudget' := mul_le_mul_of_nonneg_right (hbudget n) (sq_nonneg (q ^ (2 ^ n)))
      rw [dyadic_power_succ] at he ⊢
      nlinarith

/-- Fixed reserve `c (1-c)` suffices to preserve a double-exponential envelope.
For the decay application take `0 < q < 1`. The endpoints are deliberately
included in this arithmetic theorem. -/
theorem error_stable_ascent
    (z ε : ℕ → ℝ) (c q : ℝ)
    (hz : ∀ n, 0 ≤ z n)
    (hc0 : 0 ≤ c) (_hc1 : c ≤ 1) (hq0 : 0 ≤ q) (_hq1 : q ≤ 1)
    (hbase : z 0 ≤ c * q)
    (hrec : ∀ n, z (n + 1) ≤ z n ^ 2 + ε n)
    (herr : ∀ n, ε n ≤ c * (1 - c) * q ^ (2 ^ (n + 1))) :
    ∀ n, z n ≤ c * q ^ (2 ^ n) := by
  apply variable_budget_ascent z ε (fun _ => c) (fun _ => c * (1 - c)) q
    hz (fun _ => hc0) hq0 hbase hrec herr
  intro n
  dsimp
  nlinarith

/-- Rescaling a recurrence with coefficient `A` gives the normalized recurrence.
This statement makes the factor `A` in the admissible error explicit. -/
theorem rescale_recurrence
    (y ε : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hrec : ∀ n, y (n + 1) ≤ A * y n ^ 2 + ε n) (n : ℕ) :
    A * y (n + 1) ≤ (A * y n) ^ 2 + A * ε n := by
  have h := mul_le_mul_of_nonneg_left (hrec n) hA
  nlinarith

/-- The unnormalized form: `A εₙ ≤ c(1-c) q^(2^(n+1))` and
`A y₀ ≤ c q` imply `A yₙ ≤ c q^(2^n)`. All model-dependent inputs are
explicit hypotheses. -/
theorem scaled_error_stable_ascent
    (y ε : ℕ → ℝ) (A c q : ℝ)
    (hA : 0 ≤ A) (hy : ∀ n, 0 ≤ y n)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hbase : A * y 0 ≤ c * q)
    (hrec : ∀ n, y (n + 1) ≤ A * y n ^ 2 + ε n)
    (herr : ∀ n, A * ε n ≤ c * (1 - c) * q ^ (2 ^ (n + 1))) :
    ∀ n, A * y n ≤ c * q ^ (2 ^ n) := by
  exact error_stable_ascent (fun n => A * y n) (fun n => A * ε n) c q
    (fun n => mul_nonneg hA (hy n)) hc0 hc1 hq0 hq1 hbase
    (rescale_recurrence y ε A hA hrec) herr

/-- The actual exponential recurrence, using the existing analytic majorant
`GapFree.doubling_step`. The reserve condition `c*q ≤ 16.83/20` closes the
range assumption inside the induction; it is not assumed at later steps. -/
theorem exponential_error_stable_ascent
    (y ε : ℕ → ℝ) (c q : ℝ)
    (hy : ∀ n, 0 ≤ y n)
    (hc0 : 0 ≤ c) (_hc1 : c ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hbase : 16.83 * y 0 ≤ c * q)
    (hwindow : c * q ≤ 16.83 / 20)
    (hrec : ∀ n, y (n + 1) ≤ 16 * (Real.exp (y n) - 1) ^ 2 + ε n)
    (herr : ∀ n, 16.83 * ε n ≤ c * (1 - c) * q ^ (2 ^ (n + 1))) :
    ∀ n, y n ≤ 1 / 20 ∧ 16.83 * y n ≤ c * q ^ (2 ^ n) := by
  intro n
  induction n with
  | zero => exact ⟨by nlinarith, by simpa using hbase⟩
  | succ n ih =>
      have hmajorant := (GapFree.doubling_step (y n) (hy n) ih.1).1
      have hr := hrec n
      have hstep :
          16.83 * y (n + 1) ≤ (16.83 * y n) ^ 2 + 16.83 * ε n := by
        nlinarith
      have hsq : (16.83 * y n) ^ 2 ≤ (c * q ^ (2 ^ n)) ^ 2 :=
        pow_le_pow_left₀ (by nlinarith [hy n]) ih.2 2
      have he := herr n
      have hnext : 16.83 * y (n + 1) ≤ c * q ^ (2 ^ (n + 1)) := by
        rw [dyadic_power_succ] at he ⊢
        nlinarith
      have hpower : 1 ≤ (2 : ℕ) ^ (n + 1) := by
        have hp : 0 < (2 : ℕ) ^ (n + 1) := pow_pos (by norm_num) _
        omega
      have hqpower : q ^ (2 ^ (n + 1)) ≤ q := by
        have h : q ^ (2 ^ (n + 1)) ≤ q ^ (1 : ℕ) :=
          pow_le_pow_of_le_one hq0 hq1 hpower
        simpa using h
      have hcap := mul_le_mul_of_nonneg_left hqpower hc0
      exact ⟨by nlinarith, hnext⟩

end YangMills.ErrorStableAscent
