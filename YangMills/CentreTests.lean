import Mathlib

/-!
# Tests of the systems of SU(N)

Finite arithmetic of Lemma `ly:lem:heis` and Proposition `ly:prop:psuntests` of the paper:
the distribution of the Pfaffian `Pf(c) = c12 c34 - c13 c24 + c14 c23` on `Z_N^6` for
`N = 2, 3, 4` (which gives the Gauss sums `sum_c w^{k Pf(c)} = (N gcd(k,N))^3` used at
`beta = 0`), the divisibility step of the lemma, the twisted counts of the Hessian and
Valentiner groups, and the numerical bounds for the `Z_N` gauge theory.
-/

namespace YangMills.CentreTests

/-- Digit `i` of `m` in base `N`. -/
def dig (N m i : ℕ) : ℕ := m / N ^ i % N

/-- The Pfaffian of the class with digits `(c12, c13, c14, c23, c24, c34)`, as a residue
mod `N` (the minus sign is written as `(N - 1)`). -/
def pfN (N m : ℕ) : ℕ :=
  (dig N m 0 * dig N m 5 + (N - 1) * (dig N m 1 * dig N m 4) + dig N m 2 * dig N m 3) % N

/-- Number of classes `c` in `Z_N^6` with `Pf(c) = r`. -/
def cnt (N r : ℕ) : ℕ := ((List.range (N ^ 6)).filter (fun m => pfN N m = r)).length

theorem pf2_counts : cnt 2 0 = 36 ∧ cnt 2 1 = 28 := by decide +kernel

theorem pf3_counts : cnt 3 0 = 261 ∧ cnt 3 1 = 234 ∧ cnt 3 2 = 234 := by decide +kernel

theorem pf4_counts : cnt 4 0 = 1184 ∧ cnt 4 1 = 896 ∧ cnt 4 2 = 1120 ∧ cnt 4 3 = 896 := by
  decide +kernel

/-- Gauss sums from the counts: for `N = 3` and `k = 1, 2` the sum is
`261 + 234 (w + w^2) = 27 = 3^3`; for `N = 4`, `k = 1, 3` give `1184 - 1120 = 64 = 4^3`
(the terms with `i` and `-i` cancel), `k = 2` gives `1184 - 896 + 1120 - 896 = 512 = 8^3`,
and `N = 2` gives `36 - 28 = 8 = 2^3`. -/
theorem gauss_from_counts :
    (261 : ℤ) - 234 = 3 ^ 3 ∧ (1184 : ℤ) - 1120 = 4 ^ 3 ∧
    (1184 : ℤ) - 896 + 1120 - 896 = (4 * 2) ^ 3 ∧ (36 : ℤ) - 28 = 2 ^ 3 := by norm_num

/-- The hyperbolic quadric count `p^5 + p^3 - p^2` of classes with `Pf(c) = 0`,
for `p = 2, 3`. -/
theorem pf_zero_formula : cnt 2 0 = 2 ^ 5 + 2 ^ 3 - 2 ^ 2 ∧ cnt 3 0 = 3 ^ 5 + 3 ^ 3 - 3 ^ 2 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- The divisibility step of Lemma `ly:lem:heis`: if `e1, e2` divide `N` and the dimension
`(N / e1) (N / e2)` of an irreducible subspace divides `N`, then `N` divides `e1 e2`. -/
theorem heis_div (N e1 e2 : ℕ) (hN : 0 < N) (h1 : e1 ∣ N) (h2 : e2 ∣ N)
    (h : (N / e1) * (N / e2) ∣ N) : N ∣ e1 * e2 := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have he1 : 0 < e1 := by
    rcases Nat.eq_zero_or_pos e1 with h0 | h0
    · subst h0; simp at ha; omega
    · exact h0
  have he2 : 0 < e2 := by
    rcases Nat.eq_zero_or_pos e2 with h0 | h0
    · subst h0; simp at hb; omega
    · exact h0
  have hapos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0; simp at ha; omega
    · exact h0
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0; simp at hb; omega
    · exact h0
  have hNa : N / e1 = a := by rw [ha]; exact Nat.mul_div_cancel_left a he1
  have hNb : N / e2 = b := by rw [hb]; exact Nat.mul_div_cancel_left b he2
  rw [hNa, hNb] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  have hab : 0 < a * b := Nat.mul_pos hapos hbpos
  apply Nat.eq_of_mul_eq_mul_right hab
  calc e1 * e2 * (a * b) = (e1 * a) * (e2 * b) := by ring
    _ = N * N := by rw [← ha, ← hb]
    _ = N * (a * b * m) := by rw [← hm]
    _ = N * m * (a * b) := by ring

/-- Twisted counts of the Hessian group (order 648): `|Hom_0| = 648 * 9747`, 260 nonzero
classes with `Pf = 0`, each `17496`, total `27 * 648 * 621`. -/
theorem hessian_counts :
    6316056 = 648 * 9747 ∧ 6316056 + 260 * 17496 = 27 * 648 * 621 ∧ cnt 3 0 - 1 = 260 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [pf3_counts.1]

/-- Twisted counts of the Valentiner group (order 1080): `|Hom_0| = 1080 * 3258`,
260 classes of `19440`, total `27 * 1080 * 294`. -/
theorem valentiner_counts :
    3518640 = 1080 * 3258 ∧ 3518640 + 260 * 19440 = 27 * 1080 * 294 := by norm_num

/-- The lower bound of Proposition `ly:prop:psuntests`(c): quadruples with at most one
entry outside the centre give `N^3 (4q - 3N) >= (5/2) N^3 q` when `q >= 2N`. -/
theorem finite_lower (N q : ℕ) (h : 2 * N ≤ q) : 5 * q ≤ 2 * (4 * q - 3 * N) := by omega

theorem finite_count (N q : ℕ) (h : N ≤ q) :
    N ^ 4 + 4 * (q - N) * N ^ 3 = N ^ 3 * (4 * q - 3 * N) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  have e1 : N + r - N = r := by omega
  have e2 : 4 * (N + r) - 3 * N = N + 4 * r := by omega
  rw [e1, e2]; ring

/-- The constants in Proposition `ly:prop:psuntests`(a): `8 * 96 = 4 * 192 = 768` and
`768 = 192 * 4`. -/
theorem zn_coef : 8 * 96 = 768 ∧ 4 * 192 = 768 ∧ 192 * 4 = 768 := by norm_num

/-- The bound at `T = 8`, `N = 2^8`: below `1.8312e-4 < 1/4097`. -/
theorem zn_T8 :
    (192 : ℚ) * 8 ^ 4 * (1 / 2 ^ 32 + 4 * (2 ^ 8) ^ 3 * (1 / 2 ^ 128 + 1 / 2 ^ 256))
      < 18312 / 10 ^ 8 ∧ (18312 : ℚ) / 10 ^ 8 < 1 / 4097 := by
  constructor <;> norm_num

/-- Monotonicity of the first term `T^4 2^(-4T)`: `(T+1)^4 <= 16 T^4`. -/
theorem zn_step_first (T : ℕ) (hT : 1 ≤ T) : (T + 1) ^ 4 ≤ 16 * T ^ 4 := by
  have h : T + 1 ≤ 2 * T := by omega
  calc (T + 1) ^ 4 ≤ (2 * T) ^ 4 := Nat.pow_le_pow_left h 4
    _ = 16 * T ^ 4 := by ring

/-- Monotonicity of `2^(3T) T^4 2^(-2T^2)` (the second term with `N = 2^T`, and the bound on
`N^3 eta_1`): `8 (T+1)^4 <= 2^(4T+2) T^4` for `T >= 2`. -/
theorem zn_step_second (T : ℕ) (hT : 2 ≤ T) : 8 * (T + 1) ^ 4 ≤ 2 ^ (4 * T + 2) * T ^ 4 := by
  have h1 := zn_step_first T (by omega)
  have h2 : 2 ^ 10 ≤ 2 ^ (4 * T + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 0 < T ^ 4 := by positivity
  nlinarith

/-- `N^3 eta_1 <= 2^(3T) 96 T^4 2^(-2T^2) = 96 * 2^(-12) < 0.024` at `T = 4`, and the flux-half
loss `2 N^3 eta_1 < 1/20`. -/
theorem zn_eta4 : (2 : ℚ) ^ 12 * 96 * 4 ^ 4 / 2 ^ 32 = 96 / 2 ^ 12 ∧ (96 : ℚ) / 2 ^ 12 < 24 / 1000 ∧
    2 * ((24 : ℚ) / 1000) < 1 / 20 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- The parity step of Proposition `ly:prop:spn`(a): if `2N` divides `N^2 p` and `N` is odd,
then `p` is even. -/
theorem sp_odd (N p : ℕ) (hN : N % 2 = 1) (h : 2 * N ∣ N ^ 2 * p) : 2 ∣ p := by
  have h2 : 2 ∣ N ^ 2 * p := Nat.dvd_trans (Dvd.intro N rfl) h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h3 | h3
  · exfalso
    have : 2 ∣ N := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h3
    omega
  · exact h3

/-- Twisted counts in `Sp(2)` (Proposition `ly:prop:spn`(b)): `Q8 o D8` (order 32) and
`2I o D8` (order 480); torsion-free and dyonic sums divided by `8q`. -/
theorem sp2_counts :
    726016 + 322560 = 8 * 32 * 4096 ∧ 726016 - 322560 = 8 * 32 * 1576 ∧
    22225920 + 1612800 = 8 * 480 * 6208 ∧ 22225920 - 1612800 = 8 * 480 * 5368 ∧
    32 ^ 4 = 8 * 32 * 4096 := by norm_num

/-- The neutral half at the Potts point (Proposition `ly:prop:potts`): `|Hom_0|` plus
`(|C|^3 - 1)` temporal classes, divided by `|C|^3 q`, for `2I`, the Hessian and the
Valentiner groups. -/
theorem neutral_counts :
    76320 + 7 * 480 = 8 * 120 * 83 ∧ 6316056 + 26 * 17496 = 27 * 648 * 387 ∧
    3518640 + 26 * 19440 = 27 * 1080 * 138 := by norm_num

end YangMills.CentreTests
