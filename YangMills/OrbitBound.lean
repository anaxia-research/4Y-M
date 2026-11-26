import Mathlib

/-!
# Certified ranges and the orbit bound (Subsection "Certified ranges and the orbit bound")

* The star bound `H(T) = A T^7 q^{-(T/2-2)}` halves along doublings once `q^{T/2} > 256`
  (`doubling_ratio`, `tails_of_start`), which gives the certified tails of the refinement
  bound (Proposition `ly:prop:Rtails`) from one exact inequality per row (`row0`–`row10`).
  The rows are checked in exact integer arithmetic with downward rounding (`powLB`,
  `powLB_le`, `pow_gt_of_cert`).
* The fixed-box obstruction (Proposition `ly:prop:fixedbox`): `fixedbox_witness`.
* The orbit bound gives the pressure bound (Theorem `ly:thm:orbit`): `telescope_pos`,
  `four_doublings`, `orbit_pressure`.
* Removing the vacuum (Proposition `ly:prop:vacuum`): `remainder_le`, `vplus_le`.
-/

namespace YangMills.OrbitBound

/-- The grid `2^{-96} ℤ` of the certificate. -/
def gridD : ℕ := 79228162514264337593543950336

/-- A lower bound for `D · (a/D)^n`, computed by binary powering on the grid with
downward rounding; the base is capped at `D · 2^400`, which only lowers it. -/
def powLB : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, h, _ => h
  | f + 1, a, h, n =>
    if n = 0 then h else
      powLB f (min (a * a / gridD) (gridD * 2 ^ 400)) (if n % 2 = 1 then h * a / gridD else h) (n / 2)

lemma gridD_pos : (0 : ℝ) < (gridD : ℝ) := by unfold gridD; norm_num

lemma cast_div_le' (x : ℕ) : ((x / gridD : ℕ) : ℝ) ≤ (x : ℝ) / gridD := Nat.cast_div_le

/-- The invariant of the binary powering: the output is at most `D z y^n`. -/
theorem powLB_le : ∀ (f a h n : ℕ) (y z : ℝ), 1 ≤ y → 0 ≤ z →
    (a : ℝ) ≤ gridD * y → (h : ℝ) ≤ gridD * z → (powLB f a h n : ℝ) ≤ gridD * z * y ^ n := by
  intro f
  induction f with
  | zero =>
    intro a h n y z hy hz _ hh
    simp only [powLB]
    have : z ≤ z * y ^ n := le_mul_of_one_le_right hz (one_le_pow₀ hy)
    nlinarith [gridD_pos]
  | succ f ih =>
    intro a h n y z hy hz ha hh
    simp only [powLB]
    split_ifs with hn hodd
    · subst hn; simp; linarith
    · -- odd step
      have hD := gridD_pos
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
      have hy0 : (0 : ℝ) ≤ y := by linarith
      have ha' : ((min (a * a / gridD) (gridD * 2 ^ 400) : ℕ) : ℝ) ≤ gridD * (y * y) := by
        have h1 : ((min (a * a / gridD) (gridD * 2 ^ 400) : ℕ) : ℝ) ≤ ((a * a / gridD : ℕ) : ℝ) := by
          exact_mod_cast min_le_left _ _
        have h2 := cast_div_le' (a * a)
        push_cast at h2
        have h3 : (a : ℝ) * a / gridD ≤ gridD * (y * y) := by
          rw [div_le_iff₀ hD]; nlinarith
        linarith
      have hh' : ((h * a / gridD : ℕ) : ℝ) ≤ gridD * (z * y) := by
        have h2 := cast_div_le' (h * a)
        push_cast at h2
        have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
        have h3 : (h : ℝ) * a / gridD ≤ gridD * (z * y) := by
          rw [div_le_iff₀ hD]; nlinarith
        linarith
      have := ih _ _ (n / 2) (y * y) (z * y) (by nlinarith) (by positivity) ha' hh'
      have hn2 : n = 2 * (n / 2) + 1 := by omega
      calc (powLB f _ _ (n / 2) : ℝ) ≤ gridD * (z * y) * (y * y) ^ (n / 2) := this
        _ = gridD * z * y ^ n := by
          conv_rhs => rw [hn2, pow_succ, pow_mul]
          ring
    · -- even step
      have hD := gridD_pos
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
      have ha' : ((min (a * a / gridD) (gridD * 2 ^ 400) : ℕ) : ℝ) ≤ gridD * (y * y) := by
        have h1 : ((min (a * a / gridD) (gridD * 2 ^ 400) : ℕ) : ℝ) ≤ ((a * a / gridD : ℕ) : ℝ) := by
          exact_mod_cast min_le_left _ _
        have h2 := cast_div_le' (a * a)
        push_cast at h2
        have h3 : (a : ℝ) * a / gridD ≤ gridD * (y * y) := by
          rw [div_le_iff₀ hD]; nlinarith
        linarith
      have := ih _ _ (n / 2) (y * y) z (by nlinarith) hz ha' hh
      have hn2 : n = 2 * (n / 2) := by omega
      calc (powLB f _ h (n / 2) : ℝ) ≤ gridD * z * (y * y) ^ (n / 2) := this
        _ = gridD * z * y ^ n := by
          conv_rhs => rw [hn2, pow_mul]
          ring

/-- A certificate `D · Pn < powLB · Pd` gives `Pn / Pd < q^n`. -/
theorem pow_gt_of_cert {q : ℝ} {a0 n Pn Pd : ℕ} (hq1 : 1 ≤ q) (ha : (a0 : ℝ) ≤ (gridD : ℝ) * q)
    (hPd : (0 : ℝ) < Pd) (hN : gridD * Pn < powLB 64 a0 gridD n * Pd) :
    (Pn : ℝ) / Pd < q ^ n := by
  have hle := powLB_le 64 a0 gridD n q 1 hq1 zero_le_one ha (by simp)
  have hN' : (gridD : ℝ) * Pn < (powLB 64 a0 gridD n : ℝ) * Pd := by exact_mod_cast hN
  have hD := gridD_pos
  rw [div_lt_iff₀ hPd]
  have : (powLB 64 a0 gridD n : ℝ) * Pd ≤ gridD * q ^ n * Pd := by
    have := mul_le_mul_of_nonneg_right hle hPd.le; simpa using this
  nlinarith

/-- Row `J = 0`, `B = 0.3449`: with `r = 1010` and `q = (1 - 1/r)/λ(B)`, `q^r > 256` and `q^r > P`. -/
theorem row0 :
    let B : ℝ := 3449 / 10000
    let lam : ℝ := 3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2)
    let q : ℝ := (1 - 1 / (1010 : ℝ)) / lam
    1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 1010 ∧
      768 * B * lam * (1 + q) * 1010 * (2024 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 0 < q ^ 1010 := by
  intro B lam q
  have hq : q = 492788735773 / 454062471030 := by
    simp only [q, lam, B]; norm_num
  have hl : lam = 449566803 / 488393197 := by
    simp only [lam, B]; norm_num
  have ha : ((85985406269003345607463119418 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 1010 * (2024 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 0 =
      ((348987368929296436570999992338570180296704000 : ℕ) : ℝ) / ((488393197 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam B
  have hN : gridD * 348987368929296436570999992338570180296704000 < powLB 64 85985406269003345607463119418 gridD 1010 * 488393197 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 85985406269003345607463119418 gridD 1010 * 1 := by decide +kernel
  refine ⟨by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 1`, `B = 0.3523`: with `r = 2022` and `q = (1 - 1/r)/λ(B)`, `q^r > 256` and `q^r > P`. -/
theorem row1 :
    let B : ℝ := 3523 / 10000
    let lam : ℝ := 3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2)
    let q : ℝ := (1 - 1 / (2022 : ℝ)) / lam
    1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 2022 ∧
      768 * B * lam * (1 + q) * 2022 * (4048 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 1 < q ^ 2022 := by
  intro B lam q
  have hq : q = 107994473297 / 103345450546 := by
    simp only [q, lam, B]; norm_num
  have hl : lam = 153331529 / 160308471 := by
    simp only [lam, B]; norm_num
  have ha : ((82792262608683023814831174292 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 2022 * (4048 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 1 =
      ((20368963609679219831652123122070915108569088000 : ℕ) : ℝ) / ((53436157 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam B
  have hN : gridD * 20368963609679219831652123122070915108569088000 < powLB 64 82792262608683023814831174292 gridD 2022 * 53436157 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 82792262608683023814831174292 gridD 2022 * 1 := by decide +kernel
  refine ⟨by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 2`, `B = 0.3563`: with `r = 4046` and `q = (1 - 1/r)/λ(B)`, `q^r > 256` and `q^r > P`. -/
theorem row2 :
    let B : ℝ := 3563 / 10000
    let lam : ℝ := 3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2)
    let q : ℝ := (1 - 1 / (4046 : ℝ)) / lam
    1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 4046 ∧
      768 * B * lam * (1 + q) * 4046 * (8096 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 2 < q ^ 4046 := by
  intro B lam q
  have hq : q = 1928959751185 / 1883999293722 := by
    simp only [q, lam, B]; norm_num
  have hl : lam = 465644907 / 476875093 := by
    simp only [lam, B]; norm_num
  have ha : ((81118892750981642800198563556 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 4046 * (8096 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 2 =
      ((95146467900158946879017856980855044211088556032000 : ℕ) : ℝ) / ((476875093 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam B
  have hN : gridD * 95146467900158946879017856980855044211088556032000 < powLB 64 81118892750981642800198563556 gridD 4046 * 476875093 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 81118892750981642800198563556 gridD 4046 * 1 := by decide +kernel
  refine ⟨by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 3`, `B = 0.35846`: with `r = 8094` and `q = (1 - 1/r)/λ(B)`, `q^r > 256` and `q^r > P`. -/
theorem row3 :
    let B : ℝ := 17923 / 50000
    let lam : ℝ := 3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2)
    let q : ℝ := (1 - 1 / (8094 : ℝ)) / lam
    1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 8094 ∧
      768 * B * lam * (1 + q) * 8094 * (16192 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 3 < q ^ 8094 := by
  intro B lam q
  have hq : q = 96040425837809 / 94841459463978 := by
    simp only [q, lam, B]; norm_num
  have hl : lam = 11717501787 / 11867098213 := by
    simp only [lam, B]; norm_num
  have ha : ((80229748774660296777713989859 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 8094 * (16192 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 3 =
      ((1226761363040268700477429303777818193806401661724262400 : ℕ) : ℝ) / ((11867098213 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam B
  have hN : gridD * 1226761363040268700477429303777818193806401661724262400 < powLB 64 80229748774660296777713989859 gridD 8094 * 11867098213 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 80229748774660296777713989859 gridD 8094 * 1 := by decide +kernel
  refine ⟨by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 4`, `B = 0.35961`: with `r = 16190` and `q = (1 - 1/r)/λ(B)`, `q^r > 256` and `q^r > P`. -/
theorem row4 :
    let B : ℝ := 35961 / 100000
    let lam : ℝ := 3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2)
    let q : ℝ := (1 - 1 / (16190 : ℝ)) / lam
    1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 16190 ∧
      768 * B * lam * (1 + q) * 16190 * (32384 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 4 < q ^ 16190 := by
  intro B lam q
  have hq : q = 766575367065593 / 761460717314970 := by
    simp only [q, lam, B]; norm_num
  have hl : lam = 47032780563 / 47351619437 := by
    simp only [lam, B]; norm_num
  have ha : ((79760329561666053992307306680 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 16190 * (32384 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 4 =
      ((2522086681080728211536000306300373874363846594385254809600 : ℕ) : ℝ) / ((47351619437 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam B
  have hN : gridD * 2522086681080728211536000306300373874363846594385254809600 < powLB 64 79760329561666053992307306680 gridD 16190 * 47351619437 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79760329561666053992307306680 gridD 16190 * 1 := by decide +kernel
  refine ⟨by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 5`, `B = 0.36023`: with `r = 32382` and `q = (1 - 1/r)/λ(B)`, `q^r > 256` and `q^r > P`. -/
theorem row5 :
    let B : ℝ := 36023 / 100000
    let lam : ℝ := 3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2)
    let q : ℝ := (1 - 1 / (32382 : ℝ)) / lam
    1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 32382 ∧
      768 * B * lam * (1 + q) * 32382 * (64768 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 5 < q ^ 32382 := by
  intro B lam q
  have hq : q = 1531253141403353 / 1525858284366234 := by
    simp only [q, lam, B]; norm_num
  have hl : lam = 47120569587 / 47288630413 := by
    simp only [lam, B]; norm_num
  have ha : ((79508283292489569533098916299 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 32382 * (64768 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 5 =
      ((1293974595830783745824624073604738480681036439326035227443200 : ℕ) : ℝ) / ((47288630413 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam B
  have hN : gridD * 1293974595830783745824624073604738480681036439326035227443200 < powLB 64 79508283292489569533098916299 gridD 32382 * 47288630413 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79508283292489569533098916299 gridD 32382 * 1 := by decide +kernel
  refine ⟨by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 7`, `B = 0.36073`: with `r = 129534` and `q = (1 - 1/r)/λ(B)`, `q^r > 256` and `q^r > P`. -/
theorem row7 :
    let B : ℝ := 36073 / 100000
    let lam : ℝ := 3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2)
    let q : ℝ := (1 - 1 / (129534 : ℝ)) / lam
    1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 129534 ∧
      768 * B * lam * (1 + q) * 129534 * (259072 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 7 < q ^ 129534 := by
  intro B lam q
  have hq : q = 2039618673870643 / 2037629577790686 := by
    simp only [q, lam, B]; norm_num
  have hl : lam = 15730461329 / 15745938671 := by
    simp only [lam, B]; norm_num
  have ha : ((79305503572323668480048009673 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 129534 * (259072 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 7 =
      ((113256712534128471870405292256086208265489732382037220113409638400 : ℕ) : ℝ) / ((15745938671 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam B
  have hN : gridD * 113256712534128471870405292256086208265489732382037220113409638400 < powLB 64 79305503572323668480048009673 gridD 129534 * 15745938671 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79305503572323668480048009673 gridD 129534 * 1 := by decide +kernel
  refine ⟨by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 10`, `B = 0.36089`: with `r = 1036286` and `q = (1 - 1/r)/λ(B)`, `q^r > 256` and `q^r > P`. -/
theorem row10 :
    let B : ℝ := 36089 / 100000
    let lam : ℝ := 3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2)
    let q : ℝ := (1 - 1 / (1036286 : ℝ)) / lam
    1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 1036286 ∧
      768 * B * lam * (1 + q) * 1036286 * (2072576 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 10 < q ^ 1036286 := by
  intro B lam q
  have hq : q = 48934986259919545 / 48927256700128218 := by
    simp only [q, lam, B]; norm_num
  have hl : lam = 47214047763 / 47221552237 := by
    simp only [lam, B]; norm_num
  have ha : ((79240679030836364691360547097 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 1036286 * (2072576 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 10 =
      ((45627265732380736738899467572063091967771517800731910501815707932976742400 : ℕ) : ℝ) / ((47221552237 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam B
  have hN : gridD * 45627265732380736738899467572063091967771517800731910501815707932976742400 < powLB 64 79240679030836364691360547097 gridD 1036286 * 47221552237 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79240679030836364691360547097 gridD 1036286 * 1 := by decide +kernel
  refine ⟨by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-! ## The doubling ratio and the tails -/

/-- `H(2s) = 128 q^{-m} H(s)` for `s = 2m`, `m ≥ 2`, where `H(T) = A T^7 q^{-(T/2-2)}`. -/
theorem doubling_ratio (A qi : ℝ) (m : ℕ) (hm : 2 ≤ m) :
    A * ((4 * m : ℕ) : ℝ) ^ 7 * qi ^ ((4 * m) / 2 - 2) =
      128 * qi ^ m * (A * ((2 * m : ℕ) : ℝ) ^ 7 * qi ^ ((2 * m) / 2 - 2)) := by
  have h1 : (4 * m) / 2 - 2 = (m - 2) + m := by omega
  have h2 : (2 * m) / 2 - 2 = m - 2 := by omega
  rw [h1, h2, pow_add]
  push_cast
  ring

/-- Once `q^r > 256` with `q > 1`, every later doubling ratio `128 q^{-m}`, `m ≥ r`, is
below `1/2`. -/
theorem ratio_lt_half (q : ℝ) (r m : ℕ) (hq : 1 < q) (h256 : 256 < q ^ r) (hm : r ≤ m) :
    128 * (q⁻¹) ^ m < 1 / 2 := by
  have hq0 : 0 < q := by linarith
  have h1 : q ^ r ≤ q ^ m := pow_le_pow_right₀ hq.le hm
  have h2 : (q⁻¹) ^ m = 1 / q ^ m := by rw [inv_pow, one_div]
  rw [h2]
  have hqm : 256 < q ^ m := lt_of_lt_of_le h256 h1
  have hpos : 0 < q ^ m := by positivity
  rw [mul_one_div, div_lt_div_iff₀ hpos (by norm_num)]
  linarith

/-- **The tails by induction.** If `H J < e J`, `e (j+1) = e j / 2`, and
`H (j+1) ≤ H j / 2` from `J` on, then `H j < e j` for every `j ≥ J`. -/
theorem tails_of_start (H e : ℕ → ℝ) (J : ℕ) (h0 : H J < e J)
    (he : ∀ j, e (j + 1) = e j / 2) (hH : ∀ j, J ≤ j → H (j + 1) ≤ H j / 2) :
    ∀ j, J ≤ j → H j < e j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact h0
  | succ j hj ih => rw [he]; linarith [hH j hj]

/-- Absolute smallness gives the refinement bound (as `X ≥ 0`). -/
theorem refine_of_tail (Xf Xc e : ℝ) (hc : 0 ≤ Xc) (hf : Xf < e) : Xf ≤ Xc + e := by linarith

/-! ## The fixed-box obstruction -/

/-- `log (2 - 7·10⁻⁶) > 0.69`. -/
theorem log_witness : (0.69 : ℝ) < Real.log (2 - 7 / 10 ^ 6) := by
  have h2 := Real.log_two_gt_d9
  have hy : (0 : ℝ) < 1 - 7 / (2 * 10 ^ 6) := by norm_num
  have hsplit : (2 : ℝ) - 7 / 10 ^ 6 = 2 * (1 - 7 / (2 * 10 ^ 6)) := by norm_num
  have hl := Real.one_sub_inv_le_log_of_pos hy
  rw [hsplit, Real.log_mul (by norm_num) hy.ne']
  have : (1 : ℝ) - (1 - 7 / (2 * 10 ^ 6))⁻¹ > -1 / 10 ^ 5 := by norm_num
  linarith

/-- **The witness at a fixed box.** If the first excited eigenvalue satisfies
`1 - r₁ ≤ 64 T² ε` with `T = 2024`, `ε < 1248 · 10⁻²⁰`, and the
normalised trace is at least `1 + r₁^T`, then its logarithm exceeds `0.69`. -/
theorem fixedbox_witness (r1 eps Z : ℝ)
    (he : eps < 1248 / 10 ^ 20) (hgap : 1 - r1 ≤ 64 * 2024 ^ 2 * eps)
    (hZ : 1 + r1 ^ 2024 ≤ Z) : (0.69 : ℝ) < Real.log Z := by
  have hb := one_add_mul_le_pow (a := r1 - 1) (by linarith) 2024
  have h1 : (1 : ℝ) + (r1 - 1) = r1 := by ring
  rw [h1] at hb
  have h3 : (2 : ℝ) - 7 / 10 ^ 6 < 1 + r1 ^ 2024 := by push_cast at hb; nlinarith
  have hpos : (0 : ℝ) < 2 - 7 / 10 ^ 6 := by norm_num
  have := Real.log_lt_log hpos (lt_of_lt_of_le h3 hZ)
  linarith [log_witness]

/-! ## The orbit bound gives the pressure bound -/

/-- `Y n ≤ Y 0 + Σ_{i<n} (Y (i+1) - Y i)_+`. -/
theorem telescope_pos (Y : ℕ → ℝ) (n : ℕ) :
    Y n ≤ Y 0 + ∑ i ∈ Finset.range n, max (Y (i + 1) - Y i) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := le_max_left (Y (n + 1) - Y n) 0
    linarith

/-- `e^y - 1 ≤ y / (1 - y)` for `0 ≤ y < 1`. -/
theorem exp_sub_one_le (y : ℝ) (hy1 : y < 1) : Real.exp y - 1 ≤ y / (1 - y) := by
  have h1 : 0 < 1 - y := by linarith
  have h := Real.add_one_le_exp (-y)
  have hk : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have hey : Real.exp y ≤ 1 / (1 - y) := by
    rw [le_div_iff₀ h1]; nlinarith [Real.exp_pos y]
  have : 1 / (1 - y) - 1 = y / (1 - y) := by field_simp; ring
  linarith

/-- One fixed-coupling doubling: from `0 ≤ x ≤ c` with `64 c < 1`,
`(e^{64x} - 1)^2 ≤ (64c/(1 - 64c))^2`. -/
theorem doubling_step (x c : ℝ) (hx : 0 ≤ x) (hxc : x ≤ c) (hc : 64 * c < 1) :
    (Real.exp (64 * x) - 1) ^ 2 ≤ (64 * c / (1 - 64 * c)) ^ 2 := by
  have h0 : 0 ≤ Real.exp (64 * x) - 1 := by
    have := Real.add_one_le_exp (64 * x); linarith
  have h1 := exp_sub_one_le (64 * x) (by linarith)
  have h2 : 64 * x / (1 - 64 * x) ≤ 64 * c / (1 - 64 * c) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  exact pow_le_pow_left₀ h0 (h1.trans h2) 2

/-- **Four doublings.** If `0 ≤ X k`, `X (k+1) ≤ (e^{64 X k} - 1)^2` and
`X 0 ≤ 2 · 10⁻⁴`, then `X 4 ≤ 15 · 10⁻⁶`. -/
theorem four_doublings (X : ℕ → ℝ) (h0 : ∀ k, 0 ≤ X k)
    (hs : ∀ k, X (k + 1) ≤ (Real.exp (64 * X k) - 1) ^ 2) (hX : X 0 ≤ 200 / 10 ^ 6) :
    X 4 ≤ 15 / 10 ^ 6 := by
  have step : ∀ k (c d : ℝ), X k ≤ c → 64 * c < 1 → (64 * c / (1 - 64 * c)) ^ 2 ≤ d →
      X (k + 1) ≤ d := fun k c d hk hc hd =>
    (hs k).trans ((doubling_step _ _ (h0 k) hk hc).trans hd)
  have a1 := step 0 _ (169 / 10 ^ 6) hX (by norm_num) (by norm_num)
  have a2 := step 1 _ (120 / 10 ^ 6) a1 (by norm_num) (by norm_num)
  have a3 := step 2 _ (60 / 10 ^ 6) a2 (by norm_num) (by norm_num)
  exact step 3 _ (15 / 10 ^ 6) a3 (by norm_num) (by norm_num)

/-- **The orbit bound gives the pressure bound** (Theorem `ly:thm:orbit`). Along an
orbit `Y`, with `Y 0 ≤ 3.36 · 10⁻⁵` (the box certificate) and total rise at most
`1.664 · 10⁻⁴` (the orbit bound), and four fixed-coupling doublings `X` starting at
`X 0 = Y n`, one has `X 4 ≤ 1.5 · 10⁻⁵ < 1/28684`. -/
theorem orbit_pressure (Y X : ℕ → ℝ) (n : ℕ) (hY0 : Y 0 ≤ 336 / 10 ^ 7)
    (hA : ∑ i ∈ Finset.range n, max (Y (i + 1) - Y i) 0 ≤ 1664 / 10 ^ 7)
    (hX0 : X 0 = Y n) (h0 : ∀ k, 0 ≤ X k)
    (hs : ∀ k, X (k + 1) ≤ (Real.exp (64 * X k) - 1) ^ 2) :
    X 4 ≤ 15 / 10 ^ 6 ∧ (15 / 10 ^ 6 : ℝ) < 1 / 28684 := by
  have := telescope_pos Y n
  refine ⟨four_doublings X h0 hs (by rw [hX0]; linarith), by norm_num⟩

/-- The refinement bound implies the orbit bound: rises bounded by `10⁻⁷ 2⁻ʲ` sum to
less than `1.664 · 10⁻⁴`. -/
theorem orbit_of_refine (Y : ℕ → ℝ) (n : ℕ)
    (hR : ∀ i < n, Y (i + 1) - Y i ≤ (1 / 10 ^ 7) * (1 / 2) ^ (n - 1 - i)) :
    ∑ i ∈ Finset.range n, max (Y (i + 1) - Y i) 0 ≤ 1664 / 10 ^ 7 := by
  have hle : ∀ i ∈ Finset.range n, max (Y (i + 1) - Y i) 0 ≤ (1 / 10 ^ 7) * (1 / 2) ^ (n - 1 - i) := by
    intro i hi
    exact max_le (hR i (Finset.mem_range.mp hi)) (by positivity)
  have hsum : ∑ i ∈ Finset.range n, (1 / 10 ^ 7 : ℝ) * (1 / 2) ^ (n - 1 - i) =
      ∑ j ∈ Finset.range n, (1 / 10 ^ 7 : ℝ) * (1 / 2) ^ j := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    congr 2; omega
  have hg : ∑ j ∈ Finset.range n, (1 / 10 ^ 7 : ℝ) * (1 / 2) ^ j ≤ 2 / 10 ^ 7 := by
    rw [← Finset.mul_sum, geom_sum_eq (by norm_num) n]
    have hp : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    have : ((1 / 2 : ℝ) ^ n - 1) / (1 / 2 - 1) = 2 - 2 * (1 / 2) ^ n := by field_simp; ring
    rw [this]; nlinarith
  calc _ ≤ ∑ i ∈ Finset.range n, (1 / 10 ^ 7 : ℝ) * (1 / 2) ^ (n - 1 - i) := Finset.sum_le_sum hle
    _ ≤ 2 / 10 ^ 7 := by rw [hsum]; exact hg
    _ ≤ 1664 / 10 ^ 7 := by norm_num

/-! ## Removing the vacuum -/

/-- Successive couplings on an orbit differ by at most `4 log 2 / 7 < 1` when the scale
function `ℓ(b) = b/c₁ - γ log(1 + b/4)` has `1/c₁ ≥ 2` and `0 ≤ γ ≤ 1`. -/
theorem rung_step_le (ci γ b b' : ℝ) (hci : 2 ≤ ci) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1)
    (hb : 0 ≤ b) (hbb : b ≤ b')
    (hstep : (b' * ci - γ * Real.log (1 + b' / 4)) - (b * ci - γ * Real.log (1 + b / 4))
      = Real.log 2) : b' - b < 1 := by
  have hpos : 0 < 1 + b / 4 := by linarith
  have hpos' : 0 < 1 + b' / 4 := by linarith
  have hl : Real.log (1 + b' / 4) - Real.log (1 + b / 4) ≤ (b' - b) / 4 := by
    rw [← Real.log_div hpos'.ne' hpos.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hpos' hpos)
    have h2 : (1 + b' / 4) / (1 + b / 4) - 1 ≤ (b' - b) / 4 := by
      rw [div_sub_one hpos.ne', div_le_div_iff₀ hpos (by norm_num)]; nlinarith
    linarith
  have h2 := Real.log_two_lt_d9
  have : (b' - b) * (7 / 4) ≤ Real.log 2 := by nlinarith
  nlinarith

/-- **The vacuum remainder.** With `S = 1012 · 2^i`, `M = 2^{80+6i}`, `d ≤ Y/M`,
`Y ≤ 48 b S⁴` and `b ≤ i + 1`, one has `d ≤ K 2⁻ⁱ`, `K = 48 · 1012⁴/2⁸⁰`. -/
theorem remainder_le (i : ℕ) (b Y d : ℝ) (hb : b ≤ i + 1)
    (hd : d ≤ Y / 2 ^ (80 + 6 * i)) (hY : Y ≤ 48 * b * ((1012 : ℝ) * 2 ^ i) ^ 4) :
    d ≤ (48 * 1012 ^ 4 / 2 ^ 80) * (1 / 2 : ℝ) ^ i := by
  have hM : (0 : ℝ) < 2 ^ (80 + 6 * i) := by positivity
  have hi : ((i : ℝ) + 1) ≤ 2 ^ i := by
    have := Nat.lt_two_pow_self (n := i); exact_mod_cast this
  have key : 48 * b * ((1012 : ℝ) * 2 ^ i) ^ 4 / 2 ^ (80 + 6 * i) =
      (48 * 1012 ^ 4 / 2 ^ 80) * b * (1 / 2 : ℝ) ^ i * (1 / 2) ^ i := by
    rw [pow_add, pow_mul', one_div_pow]
    field_simp
  have h1 : d ≤ (48 * 1012 ^ 4 / 2 ^ 80) * b * (1 / 2 : ℝ) ^ i * (1 / 2) ^ i := by
    rw [← key]; exact hd.trans (div_le_div_of_nonneg_right hY hM.le)
  have h2 : b * (1 / 2 : ℝ) ^ i ≤ 1 := by
    have : (1 / 2 : ℝ) ^ i = 1 / 2 ^ i := by rw [one_div_pow]
    rw [this, mul_one_div, div_le_one (by positivity)]; linarith
  have hK : (0 : ℝ) ≤ 48 * 1012 ^ 4 / 2 ^ 80 := by positivity
  have hh : (0 : ℝ) ≤ (1 / 2) ^ i := by positivity
  calc d ≤ _ := h1
    _ = (48 * 1012 ^ 4 / 2 ^ 80) * (b * (1 / 2 : ℝ) ^ i) * (1 / 2) ^ i := by ring
    _ ≤ (48 * 1012 ^ 4 / 2 ^ 80) * 1 * (1 / 2) ^ i := by gcongr
    _ = _ := by ring

/-- `K = 48 · 1012⁴ / 2⁸⁰ < 4.17 · 10⁻¹¹`. -/
theorem K_lt : (48 * 1012 ^ 4 / 2 ^ 80 : ℝ) < 417 / 10 ^ 13 := by norm_num

/-- **The variation inequalities.** If `Y i = F i + d i` with `d ≥ 0`, then
`V₊(Y) ≤ V₊(F) + Σ d (i+1)` and `V₊(F) ≤ V₊(Y) + Σ d i`. -/
theorem vplus_le (Y F d : ℕ → ℝ) (n : ℕ) (hd : ∀ i, 0 ≤ d i) (hY : ∀ i, Y i = F i + d i) :
    ∑ i ∈ Finset.range n, max (Y (i + 1) - Y i) 0 ≤
        ∑ i ∈ Finset.range n, max (F (i + 1) - F i) 0 + ∑ i ∈ Finset.range n, d (i + 1) ∧
      ∑ i ∈ Finset.range n, max (F (i + 1) - F i) 0 ≤
        ∑ i ∈ Finset.range n, max (Y (i + 1) - Y i) 0 + ∑ i ∈ Finset.range n, d i := by
  constructor
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hY, hY]
    have := hd i; have := hd (i + 1)
    refine max_le ?_ (by positivity)
    have := le_max_left (F (i + 1) - F i) 0
    linarith
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hY i; have h2 := hY (i + 1)
    have := hd i; have := hd (i + 1)
    refine max_le ?_ (by positivity)
    have := le_max_left (Y (i + 1) - Y i) 0
    linarith

end YangMills.OrbitBound
