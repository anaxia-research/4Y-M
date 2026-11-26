import Mathlib
import YangMills.OrbitBound

/-!
# The combined flow and five neighbours: a larger averaged gain past the star threshold

Arithmetic of Lemmas `lem:combflow`, `lem:fivevar` and Proposition `prop:combsource` of the
paper, and the columns of Proposition `ly:prop:Rtails` that use the contraction `λ'' = θ₂ λ`,
where `θ₂ = 1 - 2 g β² V(β)`, `g = e_z + 3 e_x = 3/40`, `e_z = 69/2500`, `e_x = 79/5000`, and
`V(b) = (15 m)²/(5 (3 - 3 m + K A) + 16 b (1 - m))` with `K = 6b`, `m = 1/(3/2 + √(K² + 25/4))`,
`A = K/(1 + √(K² + 9))`. The analytic inputs (the flow bound, the slice flow and the reflection
flow, the ball-arithmetic enclosure of Appendix `app:vmfcomp`, the Riccati barriers, and the
Bochner identity behind `V`) are not formalised here.

* `ex_closed` : `1/4 - 1/(1 + s) = κ²/(4 (1 + s)(s + 3))` when `s² = κ² + 9`.
* `ex_at_K1` : `s = 37085/10000` dominates `√(K₁² + 9)`, `K₁ = 109/50`, and
  `4 (1 + s)(s + 3) e_x/2 ≤ 1`.
* `ex_antitone`, `ell_antitone` : the two bounds decrease in `s`.
* `g_sum` : `e_z + 3 e_x = 3/40`.
* `V_zero` : `V(0) = 5/4`.
* `V_at_b2` : at `β₂ = 1813/5000`, with `s' = 3314097/10⁶ ≥ √(K² + 25/4)` and
  `s = 1852919/500000 ≤ √(K² + 9)`, `V ≥ 4513/10000`; also `6 β₂ ≤ K₁`.
* `comb_threshold` : with `θ₂ = 1 - 2 g (3608/10000)² (4513/10000)`,
  `θ₂ λ(β₂) ≤ 1 - 2/10⁴`, `0 < θ₂ < 1`, and `λ(3608/10000) ≤ 1 - 2/10⁴`.
* `comb_consts` : the constants of the uniform cube condition, of the datum and of the
  monotonicity argument at `β₂`.
* `comb_gap` : `2/10⁴/(1250 e²) > 21/10⁹`.
* `combrow0`, ..., `combrow9` : columns `J = 0, ..., 9` with `λ''`.
-/

namespace YangMills.CombinedFlow

open YangMills.OrbitBound

/-- The star contraction `λ = 6 c s(c)` as a function of `β_W` (Lemma `lem:sclosed`). -/
noncomputable def lam (b : ℝ) : ℝ := 3 * b * (4 + b) / (8 - 8 * b - 3 * b ^ 2)

theorem ex_closed (κ s : ℝ) (hs : 0 < s) (hss : s ^ 2 = κ ^ 2 + 9) :
    1 / 4 - 1 / (1 + s) = κ ^ 2 / (4 * ((1 + s) * (s + 3))) := by
  have h1 : (1 + s) ≠ 0 := by intro h; linarith
  have h2 : (s + 3) ≠ 0 := by intro h; linarith
  field_simp
  nlinarith [hss]

theorem ex_at_K1 :
    ((109 : ℝ) / 50) ^ 2 + 9 ≤ ((37085 : ℝ) / 10000) ^ 2 ∧
      4 * ((1 + (37085 : ℝ) / 10000) * ((37085 : ℝ) / 10000 + 3)) * ((79 : ℝ) / 10000) ≤ 1 := by
  constructor <;> norm_num

theorem ex_antitone (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    1 / (4 * ((1 + t) * (t + 3))) ≤ 1 / (4 * ((1 + s) * (s + 3))) := by
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

theorem g_sum : (69 : ℝ) / 2500 + 3 * (79 / 5000) = 3 / 40 := by norm_num

theorem V_zero :
    (15 * (1 / (3 / 2 + 5 / 2 : ℝ))) ^ 2 / (5 * (3 - 3 * (1 / (3 / 2 + 5 / 2)) + 0) + 0) = 5 / 4 := by
  norm_num

theorem V_at_b2 :
    let b : ℝ := 1813 / 5000
    let s' : ℝ := 3314097 / 1000000
    let s : ℝ := 1852919 / 500000
    let m : ℝ := 1 / (3 / 2 + s')
    (6 * b) ^ 2 + 25 / 4 ≤ s' ^ 2 ∧ s ^ 2 ≤ (6 * b) ^ 2 + 9 ∧ 6 * b ≤ 109 / 50 ∧
      (4513 : ℝ) / 10000 ≤
        (15 * m) ^ 2 / (5 * (3 - 3 * m + 6 * b * (6 * b / (1 + s))) + 16 * b * (1 - m)) := by
  intro b s' s m
  simp only [m, s, s', b]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

theorem ell_antitone (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    1 / (3 / 2 + t) ≤ 1 / (3 / 2 + s) := by
  apply one_div_le_one_div_of_le
  · linarith
  · linarith

theorem comb_threshold :
    let θ₂ : ℝ := 1 - 2 * (3 / 40) * (3608 / 10000) ^ 2 * (4513 / 10000)
    θ₂ * lam (1813 / 5000) ≤ 1 - 2 / 10 ^ 4 ∧ lam (3608 / 10000) ≤ 1 - 2 / 10 ^ 4 ∧
      θ₂ < 1 ∧ 0 < θ₂ := by
  intro θ₂
  simp only [θ₂, lam]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- Constants at `β₂ = 0.3626`, `c ≤ 0.0907`: `(1 - λ'')A < 1 + 3c + 3 ≤ 4.2721` and
`0.42721 + 27/400 < 1/2` (Theorem `thm:uniformthreshold`); `192 β₂ · 3 · (1/6) · 2 = 69.6192`
and `24 · 69.6192 = 1670.8608` (Theorem `ds:thm:datum`); `θ₂ ≥ 1 - (5/2) g β₂² > 0.97`,
`5 g β₂ < 0.14`, `0.97/4 - 0.14 · 0.17 > 0`. -/
theorem comb_consts :
    (1813 : ℝ) / 5000 / 4 ≤ 907 / 10000 ∧ 1 + 3 * ((907 : ℝ) / 10000) + 3 = 42721 / 10000 ∧
      (42721 : ℝ) / 100000 + 27 / 400 < 1 / 2 ∧
      192 * ((1813 : ℝ) / 5000) * 3 * (1 / 6) * 2 = 696192 / 10000 ∧
      24 * ((696192 : ℝ) / 10000) = 16708608 / 10000 ∧
      (97 : ℝ) / 100 < 1 - 5 / 2 * (3 / 40) * (1813 / 5000) ^ 2 ∧
      5 * (3 / 40) * ((1813 : ℝ) / 5000) < 14 / 100 ∧
      (0 : ℝ) < 97 / 100 * (1 / 4) - 14 / 100 * (17 / 100) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

theorem comb_gap : (21 : ℝ) / 10 ^ 9 < 2 / 10 ^ 4 / (1250 * Real.exp 1 ^ 2) := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 := by gcongr
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- Row `J = 0`, `B = 0.34658`: `λ'' = t λ(B)` with `t = 1 - 2 g B² V`, `g = 3/40`, where
`V = (15 m)²/(5 (3 - 3 m + K A) + 16 B (1 - m))`, `K = 6B`, `m = 1/(3/2 + s')`, `A = K/(1 + s)`,
`s' = 1625903/500000` `≥ √(K² + 25/4)`, `s = 3650237/1000000` `≤ √(K² + 9)`; with `r = 1010` and `q = (1 - 1/r)/λ''`,
`q^r > 256` and `q^r > P`. -/
theorem combrow0 :
    let B : ℝ := 34658 / 100000
    let s' : ℝ := 1625903 / 500000
    let s : ℝ := 3650237 / 1000000
    let m : ℝ := 1 / (3 / 2 + s')
    let V : ℝ := (15 * m) ^ 2 / (5 * (3 - 3 * m + 6 * B * (6 * B / (1 + s))) + 16 * B * (1 - m))
    let t : ℝ := 1 - 2 * (3 / 40) * B ^ 2 * V
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (1010 : ℝ)) / lam
    (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 ∧ s ^ 2 ≤ (6 * B) ^ 2 + 9 ∧ 0 ≤ s ∧ 1 < q ∧ lam * q < 1 ∧
      (256 : ℝ) < q ^ 1010 ∧
      768 * B * lam * (1 + q) * 1010 * (2024 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 0 < q ^ 1010 := by
  intro B s' s m V t lam q
  have hs' : (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 := by simp only [s', B]; norm_num
  have hs : s ^ 2 ≤ (6 * B) ^ 2 + 9 := by simp only [s, B]; norm_num
  have hs0 : 0 ≤ s := by simp only [s]; norm_num
  have hq : q = 75338405099516801966207026747662319 / 69423254637588028558681532575319340 := by
    simp only [q, lam, t, V, m, s, s', B]; norm_num
  have hl : lam = 68735895680780226295724289678534 / 74666407432623193227162563674591 := by
    simp only [lam, t, V, m, s, s', B]; norm_num
  have ha : ((85978731967403718769584374774 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 1010 * (2024 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 0 =
      ((53615681224814491033408316676292489262675413459044630577314948710400 : ℕ) : ℝ) / ((74666407432623193227162563674591 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t V m s s' B
  have hN : gridD * 53615681224814491033408316676292489262675413459044630577314948710400 < powLB 64 85978731967403718769584374774 gridD 1010 * 74666407432623193227162563674591 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 85978731967403718769584374774 gridD 1010 * 1 := by decide +kernel
  refine ⟨hs', hs, hs0, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 1`, `B = 0.35401`: `λ'' = t λ(B)` with `t = 1 - 2 g B² V`, `g = 3/40`, where
`V = (15 m)²/(5 (3 - 3 m + K A) + 16 B (1 - m))`, `K = 6B`, `m = 1/(3/2 + s')`, `A = K/(1 + s)`,
`s' = 3280493/1000000` `≥ √(K² + 25/4)`, `s = 3675817/1000000` `≤ √(K² + 9)`; with `r = 2022` and `q = (1 - 1/r)/λ''`,
`q^r > 256` and `q^r > P`. -/
theorem combrow1 :
    let B : ℝ := 35401 / 100000
    let s' : ℝ := 3280493 / 1000000
    let s : ℝ := 3675817 / 1000000
    let m : ℝ := 1 / (3 / 2 + s')
    let V : ℝ := (15 * m) ^ 2 / (5 * (3 - 3 * m + 6 * B * (6 * B / (1 + s))) + 16 * B * (1 - m))
    let t : ℝ := 1 - 2 * (3 / 40) * B ^ 2 * V
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (2022 : ℝ)) / lam
    (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 ∧ s ^ 2 ≤ (6 * B) ^ 2 + 9 ∧ 0 ≤ s ∧ 1 < q ∧ lam * q < 1 ∧
      (256 : ℝ) < q ^ 2022 ∧
      768 * B * lam * (1 + q) * 2022 * (4048 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 1 < q ^ 2022 := by
  intro B s' s m V t lam q
  have hs' : (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 := by simp only [s', B]; norm_num
  have hs : s ^ 2 ≤ (6 * B) ^ 2 + 9 := by simp only [s, B]; norm_num
  have hs0 : 0 ≤ s := by simp only [s]; norm_num
  have hq : q = 304219912146132746252690379298290802463 / 291140128277616055899094040073345594134 := by
    simp only [q, lam, t, V, m, s, s', B]; norm_num
  have hl : lam = 431958647296166255043166231562827291 / 451588192201087698544320206776285209 := by
    simp only [lam, t, V, m, s, s', B]; norm_num
  have ha : ((82787573056936572435268364813 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 2022 * (4048 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 1 =
      ((57659378213923247022943807288922106850774469860123187323582534451095142400 : ℕ) : ℝ) / ((150529397400362566181440068925428403 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t V m s s' B
  have hN : gridD * 57659378213923247022943807288922106850774469860123187323582534451095142400 < powLB 64 82787573056936572435268364813 gridD 2022 * 150529397400362566181440068925428403 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 82787573056936572435268364813 gridD 2022 * 1 := by decide +kernel
  refine ⟨hs', hs, hs0, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 2`, `B = 0.35803`: `λ'' = t λ(B)` with `t = 1 - 2 g B² V`, `g = 3/40`, where
`V = (15 m)²/(5 (3 - 3 m + K A) + 16 B (1 - m))`, `K = 6B`, `m = 1/(3/2 + s')`, `A = K/(1 + s)`,
`s' = 3296161/1000000` `≥ √(K² + 25/4)`, `s = 3689807/1000000` `≤ √(K² + 9)`; with `r = 4046` and `q = (1 - 1/r)/λ''`,
`q^r > 256` and `q^r > P`. -/
theorem combrow2 :
    let B : ℝ := 35803 / 100000
    let s' : ℝ := 3296161 / 1000000
    let s : ℝ := 3689807 / 1000000
    let m : ℝ := 1 / (3 / 2 + s')
    let V : ℝ := (15 * m) ^ 2 / (5 * (3 - 3 * m + 6 * B * (6 * B / (1 + s))) + 16 * B * (1 - m))
    let t : ℝ := 1 - 2 * (3 / 40) * B ^ 2 * V
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (4046 : ℝ)) / lam
    (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 ∧ s ^ 2 ≤ (6 * B) ^ 2 + 9 ∧ 0 ≤ s ∧ 1 < q ∧ lam * q < 1 ∧
      (256 : ℝ) < q ^ 4046 ∧
      768 * B * lam * (1 + q) * 4046 * (8096 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 2 < q ^ 4046 := by
  intro B s' s m V t lam q
  have hs' : (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 := by simp only [s', B]; norm_num
  have hs : s ^ 2 ≤ (6 * B) ^ 2 + 9 := by simp only [s, B]; norm_num
  have hs0 : 0 ≤ s := by simp only [s]; norm_num
  have hq : q = 68235289944621837638050663700082439895 / 66649475323338133781686193806851836974 := by
    simp only [q, lam, t, V, m, s, s', B]; norm_num
  have hl : lam = 16472930134290196189245228325964369 / 16869045721785373952546517601998131 := by
    simp only [lam, t, V, m, s, s', B]; norm_num
  have ha : ((81113266304249718594880163147 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 4046 * (8096 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 2 =
      ((3382182412336884715095548466968370212822187168983227182740408187125917286400 : ℕ) : ℝ) / ((16869045721785373952546517601998131 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t V m s s' B
  have hN : gridD * 3382182412336884715095548466968370212822187168983227182740408187125917286400 < powLB 64 81113266304249718594880163147 gridD 4046 * 16869045721785373952546517601998131 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 81113266304249718594880163147 gridD 4046 * 1 := by decide +kernel
  refine ⟨hs', hs, hs0, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 3`, `B = 0.36019`: `λ'' = t λ(B)` with `t = 1 - 2 g B² V`, `g = 3/40`, where
`V = (15 m)²/(5 (3 - 3 m + K A) + 16 B (1 - m))`, `K = 6B`, `m = 1/(3/2 + s')`, `A = K/(1 + s)`,
`s' = 1652311/500000` `≥ √(K² + 25/4)`, `s = 3697367/1000000` `≤ √(K² + 9)`; with `r = 8094` and `q = (1 - 1/r)/λ''`,
`q^r > 256` and `q^r > P`. -/
theorem combrow3 :
    let B : ℝ := 36019 / 100000
    let s' : ℝ := 1652311 / 500000
    let s : ℝ := 3697367 / 1000000
    let m : ℝ := 1 / (3 / 2 + s')
    let V : ℝ := (15 * m) ^ 2 / (5 * (3 - 3 * m + 6 * B * (6 * B / (1 + s))) + 16 * B * (1 - m))
    let t : ℝ := 1 - 2 * (3 / 40) * B ^ 2 * V
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (8094 : ℝ)) / lam
    (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 ∧ s ^ 2 ≤ (6 * B) ^ 2 + 9 ∧ 0 ≤ s ∧ 1 < q ∧ lam * q < 1 ∧
      (256 : ℝ) < q ^ 8094 ∧
      768 * B * lam * (1 + q) * 8094 * (16192 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 3 < q ^ 8094 := by
  intro B s' s m V t lam q
  have hs' : (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 := by simp only [s', B]; norm_num
  have hs : s ^ 2 ≤ (6 * B) ^ 2 + 9 := by simp only [s, B]; norm_num
  have hs0 : 0 ≤ s := by simp only [s]; norm_num
  have hq : q = 6565437504185066721837963007422614977 / 6483618015512402179011212975760238284 := by
    simp only [q, lam, t, V, m, s, s', B]; norm_num
  have hl : lam = 801040031568124805906994437331386 / 811248919335854037049050167727989 := by
    simp only [lam, t, V, m, s, s', B]; norm_num
  have ha : ((80227975848406227194701340989 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 8094 * (16192 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 3 =
      ((84268527145540756300677964781456163318148937657257204373288774575210679500800 : ℕ) : ℝ) / ((811248919335854037049050167727989 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t V m s s' B
  have hN : gridD * 84268527145540756300677964781456163318148937657257204373288774575210679500800 < powLB 64 80227975848406227194701340989 gridD 8094 * 811248919335854037049050167727989 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 80227975848406227194701340989 gridD 8094 * 1 := by decide +kernel
  refine ⟨hs', hs, hs0, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 4`, `B = 0.36134`: `λ'' = t λ(B)` with `t = 1 - 2 g B² V`, `g = 3/40`, where
`V = (15 m)²/(5 (3 - 3 m + K A) + 16 B (1 - m))`, `K = 6B`, `m = 1/(3/2 + s')`, `A = K/(1 + s)`,
`s' = 3309139/1000000` `≥ √(K² + 25/4)`, `s = 925351/250000` `≤ √(K² + 9)`; with `r = 16190` and `q = (1 - 1/r)/λ''`,
`q^r > 256` and `q^r > P`. -/
theorem combrow4 :
    let B : ℝ := 36134 / 100000
    let s' : ℝ := 3309139 / 1000000
    let s : ℝ := 925351 / 250000
    let m : ℝ := 1 / (3 / 2 + s')
    let V : ℝ := (15 * m) ^ 2 / (5 * (3 - 3 * m + 6 * B * (6 * B / (1 + s))) + 16 * B * (1 - m))
    let t : ℝ := 1 - 2 * (3 / 40) * B ^ 2 * V
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (16190 : ℝ)) / lam
    (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 ∧ s ^ 2 ≤ (6 * B) ^ 2 + 9 ∧ 0 ≤ s ∧ 1 < q ∧ lam * q < 1 ∧
      (256 : ℝ) < q ^ 16190 ∧
      768 * B * lam * (1 + q) * 16190 * (32384 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 4 < q ^ 16190 := by
  intro B s' s m V t lam q
  have hs' : (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 := by simp only [s', B]; norm_num
  have hs : s ^ 2 ≤ (6 * B) ^ 2 + 9 := by simp only [s, B]; norm_num
  have hs0 : 0 ≤ s := by simp only [s]; norm_num
  have hq : q = 464068874551864974707676717372506020387 / 460971351474779224735633781862970099230 := by
    simp only [q, lam, t, V, m, s, s', B]; norm_num
  have hl : lam = 28472597373364992262855699929769617 / 28665691182399467212778844732380383 := by
    simp only [lam, t, V, m, s, s', B]; norm_num
  have ha : ((79760540634852295496237490923 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 16190 * (32384 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 4 =
      ((2900117709914554264954398941675399650101661233509310365945975271119913379430400 : ℕ) : ℝ) / ((54188452140641714957994035410927 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t V m s s' B
  have hN : gridD * 2900117709914554264954398941675399650101661233509310365945975271119913379430400 < powLB 64 79760540634852295496237490923 gridD 16190 * 54188452140641714957994035410927 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79760540634852295496237490923 gridD 16190 * 1 := by decide +kernel
  refine ⟨hs', hs, hs0, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 5`, `B = 0.36196`: `λ'' = t λ(B)` with `t = 1 - 2 g B² V`, `g = 3/40`, where
`V = (15 m)²/(5 (3 - 3 m + K A) + 16 B (1 - m))`, `K = 6B`, `m = 1/(3/2 + s')`, `A = K/(1 + s)`,
`s' = 3311577/1000000` `≥ √(K² + 25/4)`, `s = 115737/31250` `≤ √(K² + 9)`; with `r = 32382` and `q = (1 - 1/r)/λ''`,
`q^r > 256` and `q^r > P`. -/
theorem combrow5 :
    let B : ℝ := 36196 / 100000
    let s' : ℝ := 3311577 / 1000000
    let s : ℝ := 115737 / 31250
    let m : ℝ := 1 / (3 / 2 + s')
    let V : ℝ := (15 * m) ^ 2 / (5 * (3 - 3 * m + 6 * B * (6 * B / (1 + s))) + 16 * B * (1 - m))
    let t : ℝ := 1 - 2 * (3 / 40) * B ^ 2 * V
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (32382 : ℝ)) / lam
    (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 ∧ s ^ 2 ≤ (6 * B) ^ 2 + 9 ∧ 0 ≤ s ∧ 1 < q ∧ lam * q < 1 ∧
      (256 : ℝ) < q ^ 32382 ∧
      768 * B * lam * (1 + q) * 32382 * (64768 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 5 < q ^ 32382 := by
  intro B s' s m V t lam q
  have hs' : (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 := by simp only [s', B]; norm_num
  have hs : s ^ 2 ≤ (6 * B) ^ 2 + 9 := by simp only [s, B]; norm_num
  have hs0 : 0 ≤ s := by simp only [s]; norm_num
  have hq : q = 19363132893799643465353790453585457961 / 19294607186031115920671436248944404858 := by
    simp only [q, lam, t, V, m, s, s', B]; norm_num
  have hl : lam = 595843591687700448417992596162819 / 597978224693482087191680011537181 := by
    simp only [lam, t, V, m, s, s', B]; norm_num
  have ha : ((79509545071532489020316205243 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 32382 * (64768 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 5 =
      ((714831708997810568560612727918318723427401199532545707378489322505673723451801600 : ℕ) : ℝ) / ((25999053247542699443116522240747 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t V m s s' B
  have hN : gridD * 714831708997810568560612727918318723427401199532545707378489322505673723451801600 < powLB 64 79509545071532489020316205243 gridD 32382 * 25999053247542699443116522240747 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79509545071532489020316205243 gridD 32382 * 1 := by decide +kernel
  refine ⟨hs', hs, hs0, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 6`, `B = 0.36229`: `λ'' = t λ(B)` with `t = 1 - 2 g B² V`, `g = 3/40`, where
`V = (15 m)²/(5 (3 - 3 m + K A) + 16 B (1 - m))`, `K = 6B`, `m = 1/(3/2 + s')`, `A = K/(1 + s)`,
`s' = 828219/250000` `≥ √(K² + 25/4)`, `s = 1852373/500000` `≤ √(K² + 9)`; with `r = 64766` and `q = (1 - 1/r)/λ''`,
`q^r > 256` and `q^r > P`. -/
theorem combrow6 :
    let B : ℝ := 36229 / 100000
    let s' : ℝ := 828219 / 250000
    let s : ℝ := 1852373 / 500000
    let m : ℝ := 1 / (3 / 2 + s')
    let V : ℝ := (15 * m) ^ 2 / (5 * (3 - 3 * m + 6 * B * (6 * B / (1 + s))) + 16 * B * (1 - m))
    let t : ℝ := 1 - 2 * (3 / 40) * B ^ 2 * V
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (64766 : ℝ)) / lam
    (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 ∧ s ^ 2 ≤ (6 * B) ^ 2 + 9 ∧ 0 ≤ s ∧ 1 < q ∧ lam * q < 1 ∧
      (256 : ℝ) < q ^ 64766 ∧
      768 * B * lam * (1 + q) * 64766 * (129536 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 6 < q ^ 64766 := by
  intro B s' s m V t lam q
  have hs' : (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 := by simp only [s', B]; norm_num
  have hs : s ^ 2 ≤ (6 * B) ^ 2 + 9 := by simp only [s, B]; norm_num
  have hs0 : 0 ≤ s := by simp only [s]; norm_num
  have hq : q = 206692399220011064812247025514652737095 / 206306878614198408844865193491689080757 := by
    simp only [q, lam, t, V, m, s, s', B]; norm_num
  have hl : lam = 6370838977679597592714238751557579 / 6382842560642663933057886991883046 := by
    simp only [lam, t, V, m, s, s', B]; norm_num
  have ha : ((79376214239030341826485151998 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 64766 * (129536 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 6 =
      ((15002338259636097020387937479054620960196821194999687632693547394393538299419636531200 : ℕ) : ℝ) / ((1063807093440443988842981165313841 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t V m s s' B
  have hN : gridD * 15002338259636097020387937479054620960196821194999687632693547394393538299419636531200 < powLB 64 79376214239030341826485151998 gridD 64766 * 1063807093440443988842981165313841 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79376214239030341826485151998 gridD 64766 * 1 := by decide +kernel
  refine ⟨hs', hs, hs0, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 7`, `B = 0.36246`: `λ'' = t λ(B)` with `t = 1 - 2 g B² V`, `g = 3/40`, where
`V = (15 m)²/(5 (3 - 3 m + K A) + 16 B (1 - m))`, `K = 6B`, `m = 1/(3/2 + s')`, `A = K/(1 + s)`,
`s' = 1656773/500000` `≥ √(K² + 25/4)`, `s = 57896/15625` `≤ √(K² + 9)`; with `r = 129534` and `q = (1 - 1/r)/λ''`,
`q^r > 256` and `q^r > P`. -/
theorem combrow7 :
    let B : ℝ := 36246 / 100000
    let s' : ℝ := 1656773 / 500000
    let s : ℝ := 57896 / 15625
    let m : ℝ := 1 / (3 / 2 + s')
    let V : ℝ := (15 * m) ^ 2 / (5 * (3 - 3 * m + 6 * B * (6 * B / (1 + s))) + 16 * B * (1 - m))
    let t : ℝ := 1 - 2 * (3 / 40) * B ^ 2 * V
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (129534 : ℝ)) / lam
    (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 ∧ s ^ 2 ≤ (6 * B) ^ 2 + 9 ∧ 0 ≤ s ∧ 1 < q ∧ lam * q < 1 ∧
      (256 : ℝ) < q ^ 129534 ∧
      768 * B * lam * (1 + q) * 129534 * (259072 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 7 < q ^ 129534 := by
  intro B s' s m V t lam q
  have hs' : (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 := by simp only [s', B]; norm_num
  have hs : s ^ 2 ≤ (6 * B) ^ 2 + 9 := by simp only [s, B]; norm_num
  have hs0 : 0 ≤ s := by simp only [s]; norm_num
  have hq : q = 4923112783440332560773261831889639351 / 4918181443641795262963046957452154502 := by
    simp only [q, lam, t, V, m, s, s', B]; norm_num
  have hl : lam = 37968266583613532068515192593853 / 38006629842899744163828999806147 := by
    simp only [lam, t, V, m, s, s', B]; norm_num
  have ha : ((79307602647868328398455216070 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 129534 * (259072 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 7 =
      ((274679872219454142809873378663348305321085218840397108793386143561496089287026383257600 : ℕ) : ℝ) / ((38006629842899744163828999806147 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t V m s s' B
  have hN : gridD * 274679872219454142809873378663348305321085218840397108793386143561496089287026383257600 < powLB 64 79307602647868328398455216070 gridD 129534 * 38006629842899744163828999806147 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79307602647868328398455216070 gridD 129534 * 1 := by decide +kernel
  refine ⟨hs', hs, hs0, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 8`, `B = 0.36255`: `λ'' = t λ(B)` with `t = 1 - 2 g B² V`, `g = 3/40`, where
`V = (15 m)²/(5 (3 - 3 m + K A) + 16 B (1 - m))`, `K = 6B`, `m = 1/(3/2 + s')`, `A = K/(1 + s)`,
`s' = 33139/10000` `≥ √(K² + 25/4)`, `s = 3705661/1000000` `≤ √(K² + 9)`; with `r = 259070` and `q = (1 - 1/r)/λ''`,
`q^r > 256` and `q^r > P`. -/
theorem combrow8 :
    let B : ℝ := 36255 / 100000
    let s' : ℝ := 33139 / 10000
    let s : ℝ := 3705661 / 1000000
    let m : ℝ := 1 / (3 / 2 + s')
    let V : ℝ := (15 * m) ^ 2 / (5 * (3 - 3 * m + 6 * B * (6 * B / (1 + s))) + 16 * B * (1 - m))
    let t : ℝ := 1 - 2 * (3 / 40) * B ^ 2 * V
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (259070 : ℝ)) / lam
    (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 ∧ s ^ 2 ≤ (6 * B) ^ 2 + 9 ∧ 0 ≤ s ∧ 1 < q ∧ lam * q < 1 ∧
      (256 : ℝ) < q ^ 259070 ∧
      768 * B * lam * (1 + q) * 259070 * (518144 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 8 < q ^ 259070 := by
  intro B s' s m V t lam q
  have hs' : (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 := by simp only [s', B]; norm_num
  have hs : s ^ 2 ≤ (6 * B) ^ 2 + 9 := by simp only [s, B]; norm_num
  have hs0 : 0 ≤ s := by simp only [s]; norm_num
  have hq : q = 17092453045693680192284990352694 / 17083154634118727672857546810305 := by
    simp only [q, lam, t, V, m, s, s', B]; norm_num
  have hl : lam = 54466691348987026895357755299 / 54496548084653045477565444076 := by
    simp only [lam, t, V, m, s, s', B]; norm_num
  have ha : ((79271286637364734671761430741 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 259070 * (518144 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 8 =
      ((13620874725800824901770404869180457176622850850990512882346106975577364037107712000 : ℕ) : ℝ) / ((3679216046762965533186973 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t V m s s' B
  have hN : gridD * 13620874725800824901770404869180457176622850850990512882346106975577364037107712000 < powLB 64 79271286637364734671761430741 gridD 259070 * 3679216046762965533186973 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79271286637364734671761430741 gridD 259070 * 1 := by decide +kernel
  refine ⟨hs', hs, hs0, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 9`, `B = 0.3626`: `λ'' = t λ(B)` with `t = 1 - 2 g B² V`, `g = 3/40`, where
`V = (15 m)²/(5 (3 - 3 m + K A) + 16 B (1 - m))`, `K = 6B`, `m = 1/(3/2 + s')`, `A = K/(1 + s)`,
`s' = 3314097/1000000` `≥ √(K² + 25/4)`, `s = 1852919/500000` `≤ √(K² + 9)`; with `r = 518142` and `q = (1 - 1/r)/λ''`,
`q^r > 256` and `q^r > P`. -/
theorem combrow9 :
    let B : ℝ := 3626 / 10000
    let s' : ℝ := 3314097 / 1000000
    let s : ℝ := 1852919 / 500000
    let m : ℝ := 1 / (3 / 2 + s')
    let V : ℝ := (15 * m) ^ 2 / (5 * (3 - 3 * m + 6 * B * (6 * B / (1 + s))) + 16 * B * (1 - m))
    let t : ℝ := 1 - 2 * (3 / 40) * B ^ 2 * V
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (518142 : ℝ)) / lam
    (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 ∧ s ^ 2 ≤ (6 * B) ^ 2 + 9 ∧ 0 ≤ s ∧ 1 < q ∧ lam * q < 1 ∧
      (256 : ℝ) < q ^ 518142 ∧
      768 * B * lam * (1 + q) * 518142 * (1036288 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 9 < q ^ 518142 := by
  intro B s' s m V t lam q
  have hs' : (6 * B) ^ 2 + 25 / 4 ≤ s' ^ 2 := by simp only [s', B]; norm_num
  have hs : s ^ 2 ≤ (6 * B) ^ 2 + 9 := by simp only [s, B]; norm_num
  have hs0 : 0 ≤ s := by simp only [s]; norm_num
  have hq : q = 2127444243264962317959489409252313413 / 2126828457322546480207592494964782194 := by
    simp only [q, lam, t, V, m, s, s', B]; norm_num
  have hl : lam = 4104721210252298559482907185607 / 4105917584721074607026831324393 := by
    simp only [lam, t, V, m, s, s', B]; norm_num
  have ha : ((79251101641560546457360405964 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 518142 * (1036288 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 9 =
      ((7784802332653031516567490834470688084542974075126253869367604919851654668769096634466304000 : ℕ) : ℝ) / ((4105917584721074607026831324393 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t V m s s' B
  have hN : gridD * 7784802332653031516567490834470688084542974075126253869367604919851654668769096634466304000 < powLB 64 79251101641560546457360405964 gridD 518142 * 4105917584721074607026831324393 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79251101641560546457360405964 gridD 518142 * 1 := by decide +kernel
  refine ⟨hs', hs, hs0, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

end YangMills.CombinedFlow
