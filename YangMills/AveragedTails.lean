import Mathlib
import YangMills.OrbitBound

/-!
# Certified tails past the star threshold

Columns of Proposition `ly:prop:Rtails` beyond `β_⋆ = (√37 - 5)/3`, from the averaged star
response of Proposition `prop:avgsource`: the contraction `λ(B)` of Lemma `lem:sclosed` is
replaced by `λ' = t λ(B)`, where `t = 1 - 4 e₀ B² (7 - s)/(1 + s)²`, `e₀ = 193/10000`, and the
rational `s` dominates `√(36 B² + 9)`, so that `t` dominates the factor `θ` of the proposition
(`(7 - s)/(1 + s)²` decreases in `s`). The analytic inputs of `θ` (the harmonic-extension bound
and the enclosure of the zonal gain) are not formalised here. Exact integer arithmetic of
`OrbitBound` (downward rounding on the grid `2^{-96} Z`).

* `avgrow7`, `avgrow8`, `avgrow9`, `avgrow10`, `avgrow12`: `B = 0.361, 0.3611, 0.36115, 0.36118,
  0.3612`.
-/

namespace YangMills.AveragedTails

open YangMills.OrbitBound

/-- Averaged row `J = 7`, `B = 0.361`: `λ' = t λ(B)` with `t = 1 - 4 e₀ B² (7 - s)/(1 + s)²`,
`s = 3700211/1000000` `≥ √(36 B² + 9)`; with `r = 129534` and `q = (1 - 1/r)/λ'`, `q^r > 256` and `q^r > P`. -/
theorem avgrow7 :
    let B : ℝ := 361 / 1000
    let s : ℝ := 3700211 / 1000000
    let t : ℝ := 1 - 4 * (193 / 10000) * B ^ 2 * ((7 - s) / (1 + s) ^ 2)
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (129534 : ℝ)) / lam
    36 * B ^ 2 + 9 ≤ s ^ 2 ∧ 1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 129534 ∧
      768 * B * lam * (1 + q) * 129534 * (259072 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 7 < q ^ 129534 := by
  intro B s t lam q
  have hs : 36 * B ^ 2 + 9 ≤ s ^ 2 := by simp only [s, B]; norm_num
  have hq : q = 1876376740218727774692311250 / 1874335846704654233106384227 := by
    simp only [q, lam, t, s, B]; norm_num
  have hl : lam = 86819021108187235773143 / 86914226037475906897500 := by
    simp only [lam, t, s, B]; norm_num
  have ha : ((79314431068158567006959339995 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 129534 * (259072 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 7 =
      ((52559180176875481127671065727313437119515655834336328707284410245840896 : ℕ) : ℝ) / ((7302182401804319 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t s B
  have hN : gridD * 52559180176875481127671065727313437119515655834336328707284410245840896 < powLB 64 79314431068158567006959339995 gridD 129534 * 7302182401804319 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79314431068158567006959339995 gridD 129534 * 1 := by decide +kernel
  refine ⟨hs, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Averaged row `J = 8`, `B = 0.3611`: `λ' = t λ(B)` with `t = 1 - 4 e₀ B² (7 - s)/(1 + s)²`,
`s = 1850281/500000` `≥ √(36 B² + 9)`; with `r = 259070` and `q = (1 - 1/r)/λ'`, `q^r > 256` and `q^r > P`. -/
theorem avgrow8 :
    let B : ℝ := 3611 / 10000
    let s : ℝ := 1850281 / 500000
    let t : ℝ := 1 - 4 * (193 / 10000) * B ^ 2 * ((7 - s) / (1 + s) ^ 2)
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (259070 : ℝ)) / lam
    36 * B ^ 2 + 9 ≤ s ^ 2 ∧ 1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 259070 ∧
      768 * B * lam * (1 + q) * 259070 * (518144 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 8 < q ^ 259070 := by
  intro B s t lam q
  have hs : 36 * B ^ 2 + 9 ≤ s ^ 2 := by simp only [s, B]; norm_num
  have hq : q = 3752549207954895213192046850000 / 3750383430328073598750208682857 := by
    simp only [q, lam, t, s, B]; norm_num
  have hl : lam = 144763323824760628353348851 / 144847481094028819086500000 := by
    simp only [lam, t, s, B]; norm_num
  have ha : ((79273915324603671436428081266 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 259070 * (518144 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 8 =
      ((26704413233489888171047721659386926744850787590638466675100636661783867594637312 : ℕ) : ℝ) / ((7242374054701440954325 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t s B
  have hN : gridD * 26704413233489888171047721659386926744850787590638466675100636661783867594637312 < powLB 64 79273915324603671436428081266 gridD 259070 * 7242374054701440954325 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79273915324603671436428081266 gridD 259070 * 1 := by decide +kernel
  refine ⟨hs, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Averaged row `J = 9`, `B = 0.36115`: `λ' = t λ(B)` with `t = 1 - 4 e₀ B² (7 - s)/(1 + s)²`,
`s = 1850369/500000` `≥ √(36 B² + 9)`; with `r = 518142` and `q = (1 - 1/r)/λ'`, `q^r > 256` and `q^r > P`. -/
theorem avgrow9 :
    let B : ℝ := 36115 / 100000
    let s : ℝ := 1850369 / 500000
    let t : ℝ := 1 - 4 * (193 / 10000) * B ^ 2 * ((7 - s) / (1 + s) ^ 2)
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (518142 : ℝ)) / lam
    36 * B ^ 2 + 9 ≤ s ^ 2 ∧ 1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 518142 ∧
      768 * B * lam * (1 + q) * 518142 * (1036288 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 9 < q ^ 518142 := by
  intro B s t lam q
  have hs : 36 * B ^ 2 + 9 ≤ s ^ 2 := by simp only [s, B]; norm_num
  have hq : q = 1801174932049962714693873971000000 / 1800595328483810261662351234511487 := by
    simp only [q, lam, t, s, B]; norm_num
  have hl : lam = 6950200248132018873831309697 / 6952450904483384695262000000 := by
    simp only [lam, t, s, B]; norm_num
  have ha : ((79253665704685053271565775315 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 518142 * (1036288 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 9 =
      ((820555772525278764149216706217981365649913062159343166190648277508895586815618056192 : ℕ) : ℝ) / ((434528181530211543453875 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t s B
  have hN : gridD * 820555772525278764149216706217981365649913062159343166190648277508895586815618056192 < powLB 64 79253665704685053271565775315 gridD 518142 * 434528181530211543453875 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79253665704685053271565775315 gridD 518142 * 1 := by decide +kernel
  refine ⟨hs, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Averaged row `J = 10`, `B = 0.36118`: `λ' = t λ(B)` with `t = 1 - 4 e₀ B² (7 - s)/(1 + s)²`,
`s = 3700843/1000000` `≥ √(36 B² + 9)`; with `r = 1036286` and `q = (1 - 1/r)/λ'`, `q^r > 256` and `q^r > P`. -/
theorem avgrow10 :
    let B : ℝ := 36118 / 100000
    let s : ℝ := 3700843 / 1000000
    let t : ℝ := 1 - 4 * (193 / 10000) * B ^ 2 * ((7 - s) / (1 + s) ^ 2)
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (1036286 : ℝ)) / lam
    36 * B ^ 2 + 9 ≤ s ^ 2 ∧ 1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 1036286 ∧
      768 * B * lam * (1 + q) * 1036286 * (2072576 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 10 < q ^ 1036286 := by
  intro B s t lam q
  have hs : 36 * B ^ 2 + 9 ≤ s ^ 2 := by simp only [s, B]; norm_num
  have hq : q = 2786423580072421794153466671875000 / 2785954467260661843117775358869777 := by
    simp only [q, lam, t, s, B]; norm_num
  have hl : lam = 5376806146682791899374835439 / 5377716709346216135818750000 := by
    simp only [lam, t, s, B]; norm_num
  have ha : ((79241503344677903519824350472 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 1036286 * (2072576 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 10 =
      ((13000758798525412235340079545318452234684694590635382070391697390840372183120309781528576 : ℕ) : ℝ) / ((13444291773365540339546875 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t s B
  have hN : gridD * 13000758798525412235340079545318452234684694590635382070391697390840372183120309781528576 < powLB 64 79241503344677903519824350472 gridD 1036286 * 13444291773365540339546875 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79241503344677903519824350472 gridD 1036286 * 1 := by decide +kernel
  refine ⟨hs, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Averaged row `J = 12`, `B = 0.3612`: `λ' = t λ(B)` with `t = 1 - 4 e₀ B² (7 - s)/(1 + s)²`,
`s = 3700913/1000000` `≥ √(36 B² + 9)`; with `r = 4145150` and `q = (1 - 1/r)/λ'`, `q^r > 256` and `q^r > P`. -/
theorem avgrow12 :
    let B : ℝ := 3612 / 10000
    let s : ℝ := 3700913 / 1000000
    let t : ℝ := 1 - 4 * (193 / 10000) * B ^ 2 * ((7 - s) / (1 + s) ^ 2)
    let lam : ℝ := t * (3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2))
    let q : ℝ := (1 - 1 / (4145150 : ℝ)) / lam
    36 * B ^ 2 + 9 ≤ s ^ 2 ∧ 1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 4145150 ∧
      768 * B * lam * (1 + q) * 4145150 * (8290304 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 12 < q ^ 4145150 := by
  intro B s t lam q
  have hs : 36 * B ^ 2 + 9 ≤ s ^ 2 := by simp only [s, B]; norm_num
  have hq : q = 546988624890080165305874375 / 546952450012823642847403356 := by
    simp only [q, lam, t, s, B]; norm_num
  have hl : lam = 3298749442196444295426 / 3298968413982707046875 := by
    simp only [lam, t, s, B]; norm_num
  have ha : ((79233402584135395177071936296 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 4145150 * (8290304 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 12 =
      ((38233845329785394638462170900770041941390515572984742989932650328260381823520720551936 : ℕ) : ℝ) / ((150809984639209465 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam t s B
  have hN : gridD * 38233845329785394638462170900770041941390515572984742989932650328260381823520720551936 < powLB 64 79233402584135395177071936296 gridD 4145150 * 150809984639209465 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79233402584135395177071936296 gridD 4145150 * 1 := by decide +kernel
  refine ⟨hs, by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

end YangMills.AveragedTails
