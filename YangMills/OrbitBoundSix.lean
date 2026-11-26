import Mathlib
import YangMills.OrbitBound
import YangMills.TwoDoublings

/-!
# Longer certified tails and a larger constant in the orbit bound

* `row11`, `row12`, `row13`, `row16`: the columns `J = 11, 12, 13, 16` of Proposition
  `ly:prop:Rtails`, `B = 0.360905, 0.36091, 0.360915, 0.36092`, in the exact integer
  arithmetic of `OrbitBound` (downward rounding on the grid `2^{-96} Z`).
* `six_doublings`, `orbit_datum_six`: Corollary `ly:cor:orbit2`. From `X(S) <= 2336 * 10^-7`,
  six fixed-coupling doublings give `X(64 S) <= 930 * 10^-7`, and `psi <= 2X` gives the
  one-cube datum `psi < 1/4097`; with an orbit rise of at most `2 * 10^-4` and
  `Y 0 <= 3.36 * 10^-5` this holds at the top of every orbit.
-/

namespace YangMills.OrbitBoundSix

open YangMills.OrbitBound

/-- Row `J = 11`, `B = 0.360905`: with `r = 2072574` and `q = (1 - 1/r)/λ(B)`, `q^r > 256` and `q^r > P`. -/
theorem row11 :
    let B : ℝ := 360905 / 1000000
    let lam : ℝ := 3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2)
    let q : ℝ := (1 - 1 / (2072574 : ℝ)) / lam
    1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 2072574 ∧
      768 * B * lam * (1 + q) * 2072574 * (4145152 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 11 < q ^ 2072574 := by
  intro B lam q
  have hq : q = 391467815636491841 / 391436046598598442 := by
    simp only [q, lam, B]; norm_num
  have hl : lam = 188864690283 / 188880109717 := by
    simp only [lam, B]; norm_num
  have ha : ((79234592689816670208469910018 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 2072574 * (4145152 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 11 =
      ((93449230597157547691837368660720583716537512472422707936961861283753020620800 : ℕ) : ℝ) / ((188880109717 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam B
  have hN : gridD * 93449230597157547691837368660720583716537512472422707936961861283753020620800 < powLB 64 79234592689816670208469910018 gridD 2072574 * 188880109717 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79234592689816670208469910018 gridD 2072574 * 1 := by decide +kernel
  refine ⟨by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 12`, `B = 0.36091`: with `r = 4145150` and `q = (1 - 1/r)/λ(B)`, `q^r > 256` and `q^r > P`. -/
theorem row12 :
    let B : ℝ := 36091 / 100000
    let lam : ℝ := 3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2)
    let q : ℝ := (1 - 1 / (4145150 : ℝ)) / lam
    1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 4145150 ∧
      768 * B * lam * (1 + q) * 4145150 * (8290304 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 12 < q ^ 4145150 := by
  intro B lam q
  have hq : q = 65243980871373131 / 65240351208787150 := by
    simp only [q, lam, B]; norm_num
  have hl : lam = 15738960281 / 15739839719 := by
    simp only [lam, B]; norm_num
  have ha : ((79232570392086971309512978302 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 4145150 * (8290304 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 12 =
      ((3987233259655067426191696357612752204669477745659915720698756573490429768499200 : ℕ) : ℝ) / ((15739839719 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam B
  have hN : gridD * 3987233259655067426191696357612752204669477745659915720698756573490429768499200 < powLB 64 79232570392086971309512978302 gridD 4145150 * 15739839719 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79232570392086971309512978302 gridD 4145150 * 1 := by decide +kernel
  refine ⟨by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 13`, `B = 0.360915`: with `r = 8290302` and `q = (1 - 1/r)/λ(B)`, `q^r > 256` and `q^r > P`. -/
theorem row13 :
    let B : ℝ := 360915 / 1000000
    let lam : ℝ := 3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2)
    let q : ℝ := (1 - 1 / (8290302 : ℝ)) / lam
    1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 8290302 ∧
      768 * B * lam * (1 + q) * 8290302 * (16580608 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 13 < q ^ 8290302 := by
  intro B lam q
  have hq : q = 1565839252577673433 / 1565792293959083034 := by
    simp only [q, lam, B]; norm_num
  have hl : lam = 188870356467 / 188876043533 := by
    simp only [lam, B]; norm_num
  have ha : ((79230538592547184672375371646 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 8290302 * (16580608 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 13 =
      ((24497959803255460836986204420934962917503075149738479157732568440891197527529881600 : ℕ) : ℝ) / ((188876043533 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam B
  have hN : gridD * 24497959803255460836986204420934962917503075149738479157732568440891197527529881600 < powLB 64 79230538592547184672375371646 gridD 8290302 * 188876043533 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79230538592547184672375371646 gridD 8290302 * 1 := by decide +kernel
  refine ⟨by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- Row `J = 16`, `B = 0.36092`: with `r = 66322430` and `q = (1 - 1/r)/λ(B)`, `q^r > 256` and `q^r > P`. -/
theorem row16 :
    let B : ℝ := 36092 / 100000
    let lam : ℝ := 3 * B * (4 + B) / (8 - 8 * B - 3 * B ^ 2)
    let q : ℝ := (1 - 1 / (66322430 : ℝ)) / lam
    1 < q ∧ lam * q < 1 ∧ (256 : ℝ) < q ^ 66322430 ∧
      768 * B * lam * (1 + q) * 66322430 * (132644864 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 16 < q ^ 66322430 := by
  intro B lam q
  have hq : q = 195727861669087177 / 195727013968756410 := by
    simp only [q, lam, B]; norm_num
  have hl : lam = 2951143587 / 2951156413 := by
    simp only [lam, B]; norm_num
  have ha : ((79228505654121261607264080516 : ℕ) : ℝ) ≤ (gridD : ℝ) * q := by rw [hq]; unfold gridD; norm_num
  have hq1 : 1 ≤ q := by rw [hq]; norm_num
  have hP : 768 * B * lam * (1 + q) * 66322430 * (132644864 : ℝ) ^ 7 * 10 ^ 7 * 2 ^ 16 =
      ((51376779506207410220947587560863646795072539100063436751454165347519197138078575414476800 : ℕ) : ℝ) / ((2951156413 : ℕ) : ℝ) := by
    rw [hq, hl]; simp only [B]; norm_num
  clear_value q lam B
  have hN : gridD * 51376779506207410220947587560863646795072539100063436751454165347519197138078575414476800 < powLB 64 79228505654121261607264080516 gridD 66322430 * 2951156413 := by decide +kernel
  have h256 : gridD * 256 < powLB 64 79228505654121261607264080516 gridD 66322430 * 1 := by decide +kernel
  refine ⟨by rw [hq]; norm_num, by rw [hq, hl]; norm_num, ?_, ?_⟩
  · have := pow_gt_of_cert (Pn := 256) (Pd := 1) hq1 ha (by norm_num) h256
    simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using this
  · rw [hP]
    exact pow_gt_of_cert hq1 ha (by norm_num) hN

/-- **Six doublings.** If `0 ≤ X k`, `X (k+1) ≤ (e^{64 X k} - 1)^2` and
`X 0 ≤ 2336 · 10⁻⁷`, then `X 6 ≤ 930 · 10⁻⁷`. -/
theorem six_doublings (X : ℕ → ℝ) (h0 : ∀ k, 0 ≤ X k)
    (hs : ∀ k, X (k + 1) ≤ (Real.exp (64 * X k) - 1) ^ 2) (hX : X 0 ≤ 2336 / 10 ^ 7) :
    X 6 ≤ 930 / 10 ^ 7 := by
  have step : ∀ k (c d : ℝ), X k ≤ c → 64 * c < 1 → (64 * c / (1 - 64 * c)) ^ 2 ≤ d →
      X (k + 1) ≤ d := fun k c d hk hc hd =>
    (hs k).trans ((doubling_step _ _ (h0 k) hk hc).trans hd)
  have a1 := step 0 _ (2304 / 10 ^ 7) hX (by norm_num) (by norm_num)
  have a2 := step 1 _ (2240 / 10 ^ 7) a1 (by norm_num) (by norm_num)
  have a3 := step 2 _ (2116 / 10 ^ 7) a2 (by norm_num) (by norm_num)
  have a4 := step 3 _ (1885 / 10 ^ 7) a3 (by norm_num) (by norm_num)
  have a5 := step 4 _ (1492 / 10 ^ 7) a4 (by norm_num) (by norm_num)
  exact step 5 _ (930 / 10 ^ 7) a5 (by norm_num) (by norm_num)

/-- **Corollary `ly:cor:orbit2`.** Along an orbit `Y` with `Y 0 ≤ 3.36 · 10⁻⁵` and total
rise at most `2 · 10⁻⁴`, six fixed-coupling doublings `X` starting at `X 0 = Y n` give
`X 6 ≤ 930 · 10⁻⁷`, and any `ψ ≤ 2 X 6` satisfies the one-cube datum `ψ < 1/4097`. -/
theorem orbit_datum_six (Y X : ℕ → ℝ) (n : ℕ) (hY0 : Y 0 ≤ 336 / 10 ^ 7)
    (hA : ∑ i ∈ Finset.range n, max (Y (i + 1) - Y i) 0 ≤ 2 / 10 ^ 4)
    (hX0 : X 0 = Y n) (h0 : ∀ k, 0 ≤ X k)
    (hs : ∀ k, X (k + 1) ≤ (Real.exp (64 * X k) - 1) ^ 2) (ψ : ℝ) (hψ : ψ ≤ 2 * X 6) :
    X 6 ≤ 930 / 10 ^ 7 ∧ ψ < 1 / 4097 := by
  have ht := telescope_pos Y n
  have h6 := six_doublings X h0 hs (by rw [hX0]; linarith)
  refine ⟨h6, ?_⟩
  have : (1860 / 10 ^ 7 : ℝ) < 1 / 4097 := by norm_num
  linarith

/-- The bounding map does not contract at `2.37 · 10⁻⁴`: the method stops below it. -/
theorem no_contraction : (1 : ℝ) * (2370 / 10 ^ 7) < (64 * (2370 / 10 ^ 7) / (1 - 64 * (2370 / 10 ^ 7))) ^ 2 := by
  norm_num

end YangMills.OrbitBoundSix
