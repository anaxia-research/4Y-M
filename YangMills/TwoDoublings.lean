import Mathlib
import YangMills.OrbitBound

/-!
# Two doublings suffice, a lattice gap beyond one third, spectral criteria

* `two_doublings`, `datum_at_four`: from `X(S) ≤ 2 · 10⁻⁴`, two fixed-coupling doublings
  give `X(4S) < 1.2 · 10⁻⁴`, and `ψ ≤ 2X` gives the one-cube datum `ψ < 1/4097`
  (Proposition `ly:prop:twodoublings`), so the gap constant improves from `16τ` to `4τ`
  (Corollary `ly:cor:orbit`).
* `tail_below_threshold`: the row `J = 0` bound `10⁻⁷` lies below `1/8192`
  (Corollary `ly:cor:latticegap`).
* `vanish_of_exp`, `vanish_of_geom`, `gamma_moment`: the limit steps and the Gamma
  integral behind the spectral criteria (Proposition `ly:prop:spectralcrit`).
-/

namespace YangMills.TwoDoublings

open YangMills.OrbitBound

/-- **Two doublings.** If `0 ≤ X k`, `X (k+1) ≤ (e^{64 X k} - 1)^2` and
`X 0 ≤ 200 · 10⁻⁶`, then `X 2 < 120 · 10⁻⁶`. -/
theorem two_doublings (X : ℕ → ℝ) (h0 : ∀ k, 0 ≤ X k)
    (hs : ∀ k, X (k + 1) ≤ (Real.exp (64 * X k) - 1) ^ 2) (hX : X 0 ≤ 200 / 10 ^ 6) :
    X 2 < 120 / 10 ^ 6 := by
  have a1 : X 1 ≤ 169 / 10 ^ 6 :=
    (hs 0).trans ((doubling_step _ _ (h0 0) hX (by norm_num)).trans (by norm_num))
  have a2 := (hs 1).trans (doubling_step _ _ (h0 1) a1 (by norm_num))
  have : (64 * (169 / 10 ^ 6 : ℝ) / (1 - 64 * (169 / 10 ^ 6))) ^ 2 < 120 / 10 ^ 6 := by
    norm_num
  linarith

/-- **The datum at four times the box.** `ψ ≤ 2X` and `X < 120 · 10⁻⁶` give
`ψ < 240 · 10⁻⁶ < 1/4097`. -/
theorem datum_at_four (ψ X : ℝ) (hψ : ψ ≤ 2 * X) (hX : X < 120 / 10 ^ 6) :
    ψ < 1 / 4097 := by
  have : (240 / 10 ^ 6 : ℝ) < 1 / 4097 := by norm_num
  linarith

/-- The orbit bound reaches `2 · 10⁻⁴` at the top: `3.36 · 10⁻⁵ + 1.664 · 10⁻⁴`. -/
theorem top_value : (336 / 10 ^ 7 : ℝ) + 1664 / 10 ^ 7 = 200 / 10 ^ 6 := by norm_num

/-- The gap constant improves by a factor of four. -/
theorem constant_improves (τ : ℝ) (hτ : 0 < τ) :
    Real.log (63 / 32) / (16 * τ) < Real.log (63 / 32) / (4 * τ) := by
  have hl : 0 < Real.log (63 / 32) := Real.log_pos (by norm_num)
  exact div_lt_div_of_pos_left hl (by positivity) (by linarith)

/-- The certified tail `10⁻⁷` lies below the ascent threshold `1/8192`. -/
theorem tail_below_threshold : (1 / 10 ^ 7 : ℝ) < 1 / 8192 := by norm_num

/-- **The exponential criterion, limit step.** If `0 ≤ x ≤ C e^{-(m-a)t}` for all `t ≥ 1`
with `a < m`, then `x = 0`. -/
theorem vanish_of_exp (x C m a : ℝ) (hx : 0 ≤ x) (ham : a < m)
    (h : ∀ t : ℝ, 1 ≤ t → x ≤ C * Real.exp (-(m - a) * t)) : x = 0 := by
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  have hlim : Filter.Tendsto (fun t : ℝ => C * Real.exp (-(m - a) * t)) Filter.atTop
      (nhds (C * 0)) := by
    apply Filter.Tendsto.const_mul
    have : Filter.Tendsto (fun t : ℝ => -(m - a) * t) Filter.atTop Filter.atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg (by linarith) Filter.tendsto_id
    exact Real.tendsto_exp_atBot.comp this
  rw [mul_zero] at hlim
  have hev := (hlim.eventually (gt_mem_nhds hpos))
  obtain ⟨t, ht⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  linarith [h t ht.2]

/-- **The inverse-moment criterion, limit step.** If `0 ≤ x ≤ A r^k` for every `k` with
`0 ≤ r < 1`, then `x = 0`. -/
theorem vanish_of_geom (x A r : ℝ) (hx : 0 ≤ x) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ k : ℕ, x ≤ A * r ^ k) : x = 0 := by
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  have hlim : Filter.Tendsto (fun k : ℕ => A * r ^ k) Filter.atTop (nhds (A * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul A
  rw [mul_zero] at hlim
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists
  linarith [h k]

/-- **The Gamma integral.** `∫₀^∞ t^{k-1} e^{-tE} dt = (k-1)! E^{-k}` for `E > 0`, `k ≥ 1`. -/
theorem gamma_moment (E : ℝ) (hE : 0 < E) (k : ℕ) (hk : 1 ≤ k) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ ((k : ℝ) - 1) * Real.exp (-(E * t)) =
      (k - 1).factorial * (1 / E) ^ (k : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ)) (r := E)
    (by exact_mod_cast hk) hE
  rw [h]
  have : Real.Gamma (k : ℝ) = (k - 1).factorial := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
    simp
  rw [this]; ring

end YangMills.TwoDoublings
