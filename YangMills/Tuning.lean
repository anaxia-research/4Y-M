import Mathlib

/-!
# The rung count and the two-loop tuning (Lemma `ly:lem:rungs`)

The one-box reduction needs the tuning only through the rung count
`2^{n_D(β_N)} ≤ 2^K N`. This file proves the rung count for the reference map
of a scale function `ℓ`, and that the two-loop scale function
`ℓ(β) = β/c₁ - γ log (1 + β/β₁)` is a scale function.

* `side_of_rungs`: the rung count bounds the side, `T_* 2^n ≤ (2^K T_*) N`.
* `scale_step`: if `ℓ (ρ b) = ℓ b - log 2` and `ℓ` has slope at most `1/c₁`,
  then `ρ` lowers the coupling by at least `c₁ log 2`.
* `scale_iterate`: along the rungs above `a`, `ℓ (ρ^[k] β) = ℓ β - k log 2`.
* `scale_rungs`: if `ℓ β ≤ log N + C`, then `2^n ≤ 2 N e^{C - ℓ a}`.
* `twoloop_lipschitz`, `twoloop_strictMono`: the two-loop scale function has
  slope at most `1/c₁`, and is strictly increasing when `β₁ > c₁ γ`.
* `twoloop_lower`: `ℓ b ≥ b (1/c₁ - γ/β₁)`.
* `su2_twoloop_endpoint`: for `SU(2)`, `c₁ = 11/(3π²)`, `γ = 51/121`, `β₁ = 4`,
  `ℓ b ≥ log 2` for every `b ≥ 161/600` (Corollary `ly:cor:endpoint`(a)).
-/

open Real

namespace YangMills.Tuning

/-- **The side of the large box.** If `2^n ≤ 2^K N`, then
`T_* 2^n ≤ (2^K T_*) N`. -/
theorem side_of_rungs (Tstar K : ℝ) (hT : 0 ≤ Tstar) (n : ℕ) (N : ℝ)
    (h : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ K * N) :
    Tstar * 2 ^ n ≤ ((2 : ℝ) ^ K * Tstar) * N := by
  have := mul_le_mul_of_nonneg_left h hT
  nlinarith [this]

/-- **One rung of a scale function drops by `c₁ log 2`.** If
`ℓ β - ℓ β' ≤ (β - β')/c₁` for `β' ≤ β`, `ℓ` is strictly increasing and
`ℓ (ρ b) = ℓ b - log 2`, then `ρ b ≤ b - c₁ log 2`. -/
theorem scale_step (ℓ : ℝ → ℝ) (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hmono : StrictMono ℓ)
    (hlip : ∀ b b', b' ≤ b → ℓ b - ℓ b' ≤ (b - b') / c₁)
    (b r : ℝ) (hr : ℓ r = ℓ b - Real.log 2) :
    r ≤ b - c₁ * Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrb : r < b := by
    by_contra h
    rw [not_lt] at h
    have := hmono.monotone h
    linarith
  have h1 := hlip b r hrb.le
  rw [hr] at h1
  have h2 : Real.log 2 ≤ (b - r) / c₁ := by linarith
  rw [le_div_iff₀ hc₁] at h2
  linarith

/-- **Iterates of the reference map.** If `ℓ (ρ b) = ℓ b - log 2` for every
`b > a`, and the first `k` iterates stay above `a`, then
`ℓ (ρ^[k] β) = ℓ β - k log 2`. -/
theorem scale_iterate (ℓ ρ : ℝ → ℝ) (a : ℝ)
    (hρ : ∀ b, a < b → ℓ (ρ b) = ℓ b - Real.log 2) (β : ℝ) :
    ∀ k : ℕ, (∀ j < k, a < ρ^[j] β) → ℓ (ρ^[k] β) = ℓ β - k * Real.log 2 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hall
    have h1 := ih (fun j hj => hall j (Nat.lt_succ_of_lt hj))
    have h2 := hρ _ (hall k (Nat.lt_succ_self k))
    rw [Function.iterate_succ_apply', h2, h1]
    push_cast
    ring

/-- **The rung count from the scale function.** If the first `n ≥ 1` iterates
stay above `a`, `ℓ` is monotone, `ℓ (ρ b) = ℓ b - log 2` above `a`, and
`ℓ β ≤ log N + C`, then `2^n ≤ 2 N e^{C - ℓ a}`. -/
theorem scale_rungs (ℓ ρ : ℝ → ℝ) (a C β : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hmono : Monotone ℓ)
    (hρ : ∀ b, a < b → ℓ (ρ b) = ℓ b - Real.log 2)
    (hβ : ℓ β ≤ Real.log N + C)
    (n : ℕ) (hn : 1 ≤ n) (hall : ∀ k < n, a < ρ^[k] β) :
    (2 : ℝ) ^ n ≤ 2 * N * Real.exp (C - ℓ a) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hit := scale_iterate ℓ ρ a hρ β m (fun k hk => hall k (Nat.lt_succ_of_lt hk))
  have hlast := hall m (Nat.lt_succ_self m)
  have hgt : ℓ a ≤ ℓ (ρ^[m] β) := hmono hlast.le
  have hm : (m : ℝ) * Real.log 2 ≤ Real.log N + (C - ℓ a) := by
    rw [hit] at hgt; linarith
  have hpow : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos two_pos, mul_comm]
  have hle : (2 : ℝ) ^ m ≤ N * Real.exp (C - ℓ a) := by
    rw [hpow]
    calc Real.exp ((m : ℝ) * Real.log 2)
        ≤ Real.exp (Real.log N + (C - ℓ a)) := Real.exp_le_exp.mpr hm
      _ = N * Real.exp (C - ℓ a) := by
        rw [Real.exp_add, Real.exp_log hNpos]
  have hpos : 0 < (N : ℝ) * Real.exp (C - ℓ a) := by positivity
  rw [pow_succ]
  nlinarith

/-- The two-loop scale function `ℓ(β) = β/c₁ - γ log (1 + β/β₁)`. -/
noncomputable def twoloop (c₁ γ β₁ : ℝ) (β : ℝ) : ℝ :=
  β / c₁ - γ * Real.log (1 + β / β₁)

/-- The two-loop scale function has slope at most `1/c₁` on `[0, ∞)`. -/
theorem twoloop_lipschitz (c₁ γ β₁ : ℝ) (hγ : 0 ≤ γ) (hβ₁ : 0 < β₁)
    (b b' : ℝ) (hb' : 0 ≤ b') (h : b' ≤ b) :
    twoloop c₁ γ β₁ b - twoloop c₁ γ β₁ b' ≤ (b - b') / c₁ := by
  unfold twoloop
  have h1 : 0 < 1 + b' / β₁ := by positivity
  have h2 : 1 + b' / β₁ ≤ 1 + b / β₁ := by
    have := div_le_div_of_nonneg_right h hβ₁.le; linarith
  have hlog := Real.log_le_log h1 h2
  have : 0 ≤ γ * (Real.log (1 + b / β₁) - Real.log (1 + b' / β₁)) :=
    mul_nonneg hγ (by linarith)
  have e : b / c₁ - b' / c₁ = (b - b') / c₁ := by ring
  linarith

/-- The increment of `log (1 + β/β₁)` is at most `(b - b')/β₁`. -/
theorem log_incr_le (β₁ b b' : ℝ) (hβ₁ : 0 < β₁) (hb' : 0 ≤ b') (h : b' ≤ b) :
    Real.log (1 + b / β₁) - Real.log (1 + b' / β₁) ≤ (b - b') / β₁ := by
  have h1 : 0 < 1 + b' / β₁ := by positivity
  have h1' : 0 < 1 + b / β₁ := by
    have : 0 ≤ b / β₁ := div_nonneg (hb'.trans h) hβ₁.le
    linarith
  rw [← Real.log_div h1'.ne' h1.ne']
  have hq := Real.log_le_sub_one_of_pos (div_pos h1' h1)
  have hq2 : (1 + b / β₁) / (1 + b' / β₁) - 1 = ((b - b') / β₁) / (1 + b' / β₁) := by
    field_simp; ring
  have hq3 : ((b - b') / β₁) / (1 + b' / β₁) ≤ (b - b') / β₁ := by
    have hnn : 0 ≤ (b - b') / β₁ := div_nonneg (by linarith) hβ₁.le
    have hone : 1 ≤ 1 + b' / β₁ := by
      have : 0 ≤ b' / β₁ := div_nonneg hb' hβ₁.le
      linarith
    exact div_le_self hnn hone
  linarith

/-- The two-loop scale function grows at least at rate `1/c₁ - γ/β₁`. -/
theorem twoloop_lower_incr (c₁ γ β₁ : ℝ) (hγ : 0 ≤ γ) (hβ₁ : 0 < β₁)
    (b b' : ℝ) (hb' : 0 ≤ b') (h : b' ≤ b) :
    (b - b') * (1 / c₁ - γ / β₁) ≤ twoloop c₁ γ β₁ b - twoloop c₁ γ β₁ b' := by
  unfold twoloop
  have hl := log_incr_le β₁ b b' hβ₁ hb' h
  have : γ * (Real.log (1 + b / β₁) - Real.log (1 + b' / β₁)) ≤ γ * ((b - b') / β₁) :=
    mul_le_mul_of_nonneg_left hl hγ
  have e1 : (b - b') * (1 / c₁ - γ / β₁) = (b / c₁ - b' / c₁) - γ * ((b - b') / β₁) := by
    ring
  linarith

/-- **The two-loop scale function is strictly increasing on `[0, ∞)`** when
`β₁ > c₁ γ`. -/
theorem twoloop_strictMono (c₁ γ β₁ : ℝ) (hc₁ : 0 < c₁) (hγ : 0 ≤ γ)
    (hβ₁ : c₁ * γ < β₁) :
    StrictMonoOn (twoloop c₁ γ β₁) (Set.Ici 0) := by
  have hβ₁pos : 0 < β₁ := lt_of_le_of_lt (mul_nonneg hc₁.le hγ) hβ₁
  intro b' hb' b _ hlt
  have hrate : 0 < 1 / c₁ - γ / β₁ := by
    rw [sub_pos, div_lt_div_iff₀ hβ₁pos hc₁]; linarith
  have := twoloop_lower_incr c₁ γ β₁ hγ hβ₁pos b b' hb' hlt.le
  have : 0 < (b - b') * (1 / c₁ - γ / β₁) := mul_pos (by linarith) hrate
  linarith

/-- `ℓ b ≥ b (1/c₁ - γ/β₁)` for `b ≥ 0`, since `ℓ 0 = 0`. -/
theorem twoloop_lower (c₁ γ β₁ : ℝ) (hγ : 0 ≤ γ) (hβ₁ : 0 < β₁) (b : ℝ) (hb : 0 ≤ b) :
    b * (1 / c₁ - γ / β₁) ≤ twoloop c₁ γ β₁ b := by
  have := twoloop_lower_incr c₁ γ β₁ hγ hβ₁ b 0 le_rfl hb
  have h0 : twoloop c₁ γ β₁ 0 = 0 := by simp [twoloop]
  rw [h0] at this; linarith

/-- **The endpoint coupling for `SU(2)`.** With `c₁ = 11/(3π²)`,
`γ = 51/121` and `β₁ = 4`, every `b ≥ 161/600` has `ℓ b ≥ log 2`. -/
theorem su2_twoloop_endpoint (b : ℝ) (hb : 161 / 600 ≤ b) :
    Real.log 2 ≤ twoloop (11 / (3 * π ^ 2)) (51 / 121) 4 b := by
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  have hlow := twoloop_lower (11 / (3 * π ^ 2)) (51 / 121) 4 (by norm_num) (by norm_num) b hb0
  have hinv : 1 / (11 / (3 * π ^ 2)) = 3 * π ^ 2 / 11 := by
    field_simp
  rw [hinv] at hlow
  have hpi : (3.141592 : ℝ) < π := Real.pi_gt_d6
  have hpi2 : (3.141592 : ℝ) ^ 2 < π ^ 2 := by
    have : (0 : ℝ) ≤ 3.141592 := by norm_num
    nlinarith
  have hcoef : (2.586 : ℝ) ≤ 3 * π ^ 2 / 11 - 51 / 121 / 4 := by
    nlinarith
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hcpos : (0 : ℝ) ≤ 3 * π ^ 2 / 11 - 51 / 121 / 4 := le_trans (by norm_num) hcoef
  have : (161 / 600 : ℝ) * 2.586 ≤ b * (3 * π ^ 2 / 11 - 51 / 121 / 4) := by
    have := mul_le_mul hb hcoef (by norm_num) hb0
    linarith
  norm_num at this ⊢
  linarith

end YangMills.Tuning
