import Mathlib

/-!
# Symmetric twist weightings and free spatial boundary

Finite checks for Proposition `ly:prop:weights`, Theorem `ly:thm:dyonic` and Proposition
`ly:prop:freebox` of the paper.

A twist class on the four-torus is a vector `c ∈ (ℤ/2)^6`, encoded as a natural number
`c < 64` whose bits `0, ..., 5` are the coordinates `c₁₂, c₁₃, c₁₄, c₂₃, c₂₄, c₃₄`. The
permutations of the four directions act by permuting the bits; `s12`, `s23`, `s34` are the
images of the transpositions `(1 2)`, `(2 3)`, `(3 4)`, which generate the action.
`pf c = c₁₂c₃₄ + c₁₃c₂₄ + c₁₄c₂₃ (mod 2)`. With the fourth direction as time a class is
`join m z`, with `m` the spatial planes `(c₁₂, c₁₃, c₂₃)` and `z` the temporal planes
`(c₁₄, c₂₄, c₃₄)`, both encoded by three bits; `mstar m = (c₂₃, c₁₃, c₁₂)`.

* `pf_invariant`, `pf_count` : `Pf` is invariant and odd on `28` of the `64` classes.
* `pf_join` : `Pf (m, z) = m⋆ · z`.
* `qdy_table`, `qtor_table`, `qsys_table` : the block multiplicities (times `8`) of the
  weights `(-1)^Pf`, `1` and `8·1_{0}` are `8·[e = m⋆]`, `8·[e = 0]` and `8·[m = 0]`.
* `gauss` : `∑_ω (-1)^(Pf ω + ⟨ω, c⟩) = 8 (-1)^(Pf c)`.
* `vanish_of_no_spatial` : an invariant function vanishing on the classes with a spatial
  plane vanishes on every nonzero class (part (b) of the proposition).
* `face_glue`, `glue_margin`, `freebox_datum` : the inequalities of Proposition
  `ly:prop:freebox`(b).
* `z2_dyonic_T8`, `z2_dyonic_step` : the bound of Theorem `ly:thm:dyonic`(c) at `T = 8` and
  its decrease in `T`.
-/

namespace YangMills.TwistForms

/-- Coordinate `i` of the class `c`. -/
def b (c i : ℕ) : Bool := c.testBit i

/-- `Pf c = c₁₂c₃₄ + c₁₃c₂₄ + c₁₄c₂₃ mod 2`. -/
def pf (c : ℕ) : Bool := xor (xor (b c 0 && b c 5) (b c 1 && b c 4)) (b c 2 && b c 3)

/-- Action of a permutation of the six planes, given as the list of image indices. -/
def perm (σ : List ℕ) (c : ℕ) : ℕ :=
  ((List.range 6).map (fun i => if b c i then 2 ^ (σ.getD i 0) else 0)).sum

/-- The transpositions `(1 2)`, `(2 3)`, `(3 4)` of the directions, acting on planes. -/
def s12 : List ℕ := [0, 3, 4, 1, 2, 5]
def s23 : List ℕ := [1, 0, 2, 3, 5, 4]
def s34 : List ℕ := [0, 2, 1, 4, 3, 5]

theorem perm_lt : ∀ c < 64, perm s12 c < 64 ∧ perm s23 c < 64 ∧ perm s34 c < 64 := by
  decide

theorem pf_invariant :
    ∀ c < 64, pf (perm s12 c) = pf c ∧ pf (perm s23 c) = pf c ∧ pf (perm s34 c) = pf c := by
  decide

theorem pf_count : ((List.range 64).filter (fun c => pf c)).length = 28 := by
  decide

/-- The class with spatial planes `m = (c₁₂, c₁₃, c₂₃)` and temporal planes
`z = (c₁₄, c₂₄, c₃₄)`. -/
def join (m z : ℕ) : ℕ :=
  (if m.testBit 0 then 1 else 0) + (if m.testBit 1 then 2 else 0) + (if m.testBit 2 then 8 else 0)
    + (if z.testBit 0 then 4 else 0) + (if z.testBit 1 then 16 else 0)
    + (if z.testBit 2 then 32 else 0)

/-- `m⋆ = (c₂₃, c₁₃, c₁₂)`. -/
def mstar (m : ℕ) : ℕ :=
  (if m.testBit 2 then 1 else 0) + (if m.testBit 1 then 2 else 0) + (if m.testBit 0 then 4 else 0)

/-- Parity of `e · z` for three-bit vectors. -/
def dot (e z : ℕ) : Bool :=
  xor (xor (e.testBit 0 && z.testBit 0) (e.testBit 1 && z.testBit 1)) (e.testBit 2 && z.testBit 2)

/-- Parity of the pairing `⟨ω, c⟩ = ∑ ω_ab c_ab` for six-bit vectors. -/
def pair (w c : ℕ) : Bool :=
  ((List.range 6).map (fun i => b w i && b c i)).foldl xor false

def sgn (x : Bool) : ℤ := if x then -1 else 1

theorem pf_join : ∀ m < 8, ∀ z < 8, pf (join m z) = dot (mstar m) z := by
  decide

/-- `8 q(m, e)` for the weight `(-1)^Pf`. -/
def qdy8 (m e : ℕ) : ℤ := ((List.range 8).map (fun z => sgn (xor (pf (join m z)) (dot e z)))).sum

/-- `8 q(m, e)` for the weight `1`. -/
def qtor8 (_m e : ℕ) : ℤ := ((List.range 8).map (fun z => sgn (dot e z))).sum

/-- `8 q(m, e)` for the weight `8·1_{0}`. -/
def qsys8 (m e : ℕ) : ℤ :=
  ((List.range 8).map (fun z => (if join m z = 0 then 8 else 0) * sgn (dot e z))).sum

theorem qdy_table : ∀ m < 8, ∀ e < 8, qdy8 m e = if e = mstar m then 8 else 0 := by
  decide

theorem qtor_table : ∀ m < 8, ∀ e < 8, qtor8 m e = if e = 0 then 8 else 0 := by
  decide

theorem qsys_table : ∀ m < 8, ∀ e < 8, qsys8 m e = if m = 0 then 8 else 0 := by
  decide

theorem gauss :
    ∀ c < 64, ((List.range 64).map (fun w => sgn (xor (pf w) (pair w c)))).sum = 8 * sgn (pf c) := by
  decide +kernel

/-- A class has a spatial plane: `c₁₂`, `c₁₃` or `c₂₃`. -/
def hasSpatial (c : ℕ) : Bool := b c 0 || b c 1 || b c 3

theorem star_moves :
    ∀ c < 64, c ≠ 0 →
      hasSpatial c = true ∨ hasSpatial (perm s34 c) = true ∨
        hasSpatial (perm s34 (perm s23 c)) = true := by
  decide

/-- Part (b) of Proposition `ly:prop:weights`: an invariant function that vanishes on every
class with a spatial plane vanishes on every nonzero class. -/
theorem vanish_of_no_spatial (f : ℕ → ℝ)
    (h23 : ∀ c < 64, f (perm s23 c) = f c) (h34 : ∀ c < 64, f (perm s34 c) = f c)
    (hsp : ∀ c < 64, hasSpatial c = true → f c = 0) :
    ∀ c < 64, c ≠ 0 → f c = 0 := by
  intro c hc hne
  obtain ⟨_, h2, h3⟩ := perm_lt c hc
  rcases star_moves c hc hne with h | h | h
  · exact hsp c hc h
  · rw [← h34 c hc]; exact hsp _ h3 h
  · have h4 : perm s34 (perm s23 c) < 64 := (perm_lt _ h2).2.2
    rw [← h23 c hc, ← h34 _ h2]; exact hsp _ h4 h

/-! ## Free spatial boundary -/

/-- The face inequality behind (F4) for the function `Y`. -/
theorem face_glue (a x y : ℝ) (ha : 0 ≤ a) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (1 + a * x) * (1 + a * y) ≤ (1 + a * x * y) * (1 + a) := by
  have h : 0 ≤ a * ((x - 1) * (y - 1)) := mul_nonneg ha (mul_nonneg (by linarith) (by linarith))
  nlinarith [h]

theorem log_three_lt : Real.log 3 < 5 / 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have he : (2718 / 1000 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hq := Real.add_one_lt_exp (show (1 / 4 : ℝ) ≠ 0 by norm_num)
  have h2 : Real.exp (5 / 4) = Real.exp 1 * Real.exp (1 / 4) := by
    rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith [Real.exp_pos 1, Real.exp_pos (1 / 4)]

/-- The margin in (F4): `(95/12)·(M L₂ L₃) - 6 log 3 > 0` once `M L₂ L₃ ≥ 1`. -/
theorem glue_margin (t : ℝ) (ht : 1 ≤ t) : 0 < 95 / 12 * t - 6 * Real.log 3 := by
  have := log_three_lt
  nlinarith

theorem exp_thirteen_gt : (2718 / 1000 : ℝ) ^ 13 < Real.exp 13 := by
  have h1 : (2718 / 1000 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h2 : Real.exp 13 = Real.exp 1 ^ 13 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  exact pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)

/-- `X^Y(3) = 6 log(1 + 2 e^{-27/2}) < 1/28684`. -/
theorem freebox_datum : 6 * Real.log (1 + 2 * Real.exp (-(27 / 2))) < 1 / 28684 := by
  have hpos : 0 < 2 * Real.exp (-(27 / 2)) := by positivity
  have hlog : Real.log (1 + 2 * Real.exp (-(27 / 2))) ≤ 2 * Real.exp (-(27 / 2)) := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 2 * Real.exp (-(27 / 2)) by linarith)
    linarith
  have hmono : Real.exp (-(27 / 2)) ≤ Real.exp (-13) := Real.exp_le_exp.mpr (by norm_num)
  have h13 : Real.exp (-13) = 1 / Real.exp 13 := by rw [Real.exp_neg]; ring
  have hbig := exp_thirteen_gt
  have hval : (12 : ℝ) / (2718 / 1000) ^ 13 < 1 / 28684 := by norm_num
  have hE : 0 < Real.exp 13 := Real.exp_pos 13
  have hc : 12 * Real.exp (-13) < 1 / 28684 := by
    rw [h13]
    calc 12 * (1 / Real.exp 13) = 12 / Real.exp 13 := by ring
      _ < 12 / (2718 / 1000) ^ 13 := by
          apply div_lt_div_of_pos_left (by norm_num) (by positivity) hbig
      _ < 1 / 28684 := hval
  linarith

/-! ## The dyonic datum of the `ℤ₂` theory -/

/-- The bound `192 T^4 (2^{-4T} + 64·2^{-2T²})` at `T = 8` is below `1/4097`. -/
theorem z2_dyonic_T8 :
    (192 : ℚ) * 8 ^ 4 * (1 / 2 ^ 32 + 64 / 2 ^ 128) < 1 / 4097 := by
  norm_num

/-- Both terms decrease: `(T+1)^4 2^{-4(T+1)} ≤ T^4 2^{-4T}` and the same with `2T²`. -/
theorem z2_dyonic_step (T : ℕ) (hT : 8 ≤ T) :
    ((T + 1 : ℚ) ^ 4 / 2 ^ (4 * (T + 1)) ≤ (T : ℚ) ^ 4 / 2 ^ (4 * T)) ∧
      ((T + 1 : ℚ) ^ 4 / 2 ^ (2 * (T + 1) ^ 2) ≤ (T : ℚ) ^ 4 / 2 ^ (2 * T ^ 2)) := by
  have hT' : (8 : ℚ) ≤ T := by exact_mod_cast hT
  have key : (T + 1 : ℚ) ^ 4 ≤ 16 * (T : ℚ) ^ 4 := by nlinarith [sq_nonneg ((T : ℚ) - 8)]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 : ℚ) ^ (4 * (T + 1)) = 16 * 2 ^ (4 * T) := by
      rw [show 4 * (T + 1) = 4 * T + 4 by ring, pow_add]; norm_num; ring
    rw [this]; nlinarith [pow_pos (show (0 : ℚ) < 2 by norm_num) (4 * T)]
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 : ℚ) ^ (2 * (T + 1) ^ 2) = 2 ^ (2 * T ^ 2) * 2 ^ (4 * T + 2) := by
      rw [← pow_add]; congr 1; ring
    rw [this]
    have h16 : (16 : ℚ) ≤ 2 ^ (4 * T + 2) := by
      calc (16 : ℚ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (4 * T + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hp : (0 : ℚ) < 2 ^ (2 * T ^ 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h16 (le_of_lt (mul_pos hp (pow_pos (show (0:ℚ) < T by linarith) 4)))]

end YangMills.TwistForms
