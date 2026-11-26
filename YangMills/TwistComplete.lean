import Mathlib
import YangMills.TwistForms

/-!
# Completeness of the symmetric twist weightings with multiplicities in `{0, 1}`

The converse in part (c) of Proposition `ly:prop:weights` of the paper: a real function `f` on
the twist classes `c < 64` that is invariant under the permutations of the four directions, and
whose block multiplicities `q f m e = 2⁻³ ∑_z (-1)^(e·z) f (m, z)` all lie in `{0, 1}` with
`q f 0 0 = 1`, is one of `8·1_{0}`, `1` and `(-1)^Pf`.

The proof has three steps.
* `orbit` : an invariant function is constant on orbits; `words` carries every class to the least
  element of its orbit, and the eleven orbits are listed in `reps`.
* `invert` : the values of `f` on the eleven orbits are an integer combination (the matrix `M`)
  of the eleven multiplicities `q f (rm j) (re j)`; the identity `M A = 8` is `MA`.
* `search` : for each of the `2^11` choices of these eleven multiplicities in `{0, 1}`, the
  resulting function has all `64` multiplicities in `{0, 1}` and `q 0 0 = 1` only in the three
  cases of the proposition.

The encoding of classes, `perm`, `join`, `dot`, `pf` and `sgn` are those of `TwistForms`.
-/

namespace YangMills.TwistComplete

open YangMills.TwistForms

/-- Generators by index: `0 ↦ (1 2)`, `1 ↦ (2 3)`, otherwise `(3 4)`. -/
def gen : ℕ → List ℕ
  | 0 => s12
  | 1 => s23
  | _ => s34

/-- Apply a word in the generators, first letter first. -/
def applyW : List ℕ → ℕ → ℕ
  | [], c => c
  | g :: w, c => applyW w (perm (gen g) c)

/-- For each class, a word carrying it to the least element of its orbit. -/
def words : List (List ℕ) :=
  [[], [], [1], [], [2, 1], [2], [1, 2], [], [0, 1], [0], [1, 0], [], [], [], [1], [],
   [0, 2, 1], [0, 2], [0], [0], [2, 1, 0], [2], [2, 1], [2], [0, 1, 2], [0], [0, 1], [0],
   [0, 2, 1], [0, 2], [], [], [1, 0, 2, 1], [1, 0], [1, 0, 2], [1, 0], [1, 2, 1, 0], [1, 2, 1],
   [1, 2], [1, 2], [0, 1, 0, 2], [0, 1, 0], [1, 0], [1, 0], [1, 0, 2, 1], [1], [1, 0, 2], [1],
   [0, 1, 2, 1, 0], [0, 1, 2, 1], [0, 1, 0, 2, 1], [0, 1], [2, 1, 0], [2, 1, 0], [1, 2, 1, 0],
   [2, 1], [0, 1, 2], [0, 1, 2], [0, 1, 0, 2], [0, 1], [0, 1, 2, 1, 0], [0, 2, 1],
   [1, 0, 2, 1], []]

/-- The least element of the orbit of `c`. -/
def rep (c : ℕ) : ℕ := applyW (words.getD c []) c

/-- The eleven orbit representatives (the graphs on four vertices, read as sets of planes). -/
def reps : List ℕ := [0, 1, 3, 7, 11, 12, 13, 15, 30, 31, 63]

/-- The `k`-th representative. -/
def r (k : ℕ) : ℕ := reps.getD k 0

/-- The index in `reps` of the orbit of each class. -/
def kidxTable : List ℕ :=
  [0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4, 5, 6, 6, 7, 1, 2, 5, 6, 2, 4, 6, 7, 2, 3, 6, 7, 6, 7, 8, 9,
   1, 5, 2, 6, 2, 6, 4, 7, 2, 6, 3, 7, 6, 8, 7, 9, 2, 6, 6, 8, 3, 7, 7, 9, 4, 7, 7, 9, 7, 9, 9, 10]

def kidx (c : ℕ) : ℕ := kidxTable.getD c 0

theorem kidx_spec : ∀ c < 64, kidx c < 11 ∧ r (kidx c) = rep c := by
  decide +kernel

theorem join_lt : ∀ m < 8, ∀ z < 8, join m z < 64 := by
  decide +kernel

/-- An invariant function is constant along words. -/
theorem inv_word (f : ℕ → ℝ) (h12 : ∀ c < 64, f (perm s12 c) = f c)
    (h23 : ∀ c < 64, f (perm s23 c) = f c) (h34 : ∀ c < 64, f (perm s34 c) = f c) :
    ∀ (w : List ℕ) (c : ℕ), c < 64 → applyW w c < 64 ∧ f (applyW w c) = f c := by
  intro w
  induction w with
  | nil => intro c hc; exact ⟨hc, rfl⟩
  | cons g w ih =>
    intro c hc
    have hp : perm (gen g) c < 64 ∧ f (perm (gen g) c) = f c := by
      obtain ⟨h1, h2, h3⟩ := perm_lt c hc
      rcases g with _ | _ | g
      · exact ⟨h1, h12 c hc⟩
      · exact ⟨h2, h23 c hc⟩
      · exact ⟨h3, h34 c hc⟩
    obtain ⟨h1, h2⟩ := ih _ hp.1
    exact ⟨h1, h2.trans hp.2⟩

/-- An invariant function is determined by its values on the representatives. -/
theorem orbit (f : ℕ → ℝ) (h12 : ∀ c < 64, f (perm s12 c) = f c)
    (h23 : ∀ c < 64, f (perm s23 c) = f c) (h34 : ∀ c < 64, f (perm s34 c) = f c) :
    ∀ c < 64, f c = f (r (kidx c)) := by
  intro c hc
  rw [(kidx_spec c hc).2]
  exact ((inv_word f h12 h23 h34 (words.getD c []) c hc).2).symm

/-- The block multiplicity `q_f(m, e) = 2⁻³ ∑_z (-1)^(e·z) f(m, z)`. -/
noncomputable def q (f : ℕ → ℝ) (m e : ℕ) : ℝ :=
  (∑ z ∈ Finset.range 8, (sgn (dot e z) : ℝ) * f (join m z)) / 8

/-- The coefficient of the `l`-th orbit value in `8 q(m, e)`. -/
def A (m e l : ℕ) : ℤ :=
  ∑ z ∈ Finset.range 8, if kidx (join m z) = l then sgn (dot e z) else 0

/-- Sums over `List.range` and over `Finset.range` agree. -/
theorem lsum (g : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- The same coefficient as a sum over a list, for evaluation. -/
def Aval (m e l : ℕ) : ℤ :=
  ((List.range 8).map (fun z => if kidx (join m z) = l then sgn (dot e z) else 0)).sum

theorem A_eq (m e l : ℕ) : A m e l = Aval m e l := by
  unfold A Aval
  rw [lsum]

theorem q_lin (f : ℕ → ℝ) (h12 : ∀ c < 64, f (perm s12 c) = f c)
    (h23 : ∀ c < 64, f (perm s23 c) = f c) (h34 : ∀ c < 64, f (perm s34 c) = f c)
    (m e : ℕ) (hm : m < 8) :
    8 * q f m e = ∑ l ∈ Finset.range 11, (A m e l : ℝ) * f (r l) := by
  have key : ∀ z ∈ Finset.range 8, (sgn (dot e z) : ℝ) * f (join m z) =
      ∑ l ∈ Finset.range 11,
        (if kidx (join m z) = l then (sgn (dot e z) : ℝ) else 0) * f (r l) := by
    intro z hz
    have hc := join_lt m hm z (Finset.mem_range.mp hz)
    rw [orbit f h12 h23 h34 _ hc]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (kidx_spec _ hc).1)]
  unfold q
  rw [show ∀ S : ℝ, 8 * (S / 8) = S from fun S => by ring]
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  unfold A
  push_cast
  rw [Finset.sum_mul]

/-- The eleven rows `(rm j, re j)` whose multiplicities determine `f`. -/
def rm : List ℕ := [0, 0, 2, 2, 4, 4, 6, 6, 7, 7, 7]
def re : List ℕ := [0, 2, 0, 3, 2, 6, 0, 2, 4, 6, 7]

theorem rm_lt : ∀ j < 11, rm.getD j 0 < 8 := by
  decide +kernel

/-- The inverse matrix: `f (r k) = ∑_j M k j · q f (rm j) (re j)`. -/
def Mrows : List (List ℤ) :=
  [[2, 6, -3, -6, -2, -1, 2, 2, -1, -2, -1], [0, 0, 1, 4, 2, 1, 0, 0, 1, 2, 1],
   [2, -2, 1, -2, -2, -1, -2, -2, -1, -2, -1], [0, 0, -3, 0, 2, 1, 4, 4, 1, 2, 1],
   [0, 0, 1, 0, -2, 1, 0, 0, 1, 2, 1], [0, 0, 1, -4, 2, 1, 0, 0, -1, -2, -1],
   [-2, 2, 1, 2, 2, -1, 2, 2, 1, 2, 1], [0, 0, 1, 0, -2, 1, 0, 0, -1, -2, -1],
   [2, -2, -3, -2, 2, -1, 2, -6, 3, 2, -1], [0, 0, 1, 0, -2, 1, 0, 0, -3, -2, 1],
   [0, 0, 1, 0, -2, 1, 0, 0, -5, 2, -1]]

def M (k j : ℕ) : ℤ := (Mrows.getD k []).getD j 0

theorem MA_list : ∀ k < 11, ∀ l < 11,
    ((List.range 11).map (fun j => M k j * Aval (rm.getD j 0) (re.getD j 0) l)).sum =
      if k = l then 8 else 0 := by
  decide +kernel

theorem MA (k : ℕ) (hk : k < 11) (l : ℕ) (hl : l < 11) :
    ∑ j ∈ Finset.range 11, M k j * A (rm.getD j 0) (re.getD j 0) l =
      if k = l then 8 else 0 := by
  simp only [A_eq]
  rw [← lsum]
  exact MA_list k hk l hl

theorem invert (f : ℕ → ℝ) (h12 : ∀ c < 64, f (perm s12 c) = f c)
    (h23 : ∀ c < 64, f (perm s23 c) = f c) (h34 : ∀ c < 64, f (perm s34 c) = f c)
    (k : ℕ) (hk : k < 11) :
    f (r k) = ∑ j ∈ Finset.range 11, (M k j : ℝ) * q f (rm.getD j 0) (re.getD j 0) := by
  have hq : ∀ j ∈ Finset.range 11, (M k j : ℝ) * q f (rm.getD j 0) (re.getD j 0) =
      ∑ l ∈ Finset.range 11,
        (M k j : ℝ) * (A (rm.getD j 0) (re.getD j 0) l : ℝ) / 8 * f (r l) := by
    intro j hj
    have h8 := q_lin f h12 h23 h34 (rm.getD j 0) (re.getD j 0) (rm_lt j (Finset.mem_range.mp hj))
    rw [show q f (rm.getD j 0) (re.getD j 0) =
        (∑ l ∈ Finset.range 11, (A (rm.getD j 0) (re.getD j 0) l : ℝ) * f (r l)) / 8 by
      linarith, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [Finset.sum_congr rfl hq, Finset.sum_comm]
  have hl : ∀ l ∈ Finset.range 11, ∑ j ∈ Finset.range 11,
      (M k j : ℝ) * (A (rm.getD j 0) (re.getD j 0) l : ℝ) / 8 * f (r l) =
      if k = l then f (r l) else 0 := by
    intro l hl
    rw [← Finset.sum_mul, ← Finset.sum_div]
    have hMA := congrArg (Int.cast : ℤ → ℝ) (MA k hk l (Finset.mem_range.mp hl))
    push_cast at hMA
    rw [hMA]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hl, Finset.sum_ite_eq]
  simp [hk]

/-- The orbit values determined by eleven multiplicities `bs` in `{0, 1}`. -/
def X (bs : List Bool) (k : ℕ) : ℤ :=
  ((List.range 11).map (fun j => M k j * (if bs.getD j false then 1 else 0))).sum

/-- The table of `A m e l`, row `8 m + e`. -/
def Atab : List (List ℤ) :=
  [[1, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0], [1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0],
     [1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0], [1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0],
     [1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0], [1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0],
     [1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0], [1, -3, 3, -1, 0, 0, 0, 0, 0, 0, 0],
     [0, 1, 2, 0, 1, 1, 2, 1, 0, 0, 0], [0, 1, 0, 0, -1, 1, 0, -1, 0, 0, 0],
     [0, 1, 0, 0, -1, 1, 0, -1, 0, 0, 0], [0, 1, -2, 0, 1, 1, -2, 1, 0, 0, 0],
     [0, 1, 2, 0, 1, -1, -2, -1, 0, 0, 0], [0, 1, 0, 0, -1, -1, 0, 1, 0, 0, 0],
     [0, 1, 0, 0, -1, -1, 0, 1, 0, 0, 0], [0, 1, -2, 0, 1, -1, 2, -1, 0, 0, 0],
     [0, 1, 2, 0, 1, 1, 2, 1, 0, 0, 0], [0, 1, 0, 0, -1, 1, 0, -1, 0, 0, 0],
     [0, 1, 2, 0, 1, -1, -2, -1, 0, 0, 0], [0, 1, 0, 0, -1, -1, 0, 1, 0, 0, 0],
     [0, 1, 0, 0, -1, 1, 0, -1, 0, 0, 0], [0, 1, -2, 0, 1, 1, -2, 1, 0, 0, 0],
     [0, 1, 0, 0, -1, -1, 0, 1, 0, 0, 0], [0, 1, -2, 0, 1, -1, 2, -1, 0, 0, 0],
     [0, 0, 1, 1, 0, 0, 2, 2, 1, 1, 0], [0, 0, 1, -1, 0, 0, 2, -2, 1, -1, 0],
     [0, 0, 1, 1, 0, 0, 0, 0, -1, -1, 0], [0, 0, 1, -1, 0, 0, 0, 0, -1, 1, 0],
     [0, 0, 1, 1, 0, 0, 0, 0, -1, -1, 0], [0, 0, 1, -1, 0, 0, 0, 0, -1, 1, 0],
     [0, 0, 1, 1, 0, 0, -2, -2, 1, 1, 0], [0, 0, 1, -1, 0, 0, -2, 2, 1, -1, 0],
     [0, 1, 2, 0, 1, 1, 2, 1, 0, 0, 0], [0, 1, 2, 0, 1, -1, -2, -1, 0, 0, 0],
     [0, 1, 0, 0, -1, 1, 0, -1, 0, 0, 0], [0, 1, 0, 0, -1, -1, 0, 1, 0, 0, 0],
     [0, 1, 0, 0, -1, 1, 0, -1, 0, 0, 0], [0, 1, 0, 0, -1, -1, 0, 1, 0, 0, 0],
     [0, 1, -2, 0, 1, 1, -2, 1, 0, 0, 0], [0, 1, -2, 0, 1, -1, 2, -1, 0, 0, 0],
     [0, 0, 1, 1, 0, 0, 2, 2, 1, 1, 0], [0, 0, 1, 1, 0, 0, 0, 0, -1, -1, 0],
     [0, 0, 1, -1, 0, 0, 2, -2, 1, -1, 0], [0, 0, 1, -1, 0, 0, 0, 0, -1, 1, 0],
     [0, 0, 1, 1, 0, 0, 0, 0, -1, -1, 0], [0, 0, 1, 1, 0, 0, -2, -2, 1, 1, 0],
     [0, 0, 1, -1, 0, 0, 0, 0, -1, 1, 0], [0, 0, 1, -1, 0, 0, -2, 2, 1, -1, 0],
     [0, 0, 1, 1, 0, 0, 2, 2, 1, 1, 0], [0, 0, 1, 1, 0, 0, 0, 0, -1, -1, 0],
     [0, 0, 1, 1, 0, 0, 0, 0, -1, -1, 0], [0, 0, 1, 1, 0, 0, -2, -2, 1, 1, 0],
     [0, 0, 1, -1, 0, 0, 2, -2, 1, -1, 0], [0, 0, 1, -1, 0, 0, 0, 0, -1, 1, 0],
     [0, 0, 1, -1, 0, 0, 0, 0, -1, 1, 0], [0, 0, 1, -1, 0, 0, -2, 2, 1, -1, 0],
     [0, 0, 0, 0, 1, 0, 0, 3, 0, 3, 1], [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, -1],
     [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, -1], [0, 0, 0, 0, 1, 0, 0, -1, 0, -1, 1],
     [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, -1], [0, 0, 0, 0, 1, 0, 0, -1, 0, -1, 1],
     [0, 0, 0, 0, 1, 0, 0, -1, 0, -1, 1], [0, 0, 0, 0, 1, 0, 0, -3, 0, 3, -1]]

theorem Aval_tab :
    ∀ m < 8, ∀ e < 8, ∀ l < 11, Aval m e l = (Atab.getD (8 * m + e) []).getD l 0 := by
  decide +kernel

/-- The table of the products `∑_l A m e l · M l j`, row `8 m + e`. -/
def Ctab : List (List ℤ) :=
  [[8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 8, -8, -8, 0, 0, 8, 8, 0, 0, 0],
     [0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 8, -8, -8, 0, 0, 8, 8, 0, 0, 0],
     [0, 8, -8, -8, 0, 0, 8, 8, 0, 0, 0], [8, 0, 0, -24, -16, -8, -8, -8, -8, -16, -8],
     [0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0],
     [8, -8, 0, 0, -8, 0, -8, -8, 0, 0, 0], [0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0], [-8, 8, 0, 16, 8, 0, 8, 8, 8, 16, 8],
     [0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0],
     [8, -8, 0, 0, -8, 0, -8, -8, 0, 0, 0], [0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0],
     [0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0], [-8, 8, 0, 16, 8, 0, 8, 8, 8, 16, 8],
     [0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0], [0, 0, 0, 0, 8, -8, 0, -8, 8, 8, 0],
     [0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0], [0, 0, 8, 0, -8, 0, -8, 0, -8, -8, 0],
     [0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0], [0, 0, 8, 0, -8, 0, -8, 0, -8, -8, 0],
     [8, -8, -8, -8, 0, 0, 0, -8, 0, 0, 0], [8, -8, 0, -8, -8, 0, -8, -16, 0, -8, -8],
     [0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0], [8, -8, 0, 0, -8, 0, -8, -8, 0, 0, 0],
     [0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0], [0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0], [0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0], [-8, 8, 0, 16, 8, 0, 8, 8, 8, 16, 8],
     [0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0],
     [0, 0, 0, 0, 8, -8, 0, -8, 8, 8, 0], [0, 0, 8, 0, -8, 0, -8, 0, -8, -8, 0],
     [0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0], [8, -8, -8, -8, 0, 0, 0, -8, 0, 0, 0],
     [0, 0, 8, 0, -8, 0, -8, 0, -8, -8, 0], [8, -8, 0, -8, -8, 0, -8, -16, 0, -8, -8],
     [0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0], [8, -8, -8, -8, 0, 0, 0, -8, 0, 0, 0],
     [0, 0, 0, 0, 8, -8, 0, -8, 8, 8, 0], [0, 0, 8, 0, -8, 0, -8, 0, -8, -8, 0],
     [0, 0, 8, 0, -8, 0, -8, 0, -8, -8, 0], [8, -8, 0, -8, -8, 0, -8, -16, 0, -8, -8],
     [0, 0, 8, 0, -16, 8, 0, 0, -16, -8, 0], [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8]]

theorem C_tab : ∀ m < 8, ∀ e < 8, ∀ j < 11,
    ((List.range 11).map (fun l => (Atab.getD (8 * m + e) []).getD l 0 * M l j)).sum =
      (Ctab.getD (8 * m + e) []).getD j 0 := by
  decide +kernel

/-- `8 q(m, e)` of the function with orbit values `X bs`, as a form in the bits. -/
def Qb (bs : List Bool) (m e : ℕ) : ℤ :=
  ((List.range 11).map (fun j => (Ctab.getD (8 * m + e) []).getD j 0 *
    (if bs.getD j false then 1 else 0))).sum

theorem Q_swap (bs : List Bool) (m e : ℕ) (hm : m < 8) (he : e < 8) :
    ((List.range 11).map (fun l => Aval m e l * X bs l)).sum = Qb bs m e := by
  unfold X Qb
  simp only [lsum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← C_tab m hm e he j (Finset.mem_range.mp hj), lsum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Aval_tab m hm e he l (Finset.mem_range.mp hl)]
  ring

/-- The bits of the three weightings `8·1_{0}`, `1`, `(-1)^Pf`. -/
def B1 : List Bool := [true, true, false, false, false, false, false, false, false, false, false]
def B2 : List Bool := [true, false, true, false, false, false, true, false, false, false, false]
def B3 : List Bool := [true, false, false, false, false, false, false, false, false, false, true]

/-- The exhaustive search over the `2^11` choices of the eleven multiplicities. -/
theorem search : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    let bs := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]
    Qb bs 0 0 = 8 → (∀ m < 8, ∀ e < 8, Qb bs m e = 0 ∨ Qb bs m e = 8) →
      bs = B1 ∨ bs = B2 ∨ bs = B3 := by
  decide +kernel

theorem X_B : (∀ k < 11, X B1 k = if r k = 0 then 8 else 0) ∧ (∀ k < 11, X B2 k = 1) ∧
    (∀ k < 11, X B3 k = sgn (pf (r k))) := by
  decide +kernel

theorem rep_zero : ∀ c < 64, (r (kidx c) = 0 ↔ c = 0) := by
  decide +kernel

theorem rep_pf : ∀ c < 64, pf (r (kidx c)) = pf c := by
  decide +kernel

/-- Part (c) of Proposition `ly:prop:weights`: an invariant function whose block multiplicities
all lie in `{0, 1}`, with `q f 0 0 = 1`, is `8·1_{0}`, `1` or `(-1)^Pf`. -/
theorem weights_complete (f : ℕ → ℝ) (h12 : ∀ c < 64, f (perm s12 c) = f c)
    (h23 : ∀ c < 64, f (perm s23 c) = f c) (h34 : ∀ c < 64, f (perm s34 c) = f c)
    (hq : ∀ m < 8, ∀ e < 8, q f m e = 0 ∨ q f m e = 1) (h00 : q f 0 0 = 1) :
    (∀ c < 64, f c = if c = 0 then 8 else 0) ∨ (∀ c < 64, f c = 1) ∨
      (∀ c < 64, f c = (sgn (pf c) : ℝ)) := by
  classical
  set d : ℕ → Bool := fun j => decide (q f (rm.getD j 0) (re.getD j 0) = 1) with hd
  set bs : List Bool := [d 0, d 1, d 2, d 3, d 4, d 5, d 6, d 7, d 8, d 9, d 10] with hbs
  -- the eleven multiplicities are the bits `bs`
  have hbit : ∀ j < 11, q f (rm.getD j 0) (re.getD j 0) = if bs.getD j false then 1 else 0 := by
    intro j hj
    have hgd : bs.getD j false = decide (q f (rm.getD j 0) (re.getD j 0) = 1) := by
      interval_cases j <;> rfl
    rw [hgd]
    rcases hq _ (rm_lt j hj) (re.getD j 0) (by interval_cases j <;> decide) with h | h <;>
      rw [h] <;> norm_num
  -- the orbit values are `X bs`
  have hX : ∀ k < 11, f (r k) = (X bs k : ℝ) := by
    intro k hk
    rw [invert f h12 h23 h34 k hk]
    unfold X
    rw [lsum]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbit j (Finset.mem_range.mp hj)]
  -- the multiplicities of `f` are `Qb bs / 8`
  have hQ : ∀ m < 8, ∀ e < 8, (Qb bs m e : ℝ) = 8 * q f m e := by
    intro m hm e he
    rw [q_lin f h12 h23 h34 m e hm, ← Q_swap bs m e hm he, lsum]
    simp only [← A_eq]
    push_cast
    apply Finset.sum_congr rfl
    intro l hl
    rw [hX l (Finset.mem_range.mp hl)]
  have hQ00 : Qb bs 0 0 = 8 := by
    have h8 : (Qb bs 0 0 : ℝ) = 8 := by rw [hQ 0 (by norm_num) 0 (by norm_num), h00]; norm_num
    exact_mod_cast h8
  have hQall : ∀ m < 8, ∀ e < 8, Qb bs m e = 0 ∨ Qb bs m e = 8 := by
    intro m hm e he
    rcases hq m hm e he with h | h
    · left
      have h8 : (Qb bs m e : ℝ) = 0 := by rw [hQ m hm e he, h]; norm_num
      exact_mod_cast h8
    · right
      have h8 : (Qb bs m e : ℝ) = 8 := by rw [hQ m hm e he, h]; norm_num
      exact_mod_cast h8
  have hs := search (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6) (d 7) (d 8) (d 9) (d 10) hQ00 hQall
  rcases hs with h | h | h
  · left
    intro c hc
    rw [orbit f h12 h23 h34 c hc, hX _ (kidx_spec c hc).1, hbs, h, X_B.1 _ (kidx_spec c hc).1]
    by_cases h0 : c = 0
    · rw [if_pos h0, if_pos ((rep_zero c hc).2 h0)]
      norm_num
    · have : r (kidx c) ≠ 0 := fun h' => h0 ((rep_zero c hc).1 h')
      rw [if_neg h0, if_neg this]
      norm_num
  · right; left
    intro c hc
    rw [orbit f h12 h23 h34 c hc, hX _ (kidx_spec c hc).1, hbs, h, X_B.2.1 _ (kidx_spec c hc).1]
    simp
  · right; right
    intro c hc
    rw [orbit f h12 h23 h34 c hc, hX _ (kidx_spec c hc).1, hbs, h, X_B.2.2 _ (kidx_spec c hc).1,
      rep_pf c hc]

end YangMills.TwistComplete
