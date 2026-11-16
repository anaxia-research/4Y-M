import Mathlib

/-!
# One-cube criteria: the pseudoreal surface integrals (check L12)

For `SU(2)` with normalised Haar measure, the integral of `∏_{p∈S} Tr U_p` over a
closed plaquette surface `S` is evaluated by integrating the links one at a time
with the pairing rules of the paper (Lemma `pairing`), for characters `χ = Tr`
of dimension `d = 2` and Frobenius–Schur indicator `ι = -1`:

* (R1) `∫ χ(AU) χ(U⁻¹B) dU = χ(AB)/d`
* (R2) `∫ χ(AUBU⁻¹) dU = χ(A) χ(B)/d`
* (R3) `∫ χ(AU) χ(BU) dU = χ(AB⁻¹)/d`
* (R4) `∫ χ(AUBU) dU = ι χ(AB⁻¹)/d`

together with `χ(1) = d`. After all `E` links are integrated the value is
`ι^{n₄} d^{F_end - E}`, where `n₄` is the number of (R4) steps and `F_end` the
number of (empty) words left.

**What is checked here.** The surfaces `S` (28 plaquettes, in `ℤ⁴`) and `S'`
(42 plaquettes, on `(ℤ/4)³ × ℤ/3`) are entered plaquette by plaquette; the
elimination by (R1)–(R4) is implemented as a function on words of signed links
and evaluated by the kernel (`decide`). We check that every link lies in exactly
two plaquettes, the counts `F`, `E`, the number of lattice vertices, the counts
`n₁,…,n₄`, `F_end`, and that `ι^{n₄} 2^{F_end-E}` equals `-2⁻²⁷` for `S` and
`-2⁻⁴³` for `S'`; for `S'` also the odd intersection with every stack.
The Haar integrals and the pairing rules (R1)–(R4) themselves are not
formalised; they are the standard Schur orthogonality relations proved in the
paper.
-/

namespace YangMills.OneCube.Haar

/-- A plaquette `(x₀x₁x₂x₃; μν)`. -/
structure Plaq where
  x : List ℕ
  μ : ℕ
  ν : ℕ
  deriving DecidableEq, Repr

/-- A signed link: link code and exponent (`true` for `+1`). -/
abbrev Letter := ℕ × Bool

/-- Translate a site by the unit vector in direction `μ`, modulo the periods. -/
def shift (per : List ℕ) (x : List ℕ) (μ : ℕ) : List ℕ :=
  (List.range 4).map fun i => ((x.getD i 0) + (if i = μ then 1 else 0)) % (per.getD i 1)

/-- Code of the link `(x, μ)`. -/
def linkCode (per : List ℕ) (x : List ℕ) (μ : ℕ) : ℕ :=
  let y := (List.range 4).map fun i => (x.getD i 0) % (per.getD i 1)
  (((y.getD 0 0 * 16 + y.getD 1 0) * 16 + y.getD 2 0) * 16 + y.getD 3 0) * 4 + μ

/-- The word `U_μ(x) U_ν(x+μ̂) U_μ(x+ν̂)⁻¹ U_ν(x)⁻¹` of a plaquette. -/
def word (per : List ℕ) (p : Plaq) : List Letter :=
  [(linkCode per p.x p.μ, true), (linkCode per (shift per p.x p.μ) p.ν, true),
   (linkCode per (shift per p.x p.ν) p.μ, false), (linkCode per p.x p.ν, false)]

/-- Vertices of a plaquette. -/
def verts (per : List ℕ) (p : Plaq) : List (List ℕ) :=
  let norm := fun (y : List ℕ) => (List.range 4).map fun i => (y.getD i 0) % (per.getD i 1)
  [norm p.x, shift per p.x p.μ, shift per p.x p.ν, shift per (shift per p.x p.μ) p.ν]

def inv (w : List Letter) : List Letter := w.reverse.map fun l => (l.1, !l.2)

/-- Rotate a cyclic word so that the first occurrence of link `ℓ` comes first. -/
def rotateTo (w : List Letter) (ℓ : ℕ) : List Letter :=
  let i := w.findIdx (fun l => l.1 == ℓ)
  w.drop i ++ w.take i

/-- Counts `(n₁, n₂, n₃, n₄, F_end)` and the words still to be integrated. -/
structure State where
  n : ℕ × ℕ × ℕ × ℕ
  done : ℕ
  words : List (List Letter)
  deriving DecidableEq, Repr

/-- Move empty words to the counter `done`. -/
def tidy (s : State) : State :=
  { s with done := s.done + (s.words.filter (·.isEmpty)).length,
           words := s.words.filter (fun w => !w.isEmpty) }

/-- Integrate the first link of the first word with the applicable rule. -/
def step (s : State) : State :=
  match s.words with
  | [] => s
  | [] :: _ => s
  | (l :: w1) :: rest =>
    let ℓ := l.1
    let v1 := rotateTo (l :: w1) ℓ
    let e1 := (v1.headD (0, true)).2
    let a := v1.tail
    let (n1, n2, n3, n4) := s.n
    if a.any (fun m => m.1 == ℓ) then
      let i := a.findIdx (fun m => m.1 == ℓ)
      let b1 := a.take i
      let e2 := (a.getD i (0, true)).2
      let b2 := a.drop (i + 1)
      if e1 != e2 then
        tidy { n := (n1, n2 + 1, n3, n4), done := s.done, words := b1 :: b2 :: rest }
      else
        tidy { n := (n1, n2, n3, n4 + 1), done := s.done, words := (b2 ++ inv b1) :: rest }
    else
      let j := rest.findIdx (fun w => w.any (fun m => m.1 == ℓ))
      let v2 := rotateTo (rest.getD j []) ℓ
      let e2 := (v2.headD (0, true)).2
      let b := v2.tail
      let rest' := rest.eraseIdx j
      if e1 != e2 then
        let merged := if e1 then a ++ b else b ++ a
        tidy { n := (n1 + 1, n2, n3, n4), done := s.done, words := merged :: rest' }
      else
        tidy { n := (n1, n2, n3 + 1, n4), done := s.done, words := (a ++ inv b) :: rest' }

def run : ℕ → State → State
  | 0, s => s
  | k + 1, s => run k (step s)

def start (per : List ℕ) (S : List Plaq) : State :=
  tidy { n := (0, 0, 0, 0), done := 0, words := S.map (word per) }

def allLinks (per : List ℕ) (S : List Plaq) : List ℕ := (S.flatMap (word per)).map (·.1)

/-- Every link of `S` lies in exactly two plaquettes (each plaquette word contains
four distinct links, so this is the number of occurrences). -/
def closed (per : List ℕ) (S : List Plaq) : Bool :=
  (S.all fun p => ((word per p).map (·.1)).Nodup) &&
  ((allLinks per S).all fun ℓ => (allLinks per S).count ℓ == 2)

def numLinks (per : List ℕ) (S : List Plaq) : ℕ := (allLinks per S).dedup.length
def numVerts (per : List ℕ) (S : List Plaq) : ℕ := (S.flatMap (verts per)).dedup.length

/-- `ι^{n₄} d^{F_end - E}` for `d = 2`, `ι = -1`. -/
def value (s : State) (E : ℕ) : ℚ := (-1) ^ s.n.2.2.2 * 2 ^ s.done / 2 ^ E

/-! ## The surface `S` (a lattice `ℝP²`) -/

def P (s : String) (μ ν : ℕ) : Plaq :=
  ⟨s.toList.map (fun c => c.toNat - '0'.toNat), μ, ν⟩

/-- The band `M`, the cylinder `Y` and the cap `K` of the paper, in this order. -/
def surfS : List Plaq :=
  [P "0000" 0 1, P "0100" 0 1, P "1100" 0 1, P "1100" 0 2, P "2000" 1 2, P "1000" 0 2, P "0000" 0 2,
   P "0000" 1 3, P "0000" 2 3, P "0010" 0 3, P "1010" 0 3, P "2010" 1 3, P "1110" 0 3, P "1100" 2 3,
   P "1000" 1 3, P "1000" 0 3, P "2000" 1 3, P "2100" 1 3, P "1200" 0 3, P "0200" 0 3, P "0100" 1 3,
   P "0001" 1 2, P "0011" 0 1, P "0101" 0 2, P "0101" 0 1, P "1101" 0 1, P "1001" 0 1, P "1011" 0 1]

/-- `S` lives in `ℤ⁴`; periods larger than every coordinate change nothing. -/
def perZ : List ℕ := [8, 8, 8, 8]

theorem S_closed : closed perZ surfS = true := by decide +kernel
theorem S_counts : surfS.length = 28 ∧ numLinks perZ surfS = 56 ∧ numVerts perZ surfS = 29 := by
  decide +kernel

theorem S_elimination :
    run 56 (start perZ surfS) = ⟨(14, 28, 13, 1), 29, []⟩ := by decide +kernel

/-- **L12 (S).** `∫ ∏_{p∈S} Tr U_p = -2⁻²⁷`, granting (R1)–(R4). -/
theorem L12_S : value (run 56 (start perZ surfS)) 56 = -1 / 2 ^ 27 := by
  rw [S_elimination]; norm_num [value]

/-! ## The surface `S'` on `(ℤ/4)³ × ℤ/3` -/

def perL : List ℕ := [4, 4, 4, 3]

def tubeT : List Plaq := [P "3000" 0 1, P "3000" 0 3, P "3001" 0 1, P "3100" 0 3]

def torusQ : List Plaq :=
  ((List.range 4).flatMap fun α => (List.range 3).map fun β => (α, β)).filter (· ≠ (0, 0)) |>.map
    fun ab => ⟨[3, ab.1, 0, ab.2], 1, 3⟩

def surfS' : List Plaq := surfS.erase (P "0000" 1 3) ++ tubeT ++ torusQ

theorem S'_closed : closed perL surfS' = true := by decide +kernel
theorem S'_counts : surfS'.length = 42 ∧ numLinks perL surfS' = 84 ∧ numVerts perL surfS' = 41 := by
  decide +kernel

theorem S'_elimination :
    run 84 (start perL surfS') = ⟨(27, 41, 15, 1), 41, []⟩ := by decide +kernel

/-- **L12 (S').** `∫ ∏_{p∈S'} Tr U_p = -2⁻⁴³`, granting (R1)–(R4). -/
theorem L12_S' : value (run 84 (start perL surfS')) 84 = -1 / 2 ^ 43 := by
  rw [S'_elimination]; norm_num [value]

/-- Every stack `𝒱(α, β)` meets `S'` in an odd number of plaquettes. -/
theorem S'_stacks : ∀ α ∈ List.range 4, ∀ β ∈ List.range 3,
    (surfS'.filter fun p => p.μ = 1 ∧ p.ν = 3 ∧ p.x.getD 1 0 = α ∧ p.x.getD 3 0 = β).length % 2 = 1 := by
  decide +kernel

end YangMills.OneCube.Haar
