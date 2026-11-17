import Mathlib

/-!
# Section 9 line-field checks in Lean (exact rational arithmetic, kernel evaluation)

Lean re-check of `julia/onecube/be_certificates.jl`, for `thm:BE-line-field`.

(a) The period-cell operator `M = DᵀD` on the 48 active links of the cell `{0,1}⁴` with the
line field of Table A1: for the integer vector `u` below, `a = Mu - 9u` and `b = u` satisfy
`M a = 9a + 17b` and `M b = a + 9b`, so `M(a + √17 b) = (9 + √17)(a + √17 b)`; the alternating
vector has Rayleigh quotient `304/24`.

(b) The exact Rayleigh quotients of the two test fields (data of
`julia/onecube/certificates/be_cert_plus.txt` and `be_cert_minus.txt`): `R₊ ≥ 1397/100`,
`R₋ ≥ 1394/100`, and the ratios `max|X_e|²/Σ|X_e|²`.

Every statement is closed by `decide +kernel`: the kernel evaluates the rational arithmetic.
None of these checks proves the continuum limit, the one-cube bound or the mass gap.
-/

namespace YangMills.OneCube.LineField

/-- A quaternion `a + b i + c j + d k` with rational coefficients. -/
structure Q4 where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ

def qmul (p q : Q4) : Q4 :=
  ⟨p.a*q.a - p.b*q.b - p.c*q.c - p.d*q.d,
   p.a*q.b + p.b*q.a + p.c*q.d - p.d*q.c,
   p.a*q.c - p.b*q.d + p.c*q.a + p.d*q.b,
   p.a*q.d + p.b*q.c - p.c*q.b + p.d*q.a⟩
def qcj (q : Q4) : Q4 := ⟨q.a, -q.b, -q.c, -q.d⟩
def qadd (p q : Q4) : Q4 := ⟨p.a + q.a, p.b + q.b, p.c + q.c, p.d + q.d⟩
def qsc (k : ℚ) (q : Q4) : Q4 := ⟨k*q.a, k*q.b, k*q.c, k*q.d⟩
/-- Real part of the trace of the SU(2) matrix of `q`. -/
def rt (q : Q4) : ℚ := 2 * q.a
def qone : Q4 := ⟨1, 0, 0, 0⟩
def qzero : Q4 := ⟨0, 0, 0, 0⟩

/-- Table A1: the frozen direction of the site with index `8x₀ + 4x₁ + 2x₂ + x₃`. -/
def sigTab : List Nat := [0, 1, 3, 3, 2, 1, 2, 0, 0, 2, 1, 2, 3, 3, 1, 0]
def sig (i : Nat) : Nat := sigTab.getD i 0
/-- Neighbour in direction `m` in the period cell (coordinate `m` is bit `3 - m`). -/
def nb (i m : Nat) : Nat := i ^^^ (1 <<< (3 - m))
def links : List (Nat × Nat) :=
  (List.range 16).flatMap fun i => (List.range 4).map fun m => (i, m)
/-- The 48 active (non-frozen) links, in the order of the certificate files. -/
def act : List (Nat × Nat) := links.filter fun l => sig l.1 != l.2
def plaquettes : List (Nat × Nat × Nat) :=
  (List.range 16).flatMap fun i => (List.range 4).flatMap fun m =>
    ((List.range 4).filter fun n => m < n).map fun n => (i, m, n)
def edges (p : Nat × Nat × Nat) : List ((Nat × Nat) × Int) :=
  let (x, m, n) := p
  [((x, m), 1), ((nb x m, n), 1), ((nb x n, m), -1), ((x, n), -1)]

/-! ### (a) the period-cell operator -/

def idx (l : Nat × Nat) : Option Nat := act.idxOf? l
def getI (v : List Int) (l : Nat × Nat) : Int := match idx l with
  | some j => v.getD j 0
  | none => 0
/-- `D v`: one entry per plaquette. -/
def Dv (v : List Int) : List Int :=
  plaquettes.map fun p => (edges p).foldl (fun s (l, e) => s + e * getI v l) 0
/-- `Dᵀ w`. -/
def DTw (w : List Int) : List Int :=
  (List.range act.length).map fun j =>
    (plaquettes.zip w).foldl (fun s (p, wp) =>
      s + (edges p).foldl (fun t (l, e) => if idx l = some j then t + e * wp else t) 0) 0
def Mv (v : List Int) : List Int := DTw (Dv v)
def lin (α : Int) (v : List Int) (β : Int) (w : List Int) : List Int :=
  (v.zip w).map fun (x, y) => α * x + β * y
def dot (v w : List Int) : Int := (v.zip w).foldl (fun s (x, y) => s + x * y) 0

def uvec : List Int :=
  [0,0,0,0,0,0,1,0,0,0,-1,0,0,0,-1,-1,0,1,0,0,1,1,0,-1,1,0,-1,0,0,1,-1,0,1,0,0,-1,0,-1,0,1,0,0,0,0,0,0,0,0]
def avec : List Int := lin 1 (Mv uvec) (-9) uvec
def wvec : List Int :=
  act.map fun (x, m) => [1, -1, 0, 0].getD m 0 * (-1) ^ (x % 2 + x / 2 % 2 + x / 4 % 2 + x / 8 % 2)

theorem act_length : act.length = 48 := by decide +kernel
theorem plaquettes_length : plaquettes.length = 96 := by decide +kernel

/-- `M a = 9a + 17b` and `M b = a + 9b` with `b = u ≠ 0`: the eigenvalue `9 + √17`. -/
theorem eigen_9_sqrt17 :
    Mv avec = lin 9 avec 17 uvec ∧ Mv uvec = lin 1 avec 9 uvec ∧ uvec ≠ List.replicate 48 0 := by
  decide +kernel

/-- The alternating vector has Rayleigh quotient `304/24`. -/
theorem alternating_quotient : 24 * dot wvec (Mv wvec) = 304 * dot wvec wvec := by decide +kernel

/-! ### (b) the exact Rayleigh quotients of the test fields -/

/-- Test field `certPlus`: (S?, r₁, r₂, r₃, X₁, X₂, X₃) per active link, in the order of `act`. -/
def certPlus : List (Bool × Int × Int × Int × Int × Int × Int) :=
  [ (false, 20, -12, -37, 286, -629, 209),
    (false, 34, -21, -9, -111, 204, -55),
    (true, 15, -13, 76, -121, 458, -199),
    (false, 1, -4, 2, 137, -433, -565),
    (true, 3, 18, -2, -25, 144, 189),
    (true, -16, 12, -75, -191, 277, 383),
    (true, 77, 16, -29, 297, -337, -245),
    (false, 3, 25, -23, -305, 501, 423),
    (false, -34, 20, 9, 80, -165, -153),
    (true, -2, -11, -3, -400, 484, 361),
    (false, 1, -2, 0, 196, -360, -315),
    (true, -3, -18, 2, 147, -156, -106),
    (false, 11, 24, 5, 116, -593, -398),
    (false, -20, 12, 37, 548, 323, 340),
    (true, -6, -21, 11, -670, 268, 56),
    (true, -3, -16, -1, -77, 316, 401),
    (true, 7, 70, -53, -101, 126, 174),
    (true, 5, 21, -10, 251, -402, -547),
    (true, 73, 7, -50, -120, 583, 409),
    (false, -3, -25, 23, -553, -322, -335),
    (false, -10, -43, 40, 673, -260, -68),
    (false, -2, 2, 0, -222, 339, 320),
    (true, -7, -70, 53, -42, 154, 176),
    (false, 10, 43, -40, 188, -477, -512),
    (false, 27, 13, -25, -224, 441, -135),
    (true, 5, 56, 4, -46, 212, -94),
    (true, -10, -6, 53, 201, -644, 255),
    (false, -1, 4, -2, -259, 391, 552),
    (true, -8, -4, -10, -447, -396, -406),
    (true, 10, 5, -52, 705, 15, -149),
    (true, -78, -15, 29, -301, -381, -157),
    (true, -5, -56, -4, -144, -187, -8),
    (false, 64, 36, -14, 436, 566, 89),
    (true, 2, 11, 4, 260, -403, -543),
    (true, 3, 28, -10, 446, 395, 409),
    (false, -63, -35, 14, -707, 8, 136),
    (false, -11, -25, -5, 281, 384, 546),
    (false, -27, -13, 24, -259, -299, -322),
    (false, 51, 36, -77, -75, -118, -194),
    (true, 3, 17, 2, -181, -268, -403),
    (true, 8, 4, 10, 350, 418, 474),
    (false, -3, -37, 1, -135, -139, -139),
    (true, -73, -6, 49, 434, 542, 200),
    (false, -51, -36, 77, -143, -172, -86),
    (true, -23, -23, -35, -312, -402, -44),
    (true, -2, -28, 10, 281, -478, -464),
    (false, 3, 37, 0, -108, 158, 140),
    (true, 23, 22, 35, -115, 335, 368) ]

/-- Test field `certMinus`: (S?, r₁, r₂, r₃, X₁, X₂, X₃) per active link, in the order of `act`. -/
def certMinus : List (Bool × Int × Int × Int × Int × Int × Int) :=
  [ (false, -2, 18, 51, 147, -111, 456),
    (true, -18, 13, -38, -181, 259, -636),
    (true, -24, 47, 21, 54, -66, 208),
    (true, -64, -8, 35, 312, 182, 388),
    (true, 46, -3, -44, -540, -255, -388),
    (true, 22, -49, -23, 201, 49, 63),
    (true, -12, 17, 3, -707, 204, 41),
    (false, -29, 28, 7, 386, 118, -580),
    (true, 21, -14, 42, 335, -328, 534),
    (false, -22, -37, 28, 699, -226, -62),
    (false, -21, 3, 0, -352, -89, 608),
    (true, -47, -2, 50, -377, 290, -525),
    (true, -49, -71, 24, 19, 548, 455),
    (false, 2, -18, -52, -154, -368, -290),
    (false, -12, -46, -73, 29, -199, -180),
    (true, 64, -22, 7, -399, -252, -537),
    (true, -94, 14, 23, 387, 181, 269),
    (false, -9, 53, 73, 58, 109, 269),
    (false, 36, -76, -7, -19, -405, -346),
    (false, 28, -28, -8, 209, 531, 417),
    (true, -6, 26, -5, -99, -157, -111),
    (false, 21, -3, -1, 285, -393, -516),
    (true, 88, -9, -27, -151, 279, 385),
    (true, 6, -24, 4, -51, 115, 159),
    (true, 74, 18, 1, -199, 164, -663),
    (true, -31, 25, -43, 120, -218, 455),
    (true, -38, -45, 35, 62, -48, 206),
    (true, 68, 4, -35, 20, 399, 340),
    (false, 39, -9, -38, -143, -580, -393),
    (true, 38, 45, -35, 74, 174, 100),
    (true, 10, -18, -4, 566, -362, 302),
    (true, 37, -28, 54, -328, 301, -250),
    (false, -36, -31, 10, -221, 106, -87),
    (false, 24, 39, -27, -15, -573, -461),
    (true, -2, -46, 53, 116, 419, 267),
    (false, 32, 33, -11, -24, 191, 186),
    (true, 50, 72, -23, -434, 71, 558),
    (true, -75, -16, -1, 54, 537, -464),
    (true, -37, -43, -68, 369, -610, -113),
    (true, -62, 24, -7, 396, -69, -589),
    (false, -38, 9, 38, -22, -521, 489),
    (false, -2, 34, 16, -389, 596, 99),
    (false, -33, 80, 7, -400, 263, -212),
    (true, 31, 46, 73, 471, -423, 345),
    (false, -40, -22, -18, -115, 161, -115),
    (true, 0, 47, -52, -226, 283, 355),
    (false, 3, -36, -17, 230, -397, -550),
    (false, 39, 22, 18, -79, 120, 174) ]


abbrev Row := Bool × Int × Int × Int × Int × Int × Int

/-- Link variable (inverse stereographic projection of `r/100`, sign flipped for `N`) and field. -/
def toQ (row : Row) : Q4 × Q4 :=
  let (sflag, r1, r2, r3, x1, x2, x3) := row
  let s1 : ℚ := r1 / 100
  let s2 : ℚ := r2 / 100
  let s3 : ℚ := r3 / 100
  let s := s1^2 + s2^2 + s3^2
  let u : Q4 := ⟨(1 - s) / (1 + s), 2 * s1 / (1 + s), 2 * s2 / (1 + s), 2 * s3 / (1 + s)⟩
  (if sflag then u else ⟨-u.a, u.b, u.c, u.d⟩, ⟨0, x1, x2, x3⟩)

def fieldMap (cert : List Row) : List ((Nat × Nat) × (Q4 × Q4)) := act.zip (cert.map toQ)
def getQ (fm : List ((Nat × Nat) × (Q4 × Q4))) (l : Nat × Nat) : Q4 :=
  match fm.lookup l with | some (q, _) => q | none => qone
def getX (fm : List ((Nat × Nat) × (Q4 × Q4))) (l : Nat × Nat) : Q4 :=
  match fm.lookup l with | some (_, x) => x | none => qzero

def plaqTerm (fm : List ((Nat × Nat) × (Q4 × Q4))) (p : Nat × Nat × Nat) : ℚ :=
  let (x, m, n) := p
  let e1 := (x, m); let e2 := (nb x m, n); let e3 := (nb x n, m); let e4 := (x, n)
  let Q1 := getQ fm e1; let Q2 := getQ fm e2; let Q3 := getQ fm e3; let Q4' := getQ fm e4
  let W := qmul (qmul Q1 Q2) (qmul (qcj Q3) (qcj Q4'))
  let Y1 := getX fm e1
  let Y2 := qmul (qmul Q1 (getX fm e2)) (qcj Q1)
  let Y3 := qmul (qmul Q4' (getX fm e3)) (qcj Q4')
  let Y4 := getX fm e4
  let A := qadd (qadd (qmul Y1 Y1) (qsc 2 (qmul Y1 Y2))) (qmul Y2 Y2)
  let B := qadd (qadd (qmul Y3 Y3) (qsc 2 (qmul Y3 Y4))) (qmul Y4 Y4)
  rt (qmul A W) + rt (qmul W B) - 2 * rt (qmul (qmul (qadd Y1 Y2) W) (qadd Y3 Y4))

def total (cert : List Row) : ℚ :=
  let fm := fieldMap cert
  plaquettes.foldl (fun acc p => acc + plaqTerm fm p) 0
def sq2 (X : Q4) : ℚ := 2 * (X.b^2 + X.c^2 + X.d^2)
def nrm (cert : List Row) : ℚ := (cert.map toQ).foldl (fun acc qx => acc + sq2 qx.2) 0
def mx (cert : List Row) : ℚ := (cert.map toQ).foldl (fun acc qx => max acc (sq2 qx.2)) 0

/-- Every plaquette of the cell contains exactly one frozen link. -/
theorem one_frozen_link :
    plaquettes.all (fun p => ((edges p).filter fun le => sig le.1.1 == le.1.2).length == 1) = true := by
  decide +kernel

/-- Exact unit quaternions on the active links. -/
theorem unit_links :
    (certPlus ++ certMinus).all (fun r => let q := (toQ r).1; q.a^2 + q.b^2 + q.c^2 + q.d^2 == 1) = true := by
  decide +kernel

theorem R_plus : (1397 / 100 : ℚ) ≤ total certPlus / nrm certPlus := by decide +kernel

theorem R_minus : (1394 / 100 : ℚ) ≤ -total certMinus / nrm certMinus := by decide +kernel

theorem ratio_plus : mx certPlus / nrm certPlus = 525483 / 16378696 := by decide +kernel

theorem ratio_minus : mx certMinus / nrm certMinus = 543521 / 16161106 := by decide +kernel

theorem ratio_bounds : 1728 * (525483 / 16378696 : ℚ) < 56 ∧ 1728 * (543521 / 16161106 : ℚ) < 59 := by
  norm_num

end YangMills.OneCube.LineField
