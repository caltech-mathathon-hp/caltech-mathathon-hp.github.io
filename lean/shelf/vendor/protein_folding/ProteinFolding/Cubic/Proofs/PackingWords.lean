import ProteinFolding.Cubic.Proofs.VerifierPerfectCount
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Literal words for the alternative cubic packing frame described in
`research/simple_cubic_reduction.md` and `research/linear_routing_and_prefix.md`.
The input is an exact packing problem with q bins of width 4Q. Items of width
a occupy d*a H residues, where d=q*(4Q+2). This file proves the word arithmetic
and output-size bounds only; it does not assume or assert geometric forcing.
The frozen perfect-folding predicate and its encoding are unchanged. -/

namespace ProteinFolding.CubicPacking

open CubicCertificates

def repeatWord (w : Sequence) : ℕ → Sequence
  | 0 => []
  | k + 1 => w ++ repeatWord w k

theorem repeatWord_length (w : Sequence) (k : ℕ) :
    (repeatWord w k).length = k * w.length := by
  induction k with
  | zero => simp [repeatWord]
  | succ k ih => simp [repeatWord, ih, Nat.succ_mul, Nat.add_comm]

theorem hydrophobicCount_append (u v : Sequence) :
    hydrophobicCount (u ++ v) = hydrophobicCount u + hydrophobicCount v := by
  induction u with
  | nil => simp [hydrophobicCount, hydrophobicIndices]
  | cons r u ih =>
    simp only [List.cons_append, hydrophobicCount_cons, ih, Nat.add_assoc]

theorem hydrophobicCount_repeatWord (w : Sequence) (k : ℕ) :
    hydrophobicCount (repeatWord w k) = k * hydrophobicCount w := by
  induction k with
  | zero => simp [repeatWord, hydrophobicCount, hydrophobicIndices]
  | succ k ih =>
    simp [repeatWord, hydrophobicCount_append, ih, Nat.succ_mul, Nat.add_comm]

theorem hydrophobicCount_replicate (k : ℕ) (r : Residue) :
    hydrophobicCount (List.replicate k r) = if r = .H then k else 0 := by
  induction k with
  | zero => simp [hydrophobicCount, hydrophobicIndices]
  | succ k ih => simp [List.replicate_succ, hydrophobicCount_cons, ih]; split_ifs <;> omega

/-- A compressed edge path: each H has a P on both sides. -/
def edgeWord (t : ℕ) : Sequence := repeatWord [.P, .H, .P] t

/-- A surface path with paired H residues; the parameter is its H count when even. -/
def faceWord (t : ℕ) : Sequence := repeatWord [.P, .H, .H, .P] (t / 2)

theorem edgeWord_length (t : ℕ) : (edgeWord t).length = 3 * t := by
  simp [edgeWord, repeatWord_length, Nat.mul_comm]

theorem edgeWord_count (t : ℕ) : hydrophobicCount (edgeWord t) = t := by
  rw [edgeWord, hydrophobicCount_repeatWord]
  have h : hydrophobicCount [.P, .H, .P] = 1 := by decide
  rw [h, Nat.mul_one]

theorem faceWord_length (t : ℕ) (ht : 2 ∣ t) : (faceWord t).length = 2 * t := by
  have h := Nat.mul_div_cancel' ht
  simp only [faceWord, repeatWord_length]
  change t / 2 * 4 = 2 * t
  omega

theorem faceWord_count (t : ℕ) (ht : 2 ∣ t) : hydrophobicCount (faceWord t) = t := by
  simp only [faceWord, hydrophobicCount_repeatWord]
  have h : hydrophobicCount [.P, .H, .H, .P] = 2 := by decide
  rw [h, Nat.mul_comm]
  exact Nat.mul_div_cancel' ht

def alpha (Q : ℕ) : ℕ := 2 * Q
def beta (Q : ℕ) : ℕ := 4 * Q + 2
def depth (q Q : ℕ) : ℕ := q * beta Q
def side (q Q : ℕ) : ℕ := depth q Q + 2

theorem depth_even (q Q : ℕ) : 2 ∣ depth q Q := by
  refine ⟨q * (2 * Q + 1), ?_⟩
  simp only [depth, beta]
  ring

theorem depth_square_even (q Q : ℕ) : 2 ∣ depth q Q ^ 2 := by
  simpa [pow_two] using Nat.dvd_mul_right_of_dvd (depth_even q Q) (depth q Q)

theorem depth_square_sub_two_even (q Q : ℕ) : 2 ∣ depth q Q ^ 2 - 2 :=
  Nat.dvd_sub (depth_square_even q Q) (by decide)

def wallUnit (q Q : ℕ) : Sequence :=
  edgeWord (alpha Q) ++ faceWord (depth q Q) ++ edgeWord (beta Q) ++
    faceWord (depth q Q) ++ edgeWord (alpha Q)

def gapWord (q Q : ℕ) : Sequence :=
  edgeWord 2 ++ repeatWord (List.replicate (2 * alpha Q + 4) .P ++ edgeWord 2) (q - 1)

def walls (q Q : ℕ) : Sequence :=
  repeatWord (wallUnit q Q ++ List.replicate (2 * alpha Q) .P) (q - 1) ++
    wallUnit q Q ++ gapWord q Q

def prefixWord (q Q : ℕ) : Sequence :=
  let d := depth q Q
  edgeWord (9 * d + 8) ++ faceWord (d ^ 2) ++ edgeWord d ++ List.replicate 4 .P ++
    repeatWord (faceWord (d ^ 2) ++ List.replicate (d + 9) .P) 3 ++
    faceWord (d ^ 2 - 2) ++ [.P] ++ List.replicate (d ^ 3 + 2) .H ++
    List.replicate (alpha Q + 8) .P

def itemWords (q Q : ℕ) (items : List ℕ) : Sequence :=
  items.flatMap fun a => List.replicate (4 * side q Q) .P ++ faceWord (depth q Q * a)

/-- The complete single binary chain. Long connectors have length 4n. -/
def frameWord (q Q : ℕ) (items : List ℕ) : Sequence :=
  prefixWord q Q ++ walls q Q ++ itemWords q Q items

theorem wallUnit_count (q Q : ℕ) :
    hydrophobicCount (wallUnit q Q) = 2 * alpha Q + beta Q + 2 * depth q Q := by
  simp only [wallUnit, hydrophobicCount_append, edgeWord_count,
    faceWord_count _ (depth_even q Q)]
  omega

theorem gapWord_count (q Q : ℕ) (hq : 0 < q) : hydrophobicCount (gapWord q Q) = 2 * q := by
  simp [gapWord, hydrophobicCount_append, edgeWord_count, hydrophobicCount_repeatWord,
    hydrophobicCount_replicate]
  omega

theorem depth_two_le (q Q : ℕ) (hq : 0 < q) : 2 ≤ depth q Q := by
  dsimp [depth, beta]
  nlinarith

theorem walls_count (q Q : ℕ) (hq : 0 < q) :
    hydrophobicCount (walls q Q) = 2 * depth q Q + 2 * q * depth q Q := by
  have hq' : q - 1 + 1 = q := by omega
  have hu : (q - 1) * (2 * alpha Q + beta Q + 2 * depth q Q) +
      (2 * alpha Q + beta Q + 2 * depth q Q) =
      q * (2 * alpha Q + beta Q + 2 * depth q Q) := by
    calc
      _ = (q - 1 + 1) * (2 * alpha Q + beta Q + 2 * depth q Q) := by ring
      _ = _ := by rw [hq']
  simp only [walls, hydrophobicCount_append, hydrophobicCount_repeatWord,
    hydrophobicCount_replicate, reduceCtorEq, ite_false, Nat.add_zero,
    wallUnit_count, gapWord_count q Q hq]
  rw [hu]
  dsimp [alpha, beta, depth]
  ring

theorem prefixWord_count (q Q : ℕ) (hq : 0 < q) :
    hydrophobicCount (prefixWord q Q) =
      depth q Q ^ 3 + 5 * depth q Q ^ 2 + 10 * depth q Q + 8 := by
  have hd := depth_two_le q Q hq
  have hd2 : 2 ≤ depth q Q ^ 2 := by nlinarith
  have hp : hydrophobicCount [.P] = 0 := by decide
  simp only [prefixWord, hydrophobicCount_append, edgeWord_count,
    faceWord_count _ (depth_square_even q Q),
    faceWord_count _ (depth_square_sub_two_even q Q), hydrophobicCount_repeatWord,
    hydrophobicCount_replicate, hp, reduceCtorEq, ite_false, ite_true]
  omega

theorem itemWords_count (q Q : ℕ) (items : List ℕ) :
    hydrophobicCount (itemWords q Q items) = depth q Q * items.sum := by
  induction items with
  | nil => change hydrophobicCount [] = 0; decide
  | cons a items ih =>
    change hydrophobicCount
      ((List.replicate (4 * side q Q) .P ++ faceWord (depth q Q * a)) ++ itemWords q Q items) = _
    simp [hydrophobicCount_append, hydrophobicCount_replicate,
      faceWord_count _ (Nat.dvd_mul_right_of_dvd (depth_even q Q) a), ih, Nat.mul_add]

/-- Every normalized exact-packing input produces exactly n³ H residues.
Only total volume is needed here; no packing solution is assumed. -/
theorem frameWord_count (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (hsum : items.sum = q * (4 * Q)) :
    hydrophobicCount (frameWord q Q items) = side q Q ^ 3 := by
  rw [frameWord, hydrophobicCount_append, hydrophobicCount_append,
    prefixWord_count q Q hq, walls_count q Q hq, itemWords_count, hsum]
  dsimp [side, depth, beta]
  ring

/-- A well-formed perfect instance obtained from the literal frame word.
This supplies no claim that a fold exists. -/
def frameInstance (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (hsum : items.sum = q * (4 * Q)) : PerfectInstance where
  side := side q Q
  sequence := frameWord q Q items
  count_eq := frameWord_count q Q items hq hsum

theorem wallUnit_length (q Q : ℕ) :
    (wallUnit q Q).length = 6 * alpha Q + 3 * beta Q + 4 * depth q Q := by
  simp [wallUnit, List.length_append, edgeWord_length,
    faceWord_length _ (depth_even q Q)]
  ring

theorem gapWord_length (q Q : ℕ) :
    (gapWord q Q).length = 6 + (q - 1) * (2 * alpha Q + 10) := by
  simp [gapWord, repeatWord_length, edgeWord_length]

theorem walls_length (q Q : ℕ) :
    (walls q Q).length =
      (q - 1) * (6 * alpha Q + 3 * beta Q + 4 * depth q Q + 2 * alpha Q) +
      (6 * alpha Q + 3 * beta Q + 4 * depth q Q) +
      (6 + (q - 1) * (2 * alpha Q + 10)) := by
  simp [walls, repeatWord_length, wallUnit_length, gapWord_length, Nat.add_assoc]

theorem prefixWord_length (q Q : ℕ) (hq : 0 < q) :
    (prefixWord q Q).length =
      depth q Q ^ 3 + 10 * depth q Q ^ 2 + 33 * depth q Q + alpha Q + 62 := by
  have hd := depth_two_le q Q hq
  have hd2 : 2 ≤ depth q Q ^ 2 := by nlinarith
  simp only [prefixWord, List.length_append, List.length_replicate,
    List.length_singleton, repeatWord_length, edgeWord_length,
    faceWord_length _ (depth_square_even q Q),
    faceWord_length _ (depth_square_sub_two_even q Q)]
  omega

theorem itemWords_length (q Q : ℕ) (items : List ℕ) :
    (itemWords q Q items).length =
      items.length * (4 * side q Q) + 2 * depth q Q * items.sum := by
  induction items with
  | nil => simp [itemWords]
  | cons a items ih =>
    change ((List.replicate (4 * side q Q) Residue.P ++ faceWord (depth q Q * a)) ++
      itemWords q Q items).length = _
    simp only [List.length_append, List.length_replicate,
      faceWord_length _ (Nat.dvd_mul_right_of_dvd (depth_even q Q) a), ih,
      List.length_cons, List.sum_cons]
    ring

/-- The reduction word has cubic size in its cube side. Positivity bounds the
number of item connectors; the exact volume equation bounds their total H size.
This is an output-length statement, not a runtime witness. -/
theorem frameWord_length_le (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (hsum : items.sum = q * (4 * Q)) (hpos : ∀ a ∈ items, 0 < a) :
    (frameWord q Q items).length ≤ 100 * side q Q ^ 3 := by
  have hbd : beta Q ≤ depth q Q := by
    simpa only [Nat.one_mul, depth] using
      Nat.mul_le_mul_right (beta Q) (by omega : 1 ≤ q)
  have had : alpha Q ≤ depth q Q := by
    have h : alpha Q ≤ beta Q := by dsimp [alpha, beta]; omega
    omega
  have hqd : q ≤ depth q Q := by
    have h : 1 ≤ beta Q := by dsimp [beta]; omega
    simpa only [Nat.mul_one, depth] using Nat.mul_le_mul_left q h
  have hminus : q - 1 ≤ depth q Q := by omega
  have hka := Nat.mul_le_mul hminus had
  have hkb := Nat.mul_le_mul hminus hbd
  have hkd := Nat.mul_le_mul_right (depth q Q) hminus
  have hw : (walls q Q).length ≤
      17 * depth q Q ^ 2 + 23 * depth q Q + 6 := by
    rw [walls_length]
    nlinarith
  have hs : items.sum ≤ depth q Q := by
    rw [hsum]
    dsimp [depth, beta]
    nlinarith
  have hk : items.length ≤ depth q Q :=
    (List.length_le_sum_of_one_le items (fun a ha => by have := hpos a ha; omega)).trans hs
  have hconnect := Nat.mul_le_mul_right (4 * side q Q) hk
  have hitems := Nat.mul_le_mul_left (2 * depth q Q) hs
  have hi : (itemWords q Q items).length ≤ 6 * depth q Q ^ 2 + 8 * depth q Q := by
    rw [itemWords_length]
    dsimp only [side] at hconnect ⊢
    nlinarith
  rw [frameWord, List.length_append, List.length_append, prefixWord_length q Q hq]
  dsimp only [side]
  nlinarith

/-- A convenient unary parameter size. Later source encodings can dominate this
sum directly, without relying on binary numeric values as their size measure. -/
def parameterSize (q Q : ℕ) (items : List ℕ) : ℕ := q + Q + items.sum + items.length + 1

theorem side_le_parameterSize_square (q Q : ℕ) (items : List ℕ) :
    side q Q ≤ 8 * parameterSize q Q items ^ 2 := by
  have hq : q ≤ parameterSize q Q items := by dsimp [parameterSize]; omega
  have hQ : Q ≤ parameterSize q Q items := by dsimp [parameterSize]; omega
  have hsize : 1 ≤ parameterSize q Q items := by dsimp [parameterSize]; omega
  have hprod := Nat.mul_le_mul hq hQ
  dsimp only [side, depth, beta]
  nlinarith

theorem frameWord_length_polynomial (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (hsum : items.sum = q * (4 * Q)) (hpos : ∀ a ∈ items, 0 < a) :
    (frameWord q Q items).length ≤ 51200 * parameterSize q Q items ^ 6 := by
  have h := frameWord_length_le q Q items hq hsum hpos
  have hp := Nat.pow_le_pow_left (side_le_parameterSize_square q Q items) 3
  calc
    _ ≤ 100 * side q Q ^ 3 := h
    _ ≤ 100 * (8 * parameterSize q Q items ^ 2) ^ 3 := Nat.mul_le_mul_left 100 hp
    _ = _ := by ring

end ProteinFolding.CubicPacking
