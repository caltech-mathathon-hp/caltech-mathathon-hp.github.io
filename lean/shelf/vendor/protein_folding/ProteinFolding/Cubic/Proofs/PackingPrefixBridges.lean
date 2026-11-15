import ProteinFolding.Cubic.Proofs.PackingRoutingRectangle
import ProteinFolding.Cubic.Proofs.PackingBulkWord
import ProteinFolding.Common.FoldConcatenation
import Mathlib.Tactic.Ring

/-! Explicit all-P connectors between the prefix face words. The coordinates
are the finite polylines of `research/check_simple_construction.py`, with both
adjacent face endpoints excluded. Every connector has its literal word length.
-/

namespace ProteinFolding.CubicPackingPrefixBridges

open CubicCertificates CubicPackingRouting

def fourPoint (d k : ℕ) : Site :=
  if k < 1 then point (-1) d ((d : ℤ)+2)
  else if k < 2 then point (-2) d ((d : ℤ)+2)
  else if k < 3 then point (-2) d ((d : ℤ)+1)
  else point (-2) d d

def fourPos (d : ℕ) (i : Fin 4) : Site := fourPoint d i.val

theorem fourPos_injective (d : ℕ) : Function.Injective (fourPos d) := by
  intro i j he
  have hi := i.isLt; have hj := j.isLt
  unfold fourPos fourPoint at he
  split_ifs at he <;>
    (have hx := congrFun he 0
     have hz := congrFun he 2
     dsimp only [point] at hx hz
     apply Fin.ext
     omega)

theorem fourPos_adjacent (d : ℕ) (i j : Fin 4) (hij : i.val+1=j.val) :
    cubicLattice.Adj (fourPos d i) (fourPos d j) := by
  have hi := i.isLt; have hj := j.isLt
  change latticeDistance (fourPoint _ _) (fourPoint _ _) = 1
  unfold fourPoint
  split_ifs <;> try omega
  all_goals rw [distance_eq]; dsimp only [point]; omega

def fourFold (d : ℕ) : Fold cubicLattice 4 where
  pos := fourPos d
  injective_pos := fourPos_injective d
  consecutive := fourPos_adjacent d

theorem fourPos_first (d : ℕ) (i : Fin 4) (hi : i.val=0) :
    fourPos d i = point (-1) d ((d : ℤ)+2) := by simp [fourPos, fourPoint, hi]

theorem fourPos_last (d : ℕ) (i : Fin 4) (hi : i.val+1=4) :
    fourPos d i = point (-2) d d := by
  have he : i.val=3 := by omega
  simp [fourPos, fourPoint, he]

theorem fourPos_bounds (d : ℕ) (i : Fin 4) :
    fourPos d i 0 ≤ -1 ∧ fourPos d i 1 = d ∧
      (d : ℤ) ≤ fourPos d i 2 ∧ fourPos d i 2 ≤ (d : ℤ)+2 := by
  unfold fourPos fourPoint
  split_ifs <;> dsimp only [point] <;> omega

def turnDepth (d : ℕ) : ℕ := d/2+1

theorem twice_turnDepth (d : ℕ) (heven : d%2=0) : 2*turnDepth d=d+2 := by
  have := Nat.mod_add_div d 2
  dsimp [turnDepth]
  omega

def leftLinkPoint (d k : ℕ) : Site :=
  let t := turnDepth d
  if k < t+1 then point (-2-(k : ℤ)) 1 d
  else if k < t+4 then point (-2-(t : ℤ)) ((t : ℤ)+1-k) d
  else point ((k : ℤ)-2*t-5) (-2) d

def leftLinkPos (d : ℕ) (i : Fin (d+9)) : Site := leftLinkPoint d i.val

theorem leftLinkPos_injective (d : ℕ) : Function.Injective (leftLinkPos d) := by
  intro i j he
  unfold leftLinkPos leftLinkPoint at he
  dsimp only at he
  split_ifs at he <;>
    (have hx := congrFun he 0
     have hy := congrFun he 1
     dsimp only [point] at hx hy
     apply Fin.ext
     omega)

theorem leftLinkPos_adjacent (d : ℕ) (i j : Fin (d+9)) (hij : i.val+1=j.val) :
    cubicLattice.Adj (leftLinkPos d i) (leftLinkPos d j) := by
  change latticeDistance (leftLinkPoint _ _) (leftLinkPoint _ _) = 1
  unfold leftLinkPoint
  dsimp only
  split_ifs <;> try omega
  all_goals rw [distance_eq]; dsimp only [point]; omega

def leftLinkFold (d : ℕ) : Fold cubicLattice (d+9) where
  pos := leftLinkPos d
  injective_pos := leftLinkPos_injective d
  consecutive := leftLinkPos_adjacent d

theorem leftLinkPos_first (d : ℕ) (i : Fin (d+9)) (hi : i.val=0) :
    leftLinkPos d i = point (-2) 1 d := by simp [leftLinkPos, leftLinkPoint, hi]

theorem leftLinkPos_last (d : ℕ) (heven : d%2=0) (i : Fin (d+9)) (hi : i.val+1=d+9) :
    leftLinkPos d i = point 1 (-2) d := by
  have ht := twice_turnDepth d heven
  have h0 : ¬i.val<turnDepth d+1 := by omega
  have h1 : ¬i.val<turnDepth d+4 := by omega
  apply site_ext <;> simp only [leftLinkPos, leftLinkPoint, if_neg h0, if_neg h1, point] <;> omega

theorem leftLinkPos_bounds (d : ℕ) (heven : d%2=0) (i : Fin (d+9)) :
    leftLinkPos d i 2=d ∧ leftLinkPos d i 0≤1 ∧ leftLinkPos d i 1≤1 ∧
      (leftLinkPos d i 0≤-2 ∨ leftLinkPos d i 1=-2) := by
  have hi := i.isLt
  have ht := twice_turnDepth d heven
  have hp : 0<turnDepth d := by dsimp [turnDepth]; omega
  unfold leftLinkPos leftLinkPoint
  split_ifs <;> dsimp only [point] <;> omega

def rotate (d : ℕ) (p : Site) : Site := point ((d : ℤ)+1-p 1) (p 0) (p 2)

theorem rotate_injective (d : ℕ) : Function.Injective (rotate d) := by
  intro p q he
  have hx := congrFun he 0; have hy := congrFun he 1; have hz := congrFun he 2
  apply site_ext <;> dsimp only [rotate, point] at hx hy hz <;> omega

theorem rotate_distance (d : ℕ) (p q : Site) : latticeDistance (rotate d p) (rotate d q)=latticeDistance p q := by
  rw [distance_eq, distance_eq]
  simp only [rotate, point]
  rw [show (d : ℤ)+1-p 1-((d : ℤ)+1-q 1)=-(p 1-q 1) by ring, Int.natAbs_neg]
  omega

def rightLinkFold (d : ℕ) : Fold cubicLattice (d+9) where
  pos i := rotate d (leftLinkPos d i)
  injective_pos := (rotate_injective d).comp (leftLinkPos_injective d)
  consecutive i j hij := by
    change latticeDistance _ _=1
    rw [rotate_distance]
    exact leftLinkPos_adjacent d i j hij

theorem rightLinkFold_first (d : ℕ) (i : Fin (d+9)) (hi : i.val=0) :
    (rightLinkFold d).pos i=point d (-2) d := by
  change rotate d (leftLinkPos d i)=_
  rw [leftLinkPos_first d i hi]
  apply site_ext <;> simp [rotate, point]

theorem rightLinkFold_last (d : ℕ) (heven : d%2=0) (i : Fin (d+9)) (hi : i.val+1=d+9) :
    (rightLinkFold d).pos i=point ((d : ℤ)+3) 1 d := by
  change rotate d (leftLinkPos d i)=_
  rw [leftLinkPos_last d heven i hi]
  apply site_ext <;> simp [rotate, point] <;> omega

theorem rightLinkFold_bounds (d : ℕ) (heven : d%2=0) (i : Fin (d+9)) :
    (rightLinkFold d).pos i 2=d ∧ (d : ℤ)≤(rightLinkFold d).pos i 0 ∧
      (rightLinkFold d).pos i 1≤1 ∧
      ((rightLinkFold d).pos i 1≤-2 ∨ (rightLinkFold d).pos i 0=(d : ℤ)+3) := by
  have hb := leftLinkPos_bounds d heven i
  dsimp only [rightLinkFold, rotate, point]
  omega

def topLinkPoint (d k : ℕ) : Site :=
  if k<5 then point ((d : ℤ)+3) ((d : ℤ)+k) d
  else if k<d+4 then point ((d : ℤ)+3) ((d : ℤ)+4) ((d : ℤ)+4-k)
  else if k<d+8 then point (2*(d : ℤ)+6-k) ((d : ℤ)+4) 1
  else point ((d : ℤ)-1) (2*(d : ℤ)+11-k) 1

def topLinkPos (d : ℕ) (i : Fin (d+9)) : Site := topLinkPoint d i.val

theorem topLinkPos_injective (d : ℕ) (_hd : 2≤d) : Function.Injective (topLinkPos d) := by
  intro i j he
  have hi := i.isLt; have hj := j.isLt
  unfold topLinkPos topLinkPoint at he
  split_ifs at he <;>
    (have hx := congrFun he 0
     have hy := congrFun he 1
     have hz := congrFun he 2
     dsimp only [point] at hx hy hz
     apply Fin.ext
     omega)

theorem topLinkPos_adjacent (d : ℕ) (hd : 2≤d) (i j : Fin (d+9)) (hij : i.val+1=j.val) :
    cubicLattice.Adj (topLinkPos d i) (topLinkPos d j) := by
  change latticeDistance (topLinkPoint _ _) (topLinkPoint _ _) = 1
  unfold topLinkPoint
  split_ifs <;> try omega
  all_goals rw [distance_eq]; dsimp only [point]; omega

def topLinkFold (d : ℕ) (hd : 2≤d) : Fold cubicLattice (d+9) where
  pos := topLinkPos d
  injective_pos := topLinkPos_injective d hd
  consecutive := topLinkPos_adjacent d hd

theorem topLinkPos_first (d : ℕ) (i : Fin (d+9)) (hi : i.val=0) :
    topLinkPos d i=point ((d : ℤ)+3) d d := by simp [topLinkPos, topLinkPoint, hi]

theorem topLinkPos_last (d : ℕ) (hd : 2≤d) (i : Fin (d+9)) (hi : i.val+1=d+9) :
    topLinkPos d i=point ((d : ℤ)-1) ((d : ℤ)+3) 1 := by
  have h0 : ¬i.val<5 := by omega
  have h1 : ¬i.val<d+4 := by omega
  have h2 : ¬i.val<d+8 := by omega
  apply site_ext <;> simp only [topLinkPos, topLinkPoint, if_neg h0, if_neg h1, if_neg h2, point] <;> omega

theorem topLinkPos_bounds (d : ℕ) (hd : 2≤d) (i : Fin (d+9)) :
    0<topLinkPos d i 0 ∧ (d : ℤ)≤topLinkPos d i 1 ∧
      1≤topLinkPos d i 2 ∧ topLinkPos d i 2≤d ∧
      (topLinkPos d i 0=(d : ℤ)+3 ∨ (d : ℤ)+3≤topLinkPos d i 1) := by
  have hi := i.isLt
  unfold topLinkPos topLinkPoint
  split_ifs <;> dsimp only [point] <;> omega

theorem four_left_disjoint (d : ℕ) (hd : 2≤d) (heven : d%2=0) (i : Fin 4) (j : Fin (d+9)) :
    fourPos d i ≠ leftLinkPos d j := by
  intro he
  have hf := fourPos_bounds d i
  have hl := leftLinkPos_bounds d heven j
  have hy := congrFun he 1
  omega

theorem four_right_disjoint (d : ℕ) (hd : 2≤d) (heven : d%2=0) (i : Fin 4) (j : Fin (d+9)) :
    fourPos d i ≠ (rightLinkFold d).pos j := by
  intro he
  have hf := fourPos_bounds d i
  have hr := rightLinkFold_bounds d heven j
  have hx := congrFun he 0
  omega

theorem four_top_disjoint (d : ℕ) (hd : 2≤d) (i : Fin 4) (j : Fin (d+9)) :
    fourPos d i ≠ topLinkPos d j := by
  intro he
  have hf := fourPos_bounds d i
  have ht := topLinkPos_bounds d hd j
  have hx := congrFun he 0
  omega

theorem left_right_disjoint (d : ℕ) (hd : 2≤d) (heven : d%2=0) (i j : Fin (d+9)) :
    leftLinkPos d i ≠ (rightLinkFold d).pos j := by
  intro he
  have hl := leftLinkPos_bounds d heven i
  have hr := rightLinkFold_bounds d heven j
  have hx := congrFun he 0
  omega

theorem left_top_disjoint (d : ℕ) (hd : 2≤d) (heven : d%2=0) (i j : Fin (d+9)) :
    leftLinkPos d i ≠ topLinkPos d j := by
  intro he
  have hl := leftLinkPos_bounds d heven i
  have ht := topLinkPos_bounds d hd j
  have hy := congrFun he 1
  omega

theorem right_top_disjoint (d : ℕ) (hd : 2≤d) (heven : d%2=0) (i j : Fin (d+9)) :
    (rightLinkFold d).pos i ≠ topLinkPos d j := by
  intro he
  have hr := rightLinkFold_bounds d heven i
  have ht := topLinkPos_bounds d hd j
  have hy := congrFun he 1
  omega

theorem fourPos_not_mem_cube (d : ℕ) (i : Fin 4) : fourPos d i ∉ cube (fun _=>0) (d+2) := by
  intro hq
  have hf := fourPos_bounds d i
  have hx := (hq 0).1
  change 0≤fourPos d i 0 at hx
  omega

theorem leftLinkPos_not_mem_cube (d : ℕ) (heven : d%2=0) (i : Fin (d+9)) :
    leftLinkPos d i ∉ cube (fun _=>0) (d+2) := by
  intro hq
  have hl := leftLinkPos_bounds d heven i
  have hx := (hq 0).1; have hy := (hq 1).1
  change 0≤leftLinkPos d i 0 at hx
  change 0≤leftLinkPos d i 1 at hy
  omega

theorem rightLinkFold_not_mem_cube (d : ℕ) (heven : d%2=0) (i : Fin (d+9)) :
    (rightLinkFold d).pos i ∉ cube (fun _=>0) (d+2) := by
  intro hq
  have hr := rightLinkFold_bounds d heven i
  have hx := (hq 0).2; have hy := (hq 1).1
  change (rightLinkFold d).pos i 0 < 0+((d+2 : ℕ):ℤ) at hx
  change 0≤(rightLinkFold d).pos i 1 at hy
  omega

theorem topLinkPos_not_mem_cube (d : ℕ) (hd : 2≤d) (i : Fin (d+9)) :
    topLinkPos d i ∉ cube (fun _=>0) (d+2) := by
  intro hq
  have ht := topLinkPos_bounds d hd i
  have hx := (hq 0).2; have hy := (hq 1).2
  change topLinkPos d i 0 < 0+((d+2 : ℕ):ℤ) at hx
  change topLinkPos d i 1 < 0+((d+2 : ℕ):ℤ) at hy
  omega

theorem fourPos_far_cube (d : ℕ) (i : Fin 4) (q : Site) (hq : q∈cube (fun _=>0) (d+2)) :
    ¬ cubicLattice.Adj (fourPos d i) q := by
  intro ha
  have hx := hq 0; have hz := hq 2
  change latticeDistance (fourPoint d i.val) q=1 at ha
  rw [distance_eq] at ha
  unfold fourPoint at ha
  split_ifs at ha <;> dsimp only [point] at ha <;> dsimp only at hx hz <;> omega

theorem leftLinkPos_far_cube (d : ℕ) (heven : d%2=0) (i : Fin (d+9))
    (q : Site) (hq : q∈cube (fun _=>0) (d+2)) : ¬ cubicLattice.Adj (leftLinkPos d i) q := by
  intro ha
  have hb := leftLinkPos_bounds d heven i
  have hx := hq 0; have hy := hq 1
  change latticeDistance (leftLinkPos d i) q=1 at ha
  rw [distance_eq] at ha
  dsimp only at hx hy
  omega

theorem rightLinkFold_far_cube (d : ℕ) (heven : d%2=0) (i : Fin (d+9))
    (q : Site) (hq : q∈cube (fun _=>0) (d+2)) : ¬ cubicLattice.Adj ((rightLinkFold d).pos i) q := by
  intro ha
  have hb := rightLinkFold_bounds d heven i
  have hx := hq 0; have hy := hq 1
  change latticeDistance ((rightLinkFold d).pos i) q=1 at ha
  rw [distance_eq] at ha
  dsimp only at hx hy
  omega

theorem topLinkPos_far_cube (d : ℕ) (hd : 2≤d) (i : Fin (d+9))
    (q : Site) (hq : q∈cube (fun _=>0) (d+2)) : ¬ cubicLattice.Adj (topLinkPos d i) q := by
  intro ha
  have hb := topLinkPos_bounds d hd i
  have hx := hq 0; have hy := hq 1
  change latticeDistance (topLinkPos d i) q=1 at ha
  rw [distance_eq] at ha
  dsimp only at hx hy
  omega

theorem four_incoming (d : ℕ) (i : Fin 4) (hi : i.val=0) :
    cubicLattice.Adj (point (-1) d ((d : ℤ)+1)) (fourPos d i) := by
  rw [fourPos_first d i hi]
  change latticeDistance _ _=1
  rw [distance_eq]; dsimp only [point]; omega

theorem four_outgoing (d : ℕ) (i : Fin 4) (hi : i.val+1=4) :
    cubicLattice.Adj (fourPos d i) (point (-1) d d) := by
  rw [fourPos_last d i hi]
  change latticeDistance _ _=1
  rw [distance_eq]; dsimp only [point]; omega

theorem left_incoming (d : ℕ) (i : Fin (d+9)) (hi : i.val=0) :
    cubicLattice.Adj (point (-1) 1 d) (leftLinkPos d i) := by
  rw [leftLinkPos_first d i hi]
  change latticeDistance _ _=1
  rw [distance_eq]; dsimp only [point]; omega

theorem left_outgoing (d : ℕ) (heven : d%2=0) (i : Fin (d+9)) (hi : i.val+1=d+9) :
    cubicLattice.Adj (leftLinkPos d i) (point 1 (-1) d) := by
  rw [leftLinkPos_last d heven i hi]
  change latticeDistance _ _=1
  rw [distance_eq]; dsimp only [point]; omega

theorem right_incoming (d : ℕ) (i : Fin (d+9)) (hi : i.val=0) :
    cubicLattice.Adj (point d (-1) d) ((rightLinkFold d).pos i) := by
  rw [rightLinkFold_first d i hi]
  change latticeDistance _ _=1
  rw [distance_eq]; dsimp only [point]; omega

theorem right_outgoing (d : ℕ) (heven : d%2=0) (i : Fin (d+9)) (hi : i.val+1=d+9) :
    cubicLattice.Adj ((rightLinkFold d).pos i) (point ((d : ℤ)+2) 1 d) := by
  rw [rightLinkFold_last d heven i hi]
  change latticeDistance _ _=1
  rw [distance_eq]; dsimp only [point]; omega

theorem top_incoming (d : ℕ) (i : Fin (d+9)) (hi : i.val=0) :
    cubicLattice.Adj (point ((d : ℤ)+2) d d) (topLinkPos d i) := by
  rw [topLinkPos_first d i hi]
  change latticeDistance _ _=1
  rw [distance_eq]; dsimp only [point]; omega

theorem top_outgoing (d : ℕ) (hd : 2≤d) (i : Fin (d+9)) (hi : i.val+1=d+9) :
    cubicLattice.Adj (topLinkPos d i) (point ((d : ℤ)-1) ((d : ℤ)+2) 1) := by
  rw [topLinkPos_last d hd i hi]
  change latticeDistance _ _=1
  rw [distance_eq]; dsimp only [point]; omega

def pWord (N : ℕ) : Sequence := List.replicate N .P

/-- Reinterpret a connector as the literal all-P block of the same length. -/
def asPWord {N : ℕ} (f : Fold cubicLattice N) : Fold cubicLattice (pWord N).length :=
  f.onLength (by simp [pWord])

theorem asPWord_hydrophobicSites {N : ℕ} (f : Fold cubicLattice N) :
    hydrophobicSites (pWord N) (asPWord f) = ∅ := by
  ext p
  have hPH : Residue.P ≠ Residue.H := by decide
  simp [hydrophobicSites, pWord, List.get_eq_getElem, hPH]

def fourWordFold (d : ℕ) : Fold cubicLattice (pWord 4).length := asPWord (fourFold d)
def leftLinkWordFold (d : ℕ) : Fold cubicLattice (pWord (d+9)).length := asPWord (leftLinkFold d)
def rightLinkWordFold (d : ℕ) : Fold cubicLattice (pWord (d+9)).length := asPWord (rightLinkFold d)
def topLinkWordFold (d : ℕ) (hd : 2≤d) : Fold cubicLattice (pWord (d+9)).length := asPWord (topLinkFold d hd)

theorem approach_coordinates (d alpha : ℕ) (i : Fin (alpha+8)) :
    (CubicPackingBulk.approachPos d alpha i 0=d ∨
      CubicPackingBulk.approachPos d alpha i 0=(d : ℤ)+1) ∧
      CubicPackingBulk.approachPos d alpha i 1≤(d : ℤ)+3 := by
  unfold CubicPackingBulk.approachPos CubicPackingBulk.approachPoint
  split_ifs <;> dsimp only [point] <;> omega

theorem topLinkPos_regions (d : ℕ) (hd : 2≤d) (i : Fin (d+9)) :
    topLinkPos d i 0=(d : ℤ)+3 ∨ topLinkPos d i 1=(d : ℤ)+4 ∨
      topLinkPos d i 0=(d : ℤ)-1 := by
  have hi := i.isLt
  unfold topLinkPos topLinkPoint
  split_ifs <;> dsimp only [point] <;> omega

theorem four_approach_disjoint (d alpha : ℕ) (i : Fin 4) (j : Fin (alpha+8)) :
    fourPos d i ≠ CubicPackingBulk.approachPos d alpha j := by
  intro he
  have hf := fourPos_bounds d i
  have ha := approach_coordinates d alpha j
  have hx := congrFun he 0
  omega

theorem left_approach_disjoint (d alpha : ℕ) (hd : 0<d) (heven : d%2=0)
    (i : Fin (d+9)) (j : Fin (alpha+8)) :
    leftLinkPos d i ≠ CubicPackingBulk.approachPos d alpha j := by
  intro he
  have hl := leftLinkPos_bounds d heven i
  have ha := CubicPackingBulk.approachPos_exterior d alpha j
  have hy := congrFun he 1; have hz := congrFun he 2
  omega

theorem right_approach_disjoint (d alpha : ℕ) (hd : 0<d) (heven : d%2=0)
    (i : Fin (d+9)) (j : Fin (alpha+8)) :
    (rightLinkFold d).pos i ≠ CubicPackingBulk.approachPos d alpha j := by
  intro he
  have hr := rightLinkFold_bounds d heven i
  have ha := CubicPackingBulk.approachPos_exterior d alpha j
  have hy := congrFun he 1; have hz := congrFun he 2
  omega

theorem top_approach_disjoint (d alpha : ℕ) (hd : 2≤d) (i : Fin (d+9)) (j : Fin (alpha+8)) :
    topLinkPos d i ≠ CubicPackingBulk.approachPos d alpha j := by
  intro he
  have ht := topLinkPos_regions d hd i
  have ha := approach_coordinates d alpha j
  have hx := congrFun he 0; have hy := congrFun he 1
  omega

theorem outside_bulk_disjoint {N : ℕ} (f : Fold cubicLattice N) (d : ℕ)
    (hd : 0<d) (heven : d%2=0) (hout : ∀ i, f.pos i∉cube (fun _=>0) (d+2)) :
    ∀ i j, f.pos i ≠ (CubicPackingBulk.bulkFold d hd heven).pos j := by
  intro i j he
  apply hout i
  rw [he]
  exact CubicPackingBulk.bulkFold_in_cube d hd heven j

theorem bulkApproach_disjoint_of_parts {N : ℕ} (f : Fold cubicLattice N) (d alpha : ℕ)
    (hd : 0<d) (heven : d%2=0)
    (hout : ∀ i, f.pos i∉cube (fun _=>0) (d+2))
    (happ : ∀ i j, f.pos i ≠ CubicPackingBulk.approachPos d alpha j) :
    ∀ i j, f.pos i ≠ (CubicPackingBulk.bulkApproachFold d alpha hd heven).pos j := by
  intro i j
  cases j using Fin.addCases with
  | left j =>
    simpa only [CubicPackingBulk.bulkApproachFold, Fold.append_pos_left] using
      outside_bulk_disjoint f d hd heven hout i j
  | right j =>
    simpa only [CubicPackingBulk.bulkApproachFold, Fold.append_pos_right] using happ i j

theorem four_bulkApproach_disjoint (d alpha : ℕ) (hd : 0<d) (heven : d%2=0) :
    ∀ i j, (fourFold d).pos i ≠ (CubicPackingBulk.bulkApproachFold d alpha hd heven).pos j :=
  bulkApproach_disjoint_of_parts _ d alpha hd heven (fourPos_not_mem_cube d) (four_approach_disjoint d alpha)

theorem left_bulkApproach_disjoint (d alpha : ℕ) (hd : 0<d) (heven : d%2=0) :
    ∀ i j, (leftLinkFold d).pos i ≠ (CubicPackingBulk.bulkApproachFold d alpha hd heven).pos j :=
  bulkApproach_disjoint_of_parts _ d alpha hd heven (leftLinkPos_not_mem_cube d heven)
    (left_approach_disjoint d alpha hd heven)

theorem right_bulkApproach_disjoint (d alpha : ℕ) (hd : 0<d) (heven : d%2=0) :
    ∀ i j, (rightLinkFold d).pos i ≠ (CubicPackingBulk.bulkApproachFold d alpha hd heven).pos j :=
  bulkApproach_disjoint_of_parts _ d alpha hd heven (rightLinkFold_not_mem_cube d heven)
    (right_approach_disjoint d alpha hd heven)

theorem top_bulkApproach_disjoint (d alpha : ℕ) (hd : 2≤d) (heven : d%2=0) :
    ∀ i j, (topLinkFold d hd).pos i ≠ (CubicPackingBulk.bulkApproachFold d alpha (by omega) heven).pos j :=
  bulkApproach_disjoint_of_parts _ d alpha (by omega) heven (topLinkPos_not_mem_cube d hd)
    (top_approach_disjoint d alpha hd)

end ProteinFolding.CubicPackingPrefixBridges
