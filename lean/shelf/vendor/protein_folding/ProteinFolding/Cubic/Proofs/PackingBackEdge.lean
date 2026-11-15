import ProteinFolding.Cubic.Proofs.PackingFrameFaces
import ProteinFolding.Cubic.Proofs.PackingEdgeLift

/-! The straight `E_d` component between the first complete back face and
the four-P bridge. Its H path is `(0,1,d+1),...,(0,d,d+1)`; exterior attachments
alternate between the back and left cube normals, beginning and ending back. -/

namespace ProteinFolding.CubicPackingBackEdge

open CubicCertificates CubicPacking CubicPackingLift
open CubicPackingTopFace (point)

def basePos (d : ℕ) (k : Fin d) : Site := point 0 (k.val + 1) (d + 1)

def baseFold (d : ℕ) : Fold cubicLattice d where
  pos := basePos d
  injective_pos := by
    intro i j he
    have hy := congrFun he 1
    apply Fin.ext
    dsimp [basePos, point] at hy
    omega
  consecutive i j hij := by
    change latticeDistance _ _ = 1
    rw [distance_eq]
    dsimp [basePos, point]
    omega

def port (d : ℕ) (k : Fin d) (back : Bool) : Site :=
  if back then point 0 (k.val + 1) (d + 2) else point (-1) (k.val + 1) (d + 1)

def before (d : ℕ) (k : Fin d) : Site := port d k (decide (k.val % 2 = 0))
def after (d : ℕ) (k : Fin d) : Site := port d k (!(decide (k.val % 2 = 0)))

theorem base_inside (d : ℕ) (k : Fin d) : basePos d k ∈ cube (fun _ => 0) (d + 2) := by
  intro c
  have hk := k.isLt
  fin_cases c <;> change 0 ≤ _ ∧ _ < 0 + ((d + 2 : ℕ) : ℤ) <;> dsimp [basePos, point] <;> omega

theorem port_outside (d : ℕ) (k : Fin d) (back : Bool) :
    port d k back ∉ cube (fun _ => 0) (d + 2) := by
  intro hc
  cases back with
  | false => have h := (hc 0).1; change 0 ≤ (-1 : ℤ) at h; omega
  | true =>
    have h := (hc 2).2
    change (d : ℤ) + 2 < 0 + ((d + 2 : ℕ) : ℤ) at h
    omega

theorem port_adj (d : ℕ) (k : Fin d) (back : Bool) :
    cubicLattice.Adj (port d k back) (basePos d k) := by
  change latticeDistance _ _ = 1
  rw [distance_eq]
  cases back <;> simp [port, basePos, point]

theorem ports_separate (d : ℕ) (k : Fin d) : before d k ≠ after d k := by
  intro he
  have hx := congrFun he 0
  by_cases hk : k.val % 2 = 0 <;> simp [before, after, port, hk, point] at hx

theorem ports_link (d : ℕ) (i j : Fin d) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (after d i) (before d j) := by
  change latticeDistance _ _ = 1
  rw [distance_eq]
  by_cases hi : i.val % 2 = 0
  · have hj : j.val % 2 ≠ 0 := by omega
    simp only [before, after, hi, hj, decide_true, decide_false, Bool.not_true,
      Bool.false_eq_true, port, ↓reduceIte]
    dsimp [point]
    omega
  · have hj : j.val % 2 = 0 := by omega
    simp only [before, after, hi, hj, decide_true, decide_false, Bool.not_false,
      port, ↓reduceIte]
    dsimp [point]
    omega

/-- The complete original `E_d=(PHP)^d` word with globally proved injectivity. -/
def edgeFold (d : ℕ) : Fold cubicLattice (edgeWord d).length :=
  edgeLift d (baseFold d) (before d) (after d) (fun _ => 0) (d + 2)
    (base_inside d) (fun k => port_outside d k _) (fun k => port_outside d k _)
    (fun k => port_adj d k _) (fun k => (port_adj d k _).symm)
    (ports_separate d) (ports_link d)

theorem edgeFold_first (d : ℕ) (hd : 0 < d) :
    (edgeFold d).pos (edgeFirstIndex d hd) = point 0 1 (d + 2) := by
  change edgeLiftPos d (baseFold d) (before d) (after d) (edgeFirstIndex d hd) = _
  rw [edgeLiftPos_first]
  simp [before, port, point]

theorem edgeFold_last (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) :
    (edgeFold d).pos (edgeLastIndex d hd) = point 0 d (d + 2) := by
  have hp : (d - 1) % 2 ≠ 0 := by omega
  change edgeLiftPos d (baseFold d) (before d) (after d) _ = _
  rw [edgeLiftPos_last]
  simp only [after, hp, decide_false, Bool.not_false, port, ↓reduceIte]
  apply site_ext <;> dsimp [point] <;> omega

theorem edgeFold_P_outside_cube (d : ℕ) (i : Fin (edgeWord d).length)
    (hi : (edgeWord d).get i = .P) : (edgeFold d).pos i ∉ cube (fun _ => 0) (d + 2) :=
  edgeLiftPos_P_outside d (baseFold d) (before d) (after d) (fun _ => 0) (d + 2)
    (fun k => port_outside d k _) (fun k => port_outside d k _) i hi

theorem edgeFold_hydrophobicSites (d : ℕ) (p : Site) :
    p ∈ hydrophobicSites (edgeWord d) (edgeFold d) ↔
      p 0 = 0 ∧ (1 ≤ p 1 ∧ p 1 ≤ (d : ℤ)) ∧ p 2 = (d : ℤ) + 1 := by
  rw [edgeLift_H_occupation d (baseFold d) (before d) (after d) (edgeFold d) (fun _ => rfl)]
  constructor
  · rintro ⟨k, rfl⟩
    have hk := k.isLt
    dsimp [baseFold, basePos, point]
    omega
  · rintro ⟨hx, hy, hz⟩
    let k : Fin d := ⟨(p 1 - 1).toNat, by omega⟩
    refine ⟨k, ?_⟩
    apply site_ext <;> dsimp [baseFold, basePos, point, k] <;> omega

def Region (d : ℕ) (p : Site) : Prop :=
  (1 ≤ p 1 ∧ p 1 ≤ (d : ℤ)) ∧
    ((p 0 = 0 ∧ p 2 = (d : ℤ) + 1) ∨ (p 0 = -1 ∧ p 2 = (d : ℤ) + 1) ∨
      (p 0 = 0 ∧ p 2 = (d : ℤ) + 2))

theorem edgeFold_region (d : ℕ) (i : Fin (edgeWord d).length) : Region d ((edgeFold d).pos i) := by
  let k := edgeBaseIndex d i
  have hk := k.isLt
  change Region d (decoration (baseFold d) (before d) (after d) k (edgeRole i))
  generalize hr : edgeRole i = r
  fin_cases r
  · dsimp [decoration, before, port]
    split <;> dsimp [Region, point] <;> omega
  · dsimp [decoration, baseFold, basePos, Region, point]
    omega
  · dsimp [decoration, after, port]
    split <;> dsimp [Region, point] <;> omega

theorem edgeFold_first_of_val (d : ℕ) (hd : 0 < d) (i : Fin (edgeWord d).length) (hi : i.val = 0) :
    (edgeFold d).pos i = point 0 1 (d + 2) := by
  have he : i = edgeFirstIndex d hd := Fin.ext hi
  rw [he]
  exact edgeFold_first d hd

theorem edgeFold_last_of_end (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (i : Fin (edgeWord d).length) (hi : i.val + 1 = (edgeWord d).length) :
    (edgeFold d).pos i = point 0 d (d + 2) := by
  have he : i = edgeLastIndex d hd := by
    apply Fin.ext
    change i.val = (edgeWord d).length - 1
    omega
  rw [he]
  exact edgeFold_last d hd heven

theorem edgeFold_faceFold_disjoint (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (f : CubicPackingFrameFaces.Face) (i : Fin (edgeWord d).length)
    (j : Fin (faceWord (d * d)).length) :
    (edgeFold d).pos i ≠ (CubicPackingFrameFaces.faceFold d hd heven f).pos j := by
  have he := edgeFold_region d i
  have hf := CubicPackingFrameFaces.faceFold_region d hd heven f j
  intro hp
  have hx := congrFun hp 0
  have hy := congrFun hp 1
  have hz := congrFun hp 2
  dsimp [Region] at he
  cases f <;> dsimp [CubicPackingFrameFaces.Region] at hf <;> omega

theorem edgeFold_topFold_disjoint (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (edgeWord d).length) (j : Fin (faceWord (d * d - 2)).length) :
    (edgeFold d).pos i ≠ (CubicPackingTopFace.topFold d hd heven).pos j := by
  have he := edgeFold_region d i
  have ht := CubicPackingTopFace.topFold_bounds d hd heven j
  intro hp
  have hy := congrFun hp 1
  dsimp [Region] at he
  omega

theorem backFace_edge_seam (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d)).length) (j : Fin (edgeWord d).length)
    (hi : i.val + 1 = (faceWord (d * d)).length) (hj : j.val = 0) :
    cubicLattice.Adj ((CubicPackingFrameFaces.faceFold d hd heven .back).pos i) ((edgeFold d).pos j) := by
  rw [CubicPackingFrameFaces.faceFold_last_of_end d hd heven .back i hi, edgeFold_first_of_val d hd j hj]
  change latticeDistance _ _ = 1
  rw [distance_eq]
  simp [CubicPackingFrameFaces.lastP, point]

end ProteinFolding.CubicPackingBackEdge
