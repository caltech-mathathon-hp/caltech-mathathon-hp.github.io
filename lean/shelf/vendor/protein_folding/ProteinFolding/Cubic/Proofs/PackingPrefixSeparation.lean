import ProteinFolding.Cubic.Proofs.PackingPrefixComponents
import ProteinFolding.Cubic.Proofs.PackingInitialDisjoint

/-! Uniform separation of the distant P connectors from all ordinary
decorated components, together with a convenient regrouping of the literal
prefix components for the global pairwise-disjointness proof. -/

namespace ProteinFolding.CubicPackingPrefixSeparation

open CubicPacking CubicPackingComponentChain CubicPackingPrefixComponents
open CubicPackingPrefixBridges CubicPackingAttachments CubicPackingInitialDisjoint
open CubicPackingPrefix CubicPackingRouting CubicPackingBulk

def IsNear (d : ℕ) (b : Block) : Prop := ∀ i, NearCube d (b.fold.pos i)
def IsFar (d : ℕ) (b : Block) : Prop := ∀ i, b.fold.pos i∉cube (fun _=>0) (d+2) ∧
  ∀ q∈cube (fun _=>0) (d+2), ¬cubicLattice.Adj (b.fold.pos i) q

theorem disjoint_symm {a b : Block} (h : Disjoint a b) : Disjoint b a :=
  fun i j he=>h j i he.symm

theorem far_near_disjoint {d : ℕ} {a b : Block} (ha : IsFar d a) (hb : IsNear d b) : Disjoint a b := by
  intro i j he
  have hn := hb j
  rw [←he] at hn
  rcases hn with hn | ⟨q,hq,hn⟩
  · exact (ha i).1 hn
  · exact (ha i).2 q hq hn

def castPIndex {N : ℕ} (i : Fin (pWord N).length) : Fin N := Fin.cast (by simp [pWord]) i

theorem four_isFar (d : ℕ) : IsFar d (fourBlock d) := by
  intro i
  exact ⟨fourPos_not_mem_cube d (castPIndex i),fourPos_far_cube d (castPIndex i)⟩

theorem left_isFar (d : ℕ) (heven : d%2=0) : IsFar d (leftLinkBlock d heven) := by
  intro i
  exact ⟨leftLinkPos_not_mem_cube d heven (castPIndex i),leftLinkPos_far_cube d heven (castPIndex i)⟩

theorem right_isFar (d : ℕ) (heven : d%2=0) : IsFar d (rightLinkBlock d heven) := by
  intro i
  exact ⟨rightLinkFold_not_mem_cube d heven (castPIndex i),rightLinkFold_far_cube d heven (castPIndex i)⟩

theorem top_isFar (d : ℕ) (hd : 2≤d) : IsFar d (topLinkBlock d hd) := by
  intro i
  exact ⟨topLinkPos_not_mem_cube d hd (castPIndex i),topLinkPos_far_cube d hd (castPIndex i)⟩

theorem face_isNear (d : ℕ) (hd : 0<d) (heven : d%2=0) (f : CubicPackingFrameFaces.Face) :
    IsNear d (faceBlock d hd heven f) := by
  apply faceWord_near_cube _ d (CubicPackingFrameFaces.faceLength_even d heven)
  intro i hi
  apply face_H_inside d f
  exact (CubicPackingFrameFaces.faceFold_hydrophobicSites d hd heven f _).mp ⟨i,hi,rfl⟩

theorem edge_isNear (d : ℕ) (hd : 0<d) (heven : d%2=0) : IsNear d (edgeBlock d hd heven) := by
  apply edgeWord_near_cube d d
  intro i hi
  apply edge_H_inside d
  exact (CubicPackingBackEdge.edgeFold_hydrophobicSites d _).mp ⟨i,hi,rfl⟩

theorem top_isNear (d : ℕ) (hd : 2≤d) (heven : d%2=0) : IsNear d (topBlock d hd heven) := by
  apply faceWord_near_cube _ d (CubicPackingTopFace.topLength_even d heven)
  intro i hi
  apply top_H_inside d
  exact (CubicPackingTopFace.topFold_hydrophobicSites d hd heven _).mp ⟨i,hi,rfl⟩

theorem single_isNear (d : ℕ) (hd : 0<d) : IsNear d (singleBlock d) := by
  intro i
  right
  refine ⟨upperHole d, ?_, initial_bulk_seam d⟩
  intro k
  fin_cases k <;> dsimp [upperHole, point] <;> omega

theorem initial_isNear (d : ℕ) (hd : 0<d)
    (f : Fold cubicLattice (edgeWord (9*d+8)).length) (hlast)
    (hH : hydrophobicSites (edgeWord (9*d+8)) f=Set.range (skeletonPrefixFold d hd).pos) :
    IsNear d (initialBlock d f hlast) := by
  apply edgeWord_near_cube _ d
  intro i hi
  exact (initial_H_skeleton d hd f hH i hi).1

def ordinaryBlocks (d : ℕ) (hd : 2≤d) (heven : d%2=0)
    (f : Fold cubicLattice (edgeWord (9*d+8)).length)
    (hlast : ∀ i, i.val+1=(edgeWord (9*d+8)).length → f.pos i=point d 0 ((d : ℤ)+2)) : List Block :=
  [initialBlock d f hlast,edgeBlock d (by omega) heven,singleBlock d,topBlock d hd heven,
   faceBlock d (by omega) heven .back,faceBlock d (by omega) heven .left,
   faceBlock d (by omega) heven .bottom,faceBlock d (by omega) heven .right]

def farBlocks (d : ℕ) (hd : 2≤d) (heven : d%2=0) : List Block :=
  [fourBlock d,leftLinkBlock d heven,rightLinkBlock d heven,topLinkBlock d hd]

theorem ordinary_isNear (d : ℕ) (hd : 2≤d) (heven : d%2=0)
    (f : Fold cubicLattice (edgeWord (9*d+8)).length) (hlast)
    (hH : hydrophobicSites (edgeWord (9*d+8)) f=Set.range (skeletonPrefixFold d (by omega)).pos) :
    ∀ b∈ordinaryBlocks d hd heven f hlast, IsNear d b := by
  intro b hb
  simp only [ordinaryBlocks,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact initial_isNear d (by omega) f hlast hH
  · exact edge_isNear d (by omega) heven
  · exact single_isNear d (by omega)
  · exact top_isNear d hd heven
  all_goals exact face_isNear d (by omega) heven _

theorem far_isFar (d : ℕ) (hd : 2≤d) (heven : d%2=0) : ∀ b∈farBlocks d hd heven, IsFar d b := by
  intro b hb
  simp only [farBlocks,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl
  · exact four_isFar d
  · exact left_isFar d heven
  · exact right_isFar d heven
  · exact top_isFar d hd

theorem far_pairwise (d : ℕ) (hd : 2≤d) (heven : d%2=0) : (farBlocks d hd heven).Pairwise Disjoint := by
  simp [farBlocks,List.pairwise_cons,List.forall_mem_cons]
  refine ⟨⟨?_,?_,?_⟩,⟨?_,?_⟩,?_⟩
  · intro i j; exact four_left_disjoint d hd heven (castPIndex i) (castPIndex j)
  · intro i j; exact four_right_disjoint d hd heven (castPIndex i) (castPIndex j)
  · intro i j; exact four_top_disjoint d hd (castPIndex i) (castPIndex j)
  · intro i j; exact left_right_disjoint d hd heven (castPIndex i) (castPIndex j)
  · intro i j; exact left_top_disjoint d hd heven (castPIndex i) (castPIndex j)
  · intro i j; exact right_top_disjoint d hd heven (castPIndex i) (castPIndex j)

theorem regroup_perm (d alpha : ℕ) (hd : 2≤d) (heven : d%2=0)
    (f : Fold cubicLattice (edgeWord (9*d+8)).length) (hlast) :
    ((ordinaryBlocks d hd heven f hlast++farBlocks d hd heven)++[bulkBlock d alpha (by omega) heven]).Perm
      (initialBlock d f hlast::tailBlocks d alpha hd heven) := by
  classical
  apply List.perm_iff_count.mpr
  intro b
  simp only [ordinaryBlocks,farBlocks,tailBlocks,List.count_append,List.count_cons,List.count_nil]
  omega

end ProteinFolding.CubicPackingPrefixSeparation
