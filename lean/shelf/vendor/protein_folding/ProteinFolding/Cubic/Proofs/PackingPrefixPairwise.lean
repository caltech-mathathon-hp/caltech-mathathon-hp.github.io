import ProteinFolding.Cubic.Proofs.PackingPrefixSeparation
import ProteinFolding.Cubic.Proofs.PackingTopBridge

/-! The complete collision matrix of the prefix components. Ordinary E/F
blocks remain within one step of the cube, while the long P links are farther
away; only the explicitly separated bulk approach needs an additional check.
-/

namespace ProteinFolding.CubicPackingPrefixPairwise

open CubicPacking CubicPackingComponentChain CubicPackingPrefixComponents
open CubicPackingPrefixSeparation CubicPackingPrefixBridges CubicPackingBulk
open CubicPackingInitialDisjoint CubicPackingTopBridge CubicPackingPrefix
open CubicPackingFaceBulkDisjoint CubicPackingRouting

section Initial
variable (d : ℕ) (hd : 2≤d) (heven : d%2=0)
  (f : Fold cubicLattice (edgeWord (9*d+8)).length)
  (hlast : ∀ i, i.val+1=(edgeWord (9*d+8)).length → f.pos i=point d 0 ((d : ℤ)+2))
  (hH : hydrophobicSites (edgeWord (9*d+8)) f=Set.range (skeletonPrefixFold d (by omega)).pos)
  (hP : ∀ i, (edgeWord (9*d+8)).get i=.P → f.pos i∉cube (fun _=>0) (d+2))

include hH hP

theorem ordinary_pairwise : (ordinaryBlocks d hd heven f hlast).Pairwise Disjoint := by
  simp [ordinaryBlocks,List.pairwise_cons]
  repeat' constructor
  all_goals first
    | exact initial_backEdge_disjoint d (by omega) f hH hP
    | exact initial_top_disjoint d (by omega) f hH hP hd heven
    | exact initial_face_disjoint d (by omega) f hH hP heven _
    | exact fun i _ he=>bridgePoint_initial_disjoint d hd f hH i he.symm
    | exact CubicPackingBackEdge.edgeFold_topFold_disjoint d hd heven
    | exact CubicPackingBackEdge.edgeFold_faceFold_disjoint d (by omega) heven _
    | exact fun i _ he=>bridgePoint_backEdge_disjoint d i he.symm
    | exact fun _ j=>bridgePoint_top_disjoint d hd heven j
    | exact fun _ j=>bridgePoint_face_disjoint d (by omega) heven _ j
    | exact fun i j he=>CubicPackingFrameFaces.faceFold_topFold_disjoint d hd heven _ j i he.symm
    | exact CubicPackingFrameFaces.faceFolds_disjoint d (by omega) heven .back .left (by decide)
    | exact CubicPackingFrameFaces.faceFolds_disjoint d (by omega) heven .back .bottom (by decide)
    | exact CubicPackingFrameFaces.faceFolds_disjoint d (by omega) heven .back .right (by decide)
    | exact CubicPackingFrameFaces.faceFolds_disjoint d (by omega) heven .left .bottom (by decide)
    | exact CubicPackingFrameFaces.faceFolds_disjoint d (by omega) heven .left .right (by decide)
    | exact CubicPackingFrameFaces.faceFolds_disjoint d (by omega) heven .bottom .right (by decide)

theorem ordinary_bulk_disjoint (alpha : ℕ) :
    ∀ b∈ordinaryBlocks d hd heven f hlast, Disjoint b (bulkBlock d alpha (by omega) heven) := by
  intro b hb
  simp only [ordinaryBlocks,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact initial_bulkApproachWord_disjoint d (by omega) f hH hP alpha hd heven
  · exact edge_bulkApproachWord_disjoint d alpha (by omega) heven
  · exact fun _ j=>bridgePoint_bulkApproachWord_disjoint d alpha hd heven j
  · exact top_bulkApproachWord_disjoint d alpha hd heven
  all_goals exact face_bulkApproachWord_disjoint d alpha (by omega) heven _

end Initial

theorem far_bulk_disjoint (d alpha : ℕ) (hd : 2≤d) (heven : d%2=0) :
    ∀ b∈farBlocks d hd heven, Disjoint b (bulkBlock d alpha (by omega) heven) := by
  intro b hb
  have hfar := far_isFar d hd heven b hb
  have happ : ∀ i j, b.fold.pos i≠approachPos d alpha j := by
    simp only [farBlocks,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl
    · intro i j; exact four_approach_disjoint d alpha (castPIndex i) j
    · intro i j; exact left_approach_disjoint d alpha (by omega) heven (castPIndex i) j
    · intro i j; exact right_approach_disjoint d alpha (by omega) heven (castPIndex i) j
    · intro i j; exact top_approach_disjoint d alpha hd (castPIndex i) j
  intro i j
  apply disjoint_bulkApproachWord_of d alpha (by omega) heven _ ?_ (happ i) j
  intro k he
  apply (hfar i).1
  rw [he]
  exact bulkFold_in_cube d (by omega) heven k

theorem blocks_pairwise (d alpha : ℕ) (hd : 2≤d) (heven : d%2=0)
    (f : Fold cubicLattice (edgeWord (9*d+8)).length)
    (hlast : ∀ i, i.val+1=(edgeWord (9*d+8)).length → f.pos i=point d 0 ((d : ℤ)+2))
    (hH : hydrophobicSites (edgeWord (9*d+8)) f=Set.range (skeletonPrefixFold d (by omega)).pos)
    (hP : ∀ i, (edgeWord (9*d+8)).get i=.P → f.pos i∉cube (fun _=>0) (d+2)) :
    (initialBlock d f hlast::tailBlocks d alpha hd heven).Pairwise Disjoint := by
  have hnear := ordinary_isNear d hd heven f hlast hH
  have hfar := far_isFar d hd heven
  have hord := ordinary_pairwise d hd heven f hlast hH hP
  have hfarPair := far_pairwise d hd heven
  have hcross : ∀ a∈ordinaryBlocks d hd heven f hlast, ∀ b∈farBlocks d hd heven, Disjoint a b := by
    intro a ha b hb
    exact disjoint_symm (far_near_disjoint (hfar b hb) (hnear a ha))
  have hcombined : (ordinaryBlocks d hd heven f hlast++farBlocks d hd heven).Pairwise Disjoint :=
    List.pairwise_append.mpr ⟨hord,hfarPair,hcross⟩
  have hbulk : ∀ a∈ordinaryBlocks d hd heven f hlast++farBlocks d hd heven,
      Disjoint a (bulkBlock d alpha (by omega) heven) := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact ordinary_bulk_disjoint d hd heven f hlast hH hP alpha a ha
    · exact far_bulk_disjoint d alpha hd heven a ha
  have hall : ((ordinaryBlocks d hd heven f hlast++farBlocks d hd heven)++
      [bulkBlock d alpha (by omega) heven]).Pairwise Disjoint := by
    apply List.pairwise_append.mpr
    refine ⟨hcombined,by simp,?_⟩
    intro a ha b hb
    have he : b=bulkBlock d alpha (by omega) heven := by simpa only [List.mem_singleton] using hb
    rw [he]
    exact hbulk a ha
  exact hall.perm (regroup_perm d alpha hd heven f hlast) (fun h=>disjoint_symm h)

end ProteinFolding.CubicPackingPrefixPairwise
