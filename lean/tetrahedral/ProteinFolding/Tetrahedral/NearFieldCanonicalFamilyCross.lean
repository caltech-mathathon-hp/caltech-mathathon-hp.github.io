import ProteinFolding.Tetrahedral.NearFieldCanonicalUnitPairwise
import ProteinFolding.Tetrahedral.NearFieldCanonicalRemainingCross
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonFrameSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonSeparatorSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonLeftSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalRingFrameSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalRingTrackSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalRingSeparatorSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalBulkSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalLeftFrameSeparation
import ProteinFolding.Tetrahedral.NearFieldRightFillerFrameClearance
import ProteinFolding.Tetrahedral.NearFieldFrameTrackSeparation

/-! The actual eight-family separation matrix. All terminal, singleton,
ring and bulk relations are supplied by their concrete geometric proofs;
the seven remaining local relation classes stay explicit. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def PiecesCross (ps qs : List PositionedWord) : Prop :=
  ∀ u ∈ ps, ∀ v ∈ qs, WordsDisjoint u v

private theorem pairwiseEight {α : Type*} (R : α → α → Prop) (a b c d e f g h : α)
    (h01 : R a b) (h02 : R a c) (h03 : R a d) (h04 : R a e) (h05 : R a f) (h06 : R a g) (h07 : R a h)
    (h12 : R b c) (h13 : R b d) (h14 : R b e) (h15 : R b f) (h16 : R b g) (h17 : R b h)
    (h23 : R c d) (h24 : R c e) (h25 : R c f) (h26 : R c g) (h27 : R c h)
    (h34 : R d e) (h35 : R d f) (h36 : R d g) (h37 : R d h)
    (h45 : R e f) (h46 : R e g) (h47 : R e h)
    (h56 : R f g) (h57 : R f h) (h67 : R g h) : [a, b, c, d, e, f, g, h].Pairwise R := by
  simp only [List.pairwise_cons, List.forall_mem_cons, list_forall_mem_nil_iff,
    List.Pairwise.nil, and_true]
  exact ⟨⟨h01, h02, h03, h04, h05, h06, h07⟩,
    ⟨⟨h12, h13, h14, h15, h16, h17⟩,
    ⟨⟨h23, h24, h25, h26, h27⟩,
    ⟨⟨h34, h35, h36, h37⟩,
    ⟨⟨h45, h46, h47⟩, ⟨⟨h56, h57⟩, h67⟩⟩⟩⟩⟩⟩

theorem canonicalSingletonPieces_property (p : ConstructionParameters) (P : PositionedWord → Prop)
    (h : ∀ j : Fin 3, P (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j)) :
    ∀ u ∈ canonicalSingletonPieces p, P u := by
  intro u hu
  simp only [canonicalSingletonPieces, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact h 0
  · exact h 1
  · exact h 2

theorem canonicalSeparatorPieces_property (p : ConstructionParameters) (P : PositionedWord → Prop)
    (h : ∀ k : Fin (p.bins + 1), P (canonicalSeparatorPiece p k)) :
    ∀ u ∈ canonicalSeparatorPieces p, P u := by
  intro u hu
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hu
  exact h k

theorem canonicalRingPieces_property (p : ConstructionParameters) (P : PositionedWord → Prop)
    (h : ∀ j : Fin 3, P (canonicalRingWordPiece p j)) : ∀ u ∈ canonicalRingPieces p, P u := by
  intro u hu
  simp only [canonicalRingPieces, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact h 0
  · exact h 1
  · exact h 2

theorem PackedBins.taggedItemPieces_property {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (P : PositionedWord → Prop)
    (h : ∀ k before s, ∀ hk : k < p.bins, ∀ hs : 0 < s, ∀ hload : before + s ≤ p.capacity,
      P (canonicalItemPiece p k before s hk hs hload)) :
    ∀ u ∈ d.taggedItems.map CappedUnit.piece, P u := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  apply d.taggedItems_property P _ v hv
  intro k i
  exact h k.val (itemPrefix (d.parts.get k) i) ((d.parts.get k).get i) (d.bin_lt k)
    (d.part_positive k _ (List.get_mem _ _))
    (by rw [← d.part_load k]; exact itemPrefix_load (d.parts.get k) i)

private theorem singletonList_property (u : PositionedWord) (P : PositionedWord → Prop) (h : P u) :
    ∀ v ∈ [u], P v := by
  intro v hv
  have heq := List.mem_singleton.mp hv
  rw [heq]
  exact h

theorem canonicalPieceFamilies_cross_of_remaining (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) (hrem : CanonicalRemainingCross p) :
    (canonicalPieceFamilies p items d ha).Pairwise PiecesCross := by
  let ss := canonicalSingletonPieces p
  let fs := [frameWordPiece p]
  let es := canonicalSeparatorPieces p
  let ls := [canonicalLeftPiece p]
  let its := d.taggedItems.map CappedUnit.piece
  let rs := [canonicalRightPiece p]
  let gs := canonicalRingPieces p
  let bs := ReductionTM2.BulkScan.cappedRuntimePieces p.side (by have h := p.side_ge; omega) ha
  have h01 : PiecesCross ss fs := by
    apply canonicalSingletonPieces_property p
    intro j
    exact singletonList_property _ _ (frameWordPiece_singletonPiece_disjoint p j).symm
  have h02 : PiecesCross ss es := by
    apply canonicalSingletonPieces_property p
    intro j
    exact canonicalSeparatorPieces_property p _ (fun k => (canonicalSeparatorPiece_singletonPiece_disjoint p k j).symm)
  have h03 : PiecesCross ss ls := by
    apply canonicalSingletonPieces_property p
    intro j
    exact singletonList_property _ _ (canonicalLeftPiece_singletonPiece_disjoint p j).symm
  have h04 : PiecesCross ss its := by
    apply canonicalSingletonPieces_property p
    intro j
    exact d.taggedItemPieces_property _ (fun k before s hk hs hl =>
      (canonicalItemPiece_singletonPiece_disjoint p k before s hk hs hl j).symm)
  have h05 : PiecesCross ss rs := by
    apply canonicalSingletonPieces_property p
    intro j
    exact singletonList_property _ _ (canonicalRightPiece_singletonPiece_disjoint p j).symm
  have h06 : PiecesCross ss gs := by
    apply canonicalSingletonPieces_property p
    intro j
    exact canonicalRingPieces_property p _ (fun k => (canonicalRingWordPiece_singletonPiece_disjoint p k j).symm)
  have h07 : PiecesCross ss bs := by
    apply canonicalSingletonPieces_property p
    intro j
    exact canonicalBulkPieces_property p ha _ (fun k => (canonicalBulkPiece_singletonPiece_disjoint p ha k j).symm)
  have h12 : PiecesCross fs es :=
    singletonList_property _ _ (canonicalSeparatorPieces_property p _ hrem.frame_separator)
  have h13 : PiecesCross fs ls :=
    singletonList_property _ _ (singletonList_property _ _ (canonicalLeftPiece_frameWordPiece_disjoint p).symm)
  have h14 : PiecesCross fs its :=
    singletonList_property _ _ (d.taggedItemPieces_property _ (fun k before s hk hs hl =>
      (canonicalItemPiece_frameWordPiece_disjoint p k before s hk hs hl).symm))
  have h15 : PiecesCross fs rs :=
    singletonList_property _ _ (singletonList_property _ _ (canonicalRightPiece_frameWordPiece_disjoint p).symm)
  have h16 : PiecesCross fs gs :=
    singletonList_property _ _ (canonicalRingPieces_property p _ (fun j => (canonicalRingWordPiece_frameWordPiece_disjoint p j).symm))
  have h17 : PiecesCross fs bs :=
    singletonList_property _ _ (canonicalBulkPieces_property p ha _ (fun j => (canonicalBulkPiece_frameWordPiece_disjoint p ha j).symm))
  have h23 : PiecesCross es ls := by
    apply canonicalSeparatorPieces_property p
    intro k
    exact singletonList_property _ _ (hrem.separator_left k)
  have h24 : PiecesCross es its := by
    apply canonicalSeparatorPieces_property p
    intro k
    exact d.taggedItemPieces_property _ (hrem.separator_item k)
  have h25 : PiecesCross es rs := by
    apply canonicalSeparatorPieces_property p
    intro k
    exact singletonList_property _ _ (hrem.separator_right k)
  have h26 : PiecesCross es gs := by
    apply canonicalSeparatorPieces_property p
    intro k
    exact canonicalRingPieces_property p _ (fun j => (canonicalRingWordPiece_separatorPiece_disjoint p j k).symm)
  have h27 : PiecesCross es bs := by
    apply canonicalSeparatorPieces_property p
    intro k
    exact canonicalBulkPieces_property p ha _ (fun j => (canonicalBulkPiece_separatorPiece_disjoint p ha j k).symm)
  have h34 : PiecesCross ls its := singletonList_property _ _ (d.taggedItemPieces_property _ hrem.left_item)
  have h35 : PiecesCross ls rs := singletonList_property _ _ (singletonList_property _ _ hrem.left_right)
  have h36 : PiecesCross ls gs :=
    singletonList_property _ _ (canonicalRingPieces_property p _ (fun j => (canonicalRingWordPiece_leftPiece_disjoint p j).symm))
  have h37 : PiecesCross ls bs :=
    singletonList_property _ _ (canonicalBulkPieces_property p ha _ (fun j => (canonicalBulkPiece_leftPiece_disjoint p ha j).symm))
  have h45 : PiecesCross its rs := d.taggedItemPieces_property _ (fun k before s hk hs hl =>
    singletonList_property _ _ (hrem.item_right k before s hk hs hl))
  have h46 : PiecesCross its gs := d.taggedItemPieces_property _ (fun k before s hk hs hl =>
    canonicalRingPieces_property p _ (fun j => (canonicalRingWordPiece_itemPiece_disjoint p j k before s hk hs hl).symm))
  have h47 : PiecesCross its bs := d.taggedItemPieces_property _ (fun k before s hk hs hl =>
    canonicalBulkPieces_property p ha _ (fun j => (canonicalBulkPiece_itemPiece_disjoint p ha j k before s hk hs hl).symm))
  have h56 : PiecesCross rs gs :=
    singletonList_property _ _ (canonicalRingPieces_property p _ (fun j => (canonicalRingWordPiece_rightPiece_disjoint p j).symm))
  have h57 : PiecesCross rs bs :=
    singletonList_property _ _ (canonicalBulkPieces_property p ha _ (fun j => (canonicalBulkPiece_rightPiece_disjoint p ha j).symm))
  have h67 : PiecesCross gs bs := canonicalRingPieces_property p _ (fun r =>
    canonicalBulkPieces_property p ha _ (fun j => (canonicalBulkPiece_ringPiece_disjoint p ha j r).symm))
  exact pairwiseEight PiecesCross ss fs es ls its rs gs bs
    h01 h02 h03 h04 h05 h06 h07 h12 h13 h14 h15 h16 h17
    h23 h24 h25 h26 h27 h34 h35 h36 h37 h45 h46 h47 h56 h57 h67

theorem canonicalUnitPieces_pairwise_of_remaining (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) (hrem : CanonicalRemainingCross p) :
    (canonicalUnitPieces p items d ha).Pairwise WordsDisjoint :=
  canonicalUnitPieces_pairwise_of_cross p items d ha (canonicalLocal_terminal_disjoint p ha)
    (canonicalPieceFamilies_cross_of_remaining p items d ha hrem)

end ProteinFolding.Tetrahedral.NearField
