import ProteinFolding.Tetrahedral.NearFieldCanonicalRemainingCross
import ProteinFolding.Tetrahedral.NearFieldCanonicalSeparatorFrameSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalSeparatorTrackSeparation
import ProteinFolding.Tetrahedral.NearFieldTrackFillerSeparation

/-! Unconditional construction of the seven remaining whole-unit relations. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem canonicalRemainingCross (p : ConstructionParameters) : CanonicalRemainingCross p where
  frame_separator := frameWordPiece_canonicalSeparatorPiece_disjoint p
  separator_left := canonicalSeparatorPiece_leftPiece_disjoint p
  separator_item := canonicalSeparatorPiece_itemPiece_disjoint p
  separator_right := canonicalSeparatorPiece_rightPiece_disjoint p
  left_item := canonicalLeftPiece_itemPiece_disjoint p
  left_right := canonicalLeftPiece_rightPiece_disjoint p
  item_right := canonicalItemPiece_rightPiece_disjoint p

end ProteinFolding.Tetrahedral.NearField
