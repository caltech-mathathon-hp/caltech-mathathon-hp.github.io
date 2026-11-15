import Shelf

/-!
Run with `lake env lean checks/Axioms.lean`. Every line of the output should
list only `propext`, `Classical.choice` and `Quot.sound`, the three axioms of
Lean and Mathlib themselves.
-/

open ProteinFolding.Shelf

#print axioms modifiedAccepts_iff
#print axioms normalised_normalise
#print axioms exists_exact_normalise_iff
#print axioms noInstance_rejected
#print axioms reductionCorrect_of
#print axioms perfect_iff_exists_fills
#print axioms hydrophobicCount_shelfWord
#print axioms latticeDistance_clamp_le
#print axioms clamp_eq_of_adj
#print axioms Isolated.on_skeleton
#print axioms tether
#print axioms RunAt.isChain
#print axioms longPath_length_le
#print axioms longPath_free_edges
#print axioms filler_fills_free_edge
#print axioms path_in_free_edge
#print axioms far_edges
#print axioms far_edges_eq
#print axioms far_edges_end
#print axioms fills_edge_direction
#print axioms packing_of_shelf_line
#print axioms shelfAnatomy
#print axioms shelf_of_fills
#print axioms foldGivesPacking
#print axioms perfect_of_walk
#print axioms tokSites_isChain
#print axioms tokSites_nodup
#print axioms tokSites_fits
#print axioms altRun_isChain
#print axioms corePath
#print axioms routes
#print axioms exists_tiling
#print axioms aTokens_linked
#print axioms aTokens_nodup
#print axioms shelfTokens_nodup
#print axioms plain_nodup
#print axioms exists_linkers
#print axioms shelfWord_eq_layoutWord
#print axioms layout_fits
#print axioms layout_isChain
#print axioms layout_nodup
#print axioms exists_good_parts
#print axioms packingGivesFold
#print axioms reductionCorrect
#print axioms normaliseComputable
#print axioms machineWord_eq
#print axioms shelfPairComputable
#print axioms shelfMap_correct
#print axioms shelfMap_polyTime
#print axioms shelfKarp
#print axioms perfectHPStringFold_NPHard
#print axioms perfectHPStringFold_NPComplete
#print axioms hpStringFold_NPComplete

-- The Cook–Levin theorem, and the final theorems with it plugged in.
#print axioms ProteinFolding.SAT.CookLevinUniversal.cookLevin
#print axioms Unconditional.perfectHPStringFold_NPHard
#print axioms Unconditional.perfectHPStringFold_NPComplete
#print axioms Unconditional.hpStringFold_NPComplete
#print axioms Unconditional.TeamRoute.perfectHPStringFold_NPComplete
#print axioms Unconditional.TeamRoute.hpStringFold_NPComplete
