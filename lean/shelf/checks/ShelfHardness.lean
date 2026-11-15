import Shelf

/-!
The certificate of the shelf proof. Run with

  lake env lean checks/ShelfHardness.lean

For each result below Lean prints its statement and the axioms its proof depends
on. Every list of axioms should be `[propext, Classical.choice, Quot.sound]`.
The output is kept in `checks/publication-axioms.txt`.

`checks/Axioms.lean` does the same for every lemma of the paper.
-/

-- The statements. They are the team's, and they are not changed here.
#check ProteinFolding.HPStringFoldNPComplete
#print axioms ProteinFolding.HPStringFoldNPComplete
#check ProteinFolding.PerfectHPStringFoldNPHard
#print axioms ProteinFolding.PerfectHPStringFoldNPHard
#check ProteinFolding.PerfectHPStringFoldNPComplete
#print axioms ProteinFolding.PerfectHPStringFoldNPComplete

-- The shelf reduction, with no assumption: both directions, and the machine.
#check ProteinFolding.Shelf.foldGivesPacking
#print axioms ProteinFolding.Shelf.foldGivesPacking
#check ProteinFolding.Shelf.packingGivesFold
#print axioms ProteinFolding.Shelf.packingGivesFold
#check ProteinFolding.Shelf.reductionCorrect
#print axioms ProteinFolding.Shelf.reductionCorrect
#check ProteinFolding.Shelf.shelfMap_correct
#print axioms ProteinFolding.Shelf.shelfMap_correct
#check ProteinFolding.Shelf.shelfMap_polyTime
#print axioms ProteinFolding.Shelf.shelfMap_polyTime
#check ProteinFolding.Shelf.shelfKarp
#print axioms ProteinFolding.Shelf.shelfKarp

-- What we take from the team's library, with no assumption.
#check ProteinFolding.hpStringFold_inNP
#print axioms ProteinFolding.hpStringFold_inNP
#check ProteinFolding.perfectHPStringFold_inNP
#print axioms ProteinFolding.perfectHPStringFold_inNP
#check ProteinFolding.hpNPHard_of_perfectNPHard
#print axioms ProteinFolding.hpNPHard_of_perfectNPHard

-- The Cook–Levin theorem is a hypothesis `hCL` of these results, not an axiom.
#check ProteinFolding.SATPacking.modifiedBinPackingUnary_NPHard
#print axioms ProteinFolding.SATPacking.modifiedBinPackingUnary_NPHard
#check ProteinFolding.Shelf.perfectHPStringFold_NPHard
#print axioms ProteinFolding.Shelf.perfectHPStringFold_NPHard
#check ProteinFolding.Shelf.perfectHPStringFold_NPComplete
#print axioms ProteinFolding.Shelf.perfectHPStringFold_NPComplete
#check ProteinFolding.Shelf.hpStringFold_NPComplete
#print axioms ProteinFolding.Shelf.hpStringFold_NPComplete
