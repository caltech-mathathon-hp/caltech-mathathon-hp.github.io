import ProteinFolding.Cubic.Proofs.GeometryMain
import ProteinFolding.Cubic.Proofs.PackingReductionCorrect
import ProteinFolding.Cubic.Proofs.SATPackingComputable
import ProteinFolding.Cubic.Proofs.PerfectToHPComputable
import ProteinFolding.Cubic.Proofs.NPMembership

/-! The four requested Berger--Leighton results, proved against the unchanged
frozen statements. Theorem 3.2 is unconditional. Cook--Levin is the sole explicit
hypothesis of the three complexity results; all subsequent reductions, finite
TM2 runtimes, geometric constructions and NP verifiers are proved. -/

namespace ProteinFolding

theorem perfectIffThreshold_holds : PerfectIffThreshold := by
  intro I
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (CubicGeometry.packsCube_iff_bond_threshold I.sequence f I.side I.count_eq).1 hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, (CubicGeometry.packsCube_iff_bond_threshold I.sequence f I.side I.count_eq).2 hf⟩

/-- PERFECT HP STRING-FOLD is NP-hard, assuming only the explicit Cook--Levin
statement. Every subsequent reduction and its runtime are kernel checked. -/
theorem perfectHPStringFold_NPHard (hCL : SAT.CookLevin) :
    PerfectHPStringFoldNPHard :=
  npHard_of_karpReduces (SATPacking.modifiedBinPackingUnary_NPHard hCL)
    CubicPacking.packingToPerfect_karp

/-- The perfect cubic problem is NP-complete: hardness from the proved
packing reduction, membership from the proved direction-certificate verifier. -/
theorem perfectHPStringFold_NPComplete (hCL : SAT.CookLevin) :
    PerfectHPStringFoldNPComplete :=
  ⟨perfectHPStringFold_inNP, perfectHPStringFold_NPHard hCL⟩

/-- The paper's main theorem: HP STRING-FOLD on the unchanged cubic lattice
is NP-complete, using the actual perfect-to-threshold Karp reduction. -/
theorem hpStringFold_NPComplete (hCL : SAT.CookLevin) :
    HPStringFoldNPComplete :=
  ⟨hpStringFold_inNP, hpNPHard_of_perfectNPHard (perfectHPStringFold_NPHard hCL)⟩

end ProteinFolding
