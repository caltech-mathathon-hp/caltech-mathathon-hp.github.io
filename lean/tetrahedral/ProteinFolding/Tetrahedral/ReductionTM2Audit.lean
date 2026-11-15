import ProteinFolding.Tetrahedral.ReductionTM2Guard
import ProteinFolding.Tetrahedral.ReductionTM2BulkOutput
import ProteinFolding.Tetrahedral.ReductionTM2ColourFlags
import ProteinFolding.Tetrahedral.ReductionTM2PrefixColours
import ProteinFolding.Tetrahedral.ReductionTM2Canonical

/-! Kernel dependency audit for the actual reduction computation stages.
The canonical bulk algorithm's geometric correctness is a separate theorem;
the closed machine witnesses below contain no runtime or graph oracle premise. -/

#print axioms ProteinFolding.Tetrahedral.ReductionTM2.preparedInstanceComputable
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.guardedPreparedInstanceComputable
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.rejectingInstance_not_accepts
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.Iterate.computable
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.BoundedWalk.computable
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.Grid.octahedron_has_index
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.BulkPredicate.computable
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.BulkScan.recordsComputable
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.BulkScan.sourceDataComputable
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.ColourFlags.computable
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.Pipeline.computable
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.PrefixColours.reductionComputable
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.Canonical.computable
#print axioms ProteinFolding.Tetrahedral.ReductionTM2.Canonical.flags_head
