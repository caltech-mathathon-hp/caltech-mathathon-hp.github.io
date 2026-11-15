import ProteinFolding.Tetrahedral.PathCoverExtraction
import ProteinFolding.Tetrahedral.BulkEdgeCount
import ProteinFolding.Tetrahedral.ReductionWordCounts

/-! The exact bulk mass supplied by the actual canonical graph's component
paths. Serialization order and its computation remain separate obligations. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

local instance (m : ℕ) : Finite (bulkFiniteGraph m).ConnectedComponent :=
  Finite.of_surjective (bulkFiniteGraph m).connectedComponentMk (fun c => c.exists_rep)

noncomputable local instance (m : ℕ) : Fintype (bulkFiniteGraph m).ConnectedComponent := Fintype.ofFinite _

theorem sum_bulkComponentLength_mass (m : ℕ) (hm : 3 ≤ m)
    (hdegree : ∀ p ∈ bulkInterior m, (bulkCoverNeighbours m p).card ≤ 2) :
    (∑ c : (bulkFiniteGraph m).ConnectedComponent, bulkComponentLength m c) + 24 * m =
      octahedralNumber m + 42 := by
  rw [sum_bulkComponentLength m hdegree]
  exact bulkInterior_card_add hm

theorem ConstructionParameters.reductionWord_count_of_component_mass
    (p : ConstructionParameters) (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity)
    (hdegree : ∀ v ∈ bulkInterior p.side, (bulkCoverNeighbours p.side v).card ≤ 2)
    (hsum : bulkLengths.sum = ∑ c : (bulkFiniteGraph p.side).ConnectedComponent,
      bulkComponentLength p.side c) :
    hydrophobicCount (p.reductionWord items bulkLengths gaps) = octahedralNumber p.side := by
  have hlarge := p.side_ge
  have hmass := sum_bulkComponentLength_mass p.side (by omega) hdegree
  apply p.reductionWord_hydrophobicCount items bulkLengths gaps htotal
  omega

end ProteinFolding.Tetrahedral
