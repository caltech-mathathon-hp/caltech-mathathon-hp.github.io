import ProteinFolding.Common.SAT.MatchingEnumeration
import ProteinFolding.Common.SAT.MatchingGraph

namespace ProteinFolding.ThreeDimensionalMatching.SourceQueries

theorem flatMap_test_singleton {A B : Type} (xs : List A) (p : A → Bool) (g : A → B) :
    xs.flatMap (fun a => if p a then [g a] else []) = (xs.filter p).map g := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases hp : p a <;> simp [hp, ih]

theorem vertexCount_eq (φ : SAT.CNF) : vertexCount φ = 2 * (indexedOccurrences φ).length := by
  unfold vertexCount
  omega

theorem denseTriples_eq_graphTriples (φ : SAT.CNF) :
    denseTriples φ = graphTriples (vertexCount φ)
      (fun x y z => rawRelation φ x.val y.val z.val) := by
  unfold denseTriples graphTriples
  simp only [← List.map_coe_finRange (vertexCount φ), List.flatMap_map]
  congr 1
  funext x
  congr 1
  funext y
  exact flatMap_test_singleton _ _ _

end ProteinFolding.ThreeDimensionalMatching.SourceQueries
