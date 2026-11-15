import ProteinFolding.Tetrahedral.ReductionTM2BulkPredicateCorrect

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkPredicate

open Arithmetic BulkArithmetic

theorem endpoint_count_correct (m i j : ℕ) (s : Site) (hs : Grid.point m i = s.val) :
    Arithmetic.eval (fields (m, (i, j)))
      (Arithmetic.count 4 (fun d => cover (.field 0) leftPoint (stepPoint leftPoint d))) =
        (bulkCoverNeighbours m s).card := by
  have hp : evalPoint (fields (m, (i, j))) leftPoint = s.val := (eval_leftPoint _).trans hs
  rw [Arithmetic.eval_count, bulkCoverNeighbours_fast_card]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, bulkFastCoverDirections,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [eval_cover (fields (m, (i, j))) (.field 0) leftPoint (stepPoint leftPoint d)
    s (step s d) hp (eval_stepPoint _ leftPoint s hp d)]
  exact bulkCoverBond_fast_iff m s (step s d)

theorem endpoint_correct (m i j : ℕ) (s : Site) (hs : Grid.point m i = s.val) :
    endpoint (m, (i, j)) = true ↔ (bulkCoverNeighbours m s).card = 1 := by
  change Arithmetic.eval (fields (m, (i, j))) endpointSyntax = true ↔ _
  rw [endpointSyntax, Arithmetic.eval_and_true, eval_site, eval_leftPoint, hs,
    Arithmetic.eval_nat_eq_true, endpoint_count_correct m i j s hs]
  simp only [Arithmetic.eval, s.property, true_and]

theorem endpoint_true_site {m i j : ℕ} (h : endpoint (m, (i, j)) = true) :
    IsLatticeSite (Grid.point m i) := by
  change Arithmetic.eval (fields (m, (i, j))) endpointSyntax = true at h
  rw [endpointSyntax, Arithmetic.eval_and_true, eval_site, eval_leftPoint] at h
  exact h.1

theorem endpoint_guarded_correct (m i j : ℕ) : endpoint (m, (i, j)) = true ↔
    ∃ hs : IsLatticeSite (Grid.point m i), (bulkCoverNeighbours m ⟨Grid.point m i, hs⟩).card = 1 := by
  constructor
  · intro h
    exact ⟨endpoint_true_site h, (endpoint_correct m i j _ rfl).1 h⟩
  · rintro ⟨hs, h⟩
    exact (endpoint_correct m i j _ rfl).2 h

theorem endpoint_inside {m i j : ℕ} (h : endpoint (m, (i, j)) = true) :
    ∃ hs : IsLatticeSite (Grid.point m i), (⟨Grid.point m i, hs⟩ : Site) ∈ bulkInterior m := by
  obtain ⟨hs, hc⟩ := (endpoint_guarded_correct m i j).1 h
  have hn : (bulkCoverNeighbours m ⟨Grid.point m i, hs⟩).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨q, hq⟩ := hn
  exact ⟨hs, (bulkCoverGraph_support m ((mem_bulkCoverNeighbours m _ q).1 hq)).1⟩

end ProteinFolding.Tetrahedral.ReductionTM2.BulkPredicate
