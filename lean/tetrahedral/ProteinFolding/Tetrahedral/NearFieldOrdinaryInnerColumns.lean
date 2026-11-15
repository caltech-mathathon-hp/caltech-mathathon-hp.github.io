import ProteinFolding.Tetrahedral.NearFieldCanonicalRightPiece
import ProteinFolding.Tetrahedral.NearFieldFrameColumnFamily
import ProteinFolding.Tetrahedral.NearFieldFrameTrackCoreSeparation
import ProteinFolding.Tetrahedral.NearFieldPPPCanonicalColumns

/-! The ordinary selected A columns are actual inner track or exit columns.
Their own chain endpoints are excluded from every internal PPP by index arithmetic. -/

namespace ProteinFolding.Tetrahedral.NearField

def OrdinaryInnerColumn (p : ConstructionParameters) (C : DanglingColumn p.side) : Prop :=
  (∃ (a : ℕ) (hlo : 2 ≤ a) (hhi : a + 3 ≤ p.side),
    C = trackAColumn (m := p.side) (by have h := p.side_ge; omega) a (by omega)) ∨
  (∃ (k : ℕ) (hk : k ≤ p.bins), C = exitCapColumn p k hk)

theorem OrdinaryInnerColumn.edge_data {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) :
    ∃ (G : OctEdgeFrame) (a : ℕ), C.owner = octEdgeZigzag p.side G a ∧
      4 ≤ a ∧ a + 4 ≤ 2 * p.side - 2 ∧ G.j = 3 := by
  rcases hC with ⟨a, hlo, hhi, rfl⟩ | ⟨k, hk, rfl⟩
  · exact ⟨trackEdgeFrame, 2 * a, rfl, by omega, by omega, rfl⟩
  · exact ⟨exitEdgeFrame, 10 * p.exitSlot k + 10, exitCapColumn_owner p k hk,
      by omega, by have h := p.exit_column_triangle_room k; omega, rfl⟩

theorem OrdinaryInnerColumn.owner_reserved_coordinate {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) : tetraCoordinate p.side C.owner.val 3 ≤ -octRadius p.side := by
  obtain ⟨G, a, ho, _, _, hj⟩ := hC.edge_data
  rw [ho, ← hj]
  exact ringEdgePoint_small_coordinate p.side (by have h := p.side_ge; omega) G a

private theorem edgeData_owner_deleted {m : ℕ} (hm : 1 ≤ m) (C : DanglingColumn m)
    (hdata : ∃ (G : OctEdgeFrame) (a : ℕ), C.owner = octEdgeZigzag m G a ∧
      4 ≤ a ∧ a + 4 ≤ 2 * m - 2 ∧ G.j = 3) : C.owner ∈ bulkDeletedEdges m := by
  obtain ⟨G, a, ho, _, hhi, _⟩ := hdata
  rw [ho]
  exact edgeZigzag_mem_deleted hm G a (by omega)

theorem OrdinaryInnerColumn.owner_deleted {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) : C.owner ∈ bulkDeletedEdges p.side := by
  with_reducible exact edgeData_owner_deleted (m := p.side) (by have h := p.side_ge; omega) C hC.edge_data

theorem OrdinaryInnerColumn.edgePPP_clear {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * p.side - 1)
    (hp : C.owner ≠ octEdgeZigzag p.side F r) (hq : C.owner ≠ octEdgeZigzag p.side F (r + 2))
    (s : Fin 3) (n : ℕ) : (edgePPPFold p.side F r).pos s ≠ C.point n := by
  obtain ⟨G, a, ho, hlo, hhi, _⟩ := hC.edge_data
  exact edgePPPFold_ne_inner_edge_column p.side (by have h := p.side_ge; omega)
    F G r a hr hlo hhi C ho hp hq s n

theorem OrdinaryInnerColumn.entryTether_clear {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (k : ℕ) (hk : k ≤ p.bins) (s : Fin (p.entryTether k)) (n : ℕ) :
    (entryTetherFold p k hk).pos s ≠ C.point n := by
  rcases hC with ⟨a, hlo, hhi, rfl⟩ | ⟨l, hl, rfl⟩
  · exact entryTetherFold_ne_trackAColumn p k hk a (by omega) n s
  · exact entryTetherFold_ne_exitCapColumn p k l hk hl s n

theorem OrdinaryInnerColumn.exitTether_clear {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (k : ℕ) (hk : k ≤ p.bins) (s : Fin (p.exitTether k)) (n : ℕ) :
    (exitTetherFold p k hk).pos s ≠ C.point n := by
  rcases hC with ⟨a, hlo, hhi, rfl⟩ | ⟨l, hl, rfl⟩
  · exact exitTetherFold_ne_trackAColumn p k hk a (by omega) n s
  · exact exitTetherFold_ne_exitCapColumn p k l hk hl s n

theorem OrdinaryInnerColumn.frame_clear {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (n : ℕ) (hn : 1 ≤ n) (s : Fin p.frameWord.length) :
    (frameFold p).pos s ≠ C.point n := by
  rcases hC with ⟨a, hlo, hhi, rfl⟩ | ⟨k, hk, rfl⟩
  · exact frameFold_ne_trackAColumn p a (by omega) n hn s
  · exact frameFold_ne_exitCapColumn p k hk n hn s

theorem edgeDimerFold_ne_ordinaryInnerColumn {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * p.side - 1)
    (howners : DimerLinkOwnerExcluded p.side F base q reverse C.owner)
    (i : Fin (dimerChain (q + 1)).length) (n : ℕ) :
    (edgeDimerFold (by have h := p.side_ge; omega : 1 ≤ p.side) F base q reverse hroom).pos i ≠ C.point n := by
  apply edgeDimerFold_ne_column_of_PPP_ne (by have h := p.side_ge; omega : 1 ≤ p.side)
    F base q reverse hroom C _ i n
  intro j hj s r
  have hb := dimerLinkIndex_bounds base reverse j
  exact hC.edgePPP_clear F _ (by omega)
    (by simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using howners j hj 0)
    (by simpa only [Fin.val_one, Nat.mul_one] using howners j hj 1) s r

theorem cappedInterval_ne_ordinaryInnerColumn {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (F : OctEdgeFrame) (base q : ℕ) (hq : 0 < q) (reverse : Bool)
    (hroom : base + 2 * q ≤ 2 * p.side - 1) (D E : DanglingColumn p.side)
    (hD : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hE : E.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (q - 1) 1))
    (howners : DimerLinkOwnerExcluded p.side F base (q - 1) reverse C.owner)
    (i : Fin (capWord (dimerChain q)).length) (n : ℕ) (hn : 1 ≤ n) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      F base q hq reverse hroom D E hD hE).pos i ≠ C.point n := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hr : base + 2 * (q - 1 + 1) ≤ 2 * p.side - 1 := by omega
  apply transportWordFold_property (congrArg capWord (positive_dimer_word q hq))
    (cappedEdgeDimerFold hm F base (q - 1) reverse hr D E hD hE) (fun x => x ≠ C.point n) _ i
  exact cappedEdgeDimerFold_property hm F base (q - 1) reverse hr D E hD hE (fun x => x ≠ C.point n)
    (FarField.dangling_ne_positive_column D.seed_dangling C n hn)
    (fun j => edgeDimerFold_ne_ordinaryInnerColumn hC F base (q - 1) reverse hr howners j n)
    (FarField.dangling_ne_positive_column E.seed_dangling C n hn)

theorem cappedInterval_ne_own_first_innerColumn {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (F : OctEdgeFrame) (base q : ℕ) (hq : 0 < q) (reverse : Bool)
    (hroom : base + 2 * q ≤ 2 * p.side - 1) (D : DanglingColumn p.side)
    (hfirst : C.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hlast : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (q - 1) 1))
    (i : Fin (capWord (dimerChain q)).length) (n : ℕ) (hn : 1 ≤ n) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      F base q hq reverse hroom C D hfirst hlast).pos i ≠ C.point n := by
  apply cappedInterval_ne_ordinaryInnerColumn hC F base q hq reverse hroom C D hfirst hlast _ i n hn
  rw [hfirst]
  exact dimerLinkOwnerExcluded_first (by have h := p.side_ge; omega) F base (q - 1) reverse

theorem cappedInterval_ne_own_last_innerColumn {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (F : OctEdgeFrame) (base q : ℕ) (hq : 0 < q) (reverse : Bool)
    (hroom : base + 2 * q ≤ 2 * p.side - 1) (D : DanglingColumn p.side)
    (hfirst : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hlast : C.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (q - 1) 1))
    (i : Fin (capWord (dimerChain q)).length) (n : ℕ) (hn : 1 ≤ n) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      F base q hq reverse hroom D C hfirst hlast).pos i ≠ C.point n := by
  apply cappedInterval_ne_ordinaryInnerColumn hC F base q hq reverse hroom D C hfirst hlast _ i n hn
  rw [hlast]
  exact dimerLinkOwnerExcluded_last (by have h := p.side_ge; omega) F base (q - 1) reverse

theorem leftLastColumn_ordinary (p : ConstructionParameters) : OrdinaryInnerColumn p (leftLastColumn p) := by
  apply Or.inl
  refine ⟨p.leftFiller - 1, by have h := p.leftFiller_ge; omega, ?_, rfl⟩
  have hs := p.side_eq_track
  have hr := p.rightFiller_ge
  omega

theorem itemFirstColumn_ordinary (p : ConstructionParameters) (k before s : ℕ) (hk : k < p.bins)
    (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    OrdinaryInnerColumn p (itemFirstColumn p k before s hk hs hload) := by
  have hend := itemTrackBase_end_le p k before s hload
  have hroom := p.separator_room (k + 1) (by omega)
  have hstart : p.leftFiller ≤ itemTrackAStart p k before := by
    dsimp [itemTrackAStart, ConstructionParameters.separatorIndex]
    omega
  have hn := p.itemDimers_ge s hs
  apply Or.inl
  refine ⟨itemTrackAStart p k before, by have h := p.leftFiller_ge; omega, ?_, rfl⟩
  change 2 * itemTrackAStart p k before + 2 * p.itemDimers s ≤ 2 * p.separatorIndex (k + 1) at hend
  omega

theorem itemLastColumn_ordinary (p : ConstructionParameters) (k before s : ℕ) (hk : k < p.bins)
    (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    OrdinaryInnerColumn p (itemLastColumn p k before s hk hs hload) := by
  have hend := itemTrackBase_end_le p k before s hload
  have hroom := p.separator_room (k + 1) (by omega)
  have hstart : p.leftFiller ≤ itemTrackAStart p k before := by
    dsimp [itemTrackAStart, ConstructionParameters.separatorIndex]
    omega
  have hn := p.itemDimers_ge s hs
  apply Or.inl
  refine ⟨itemTrackAStart p k before + p.itemDimers s - 1, by have h := p.leftFiller_ge; omega, ?_, rfl⟩
  change 2 * itemTrackAStart p k before + 2 * p.itemDimers s ≤ 2 * p.separatorIndex (k + 1) at hend
  omega

theorem rightFirstColumn_ordinary (p : ConstructionParameters) : OrdinaryInnerColumn p (rightFirstColumn p) := by
  apply Or.inl
  refine ⟨p.separatorIndex p.bins + 2, by omega, ?_, rfl⟩
  have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
  have hr := p.rightFiller_ge
  omega

theorem exitCapColumn_ordinary (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    OrdinaryInnerColumn p (exitCapColumn p k hk) := Or.inr ⟨k, hk, rfl⟩

end ProteinFolding.Tetrahedral.NearField
