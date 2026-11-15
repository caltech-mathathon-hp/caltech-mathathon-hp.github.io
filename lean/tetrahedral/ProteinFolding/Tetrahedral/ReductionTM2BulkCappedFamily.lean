import ProteinFolding.Tetrahedral.ReductionTM2BulkCappedPieces

/-! Capping preserves occurrence order and pairwise disjointness for any
global endpoint-column family with the actual bulk owners. A concrete family
is then obtained by choosing the least outside direction at every endpoint. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

open NearField

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable def runtimeEndpoint (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (e : Bool) : Site :=
  if e then runtimeLast m hm ha j else runtimeFirst m hm ha j

theorem runtimeEndpoint_mem_body (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (e : Bool) :
    runtimeEndpoint m hm ha j e ∈ foldSites (runtimePiece m hm ha j).fold := by
  cases e
  · apply (mem_foldSites _ _).2
    exact ⟨⟨0, (runtimePiece m hm ha j).length_pos⟩, (runtimePiece m hm ha j).first_eq _ rfl⟩
  · apply (mem_foldSites _ _).2
    let p := runtimePiece m hm ha j
    let i : Fin p.word.length := ⟨p.word.length - 1, by have h := p.length_pos; omega⟩
    exact ⟨i, p.last_eq i (by dsimp [i]; have h := p.length_pos; omega)⟩

theorem runtimeEndpoints_ne_of_occurrence_ne (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j k : Fin (lengths m).length) (hne : j ≠ k) (e f : Bool) :
    runtimeEndpoint m hm ha j e ≠ runtimeEndpoint m hm ha k f := by
  intro he
  have hj := runtimeEndpoint_mem_body m hm ha j e
  have hk := runtimeEndpoint_mem_body m hm ha k f
  rw [← he] at hk
  exact Finset.disjoint_left.mp (runtimePiece_disjoint m hm ha j k hne) hj hk

theorem cappedRuntimePiece_ne_positive_column (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (C D : DanglingColumn m)
    (hC : C.owner = runtimeFirst m hm ha j) (hD : D.owner = runtimeLast m hm ha j)
    (E : DanglingColumn m) (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (cappedRuntimePieceWithColumns m hm ha j C D hC hD).word.length) :
    (cappedRuntimePieceWithColumns m hm ha j C D hC hD).fold.pos i ≠ E.point n := by
  intro he
  have hmem := (mem_foldSites (cappedRuntimePieceWithColumns m hm ha j C D hC hD).fold _).2 ⟨i, he⟩
  change E.point n ∈ foldSites (cappedRuntimeFoldWithColumns m hm ha j C D hC hD) at hmem
  rw [cappedRuntimeFoldWithColumns_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · have hdang : IsDangling m (E.point n) := by rw [h]; exact C.seed_dangling
    have hz := (E.point_dangling_iff_zero n).1 hdang
    omega
  · exact E.point_outside n (Finset.mem_sdiff.mp (runtimePiece_inside m hm ha j _ h)).1
  · have hdang : IsDangling m (E.point n) := by rw [h]; exact D.seed_dangling
    have hz := (E.point_dangling_iff_zero n).1 hdang
    omega

noncomputable def cappedRuntimePiecesWithColumns (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (E : Fin (lengths m).length → Bool → DanglingColumn m)
    (hE : ∀ j e, (E j e).owner = runtimeEndpoint m hm ha j e) : List PositionedWord :=
  List.ofFn (fun j => cappedRuntimePieceWithColumns m hm ha j (E j false) (E j true) (hE j false) (hE j true))

theorem cappedRuntimePiecesWithColumns_disjoint (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (E : Fin (lengths m).length → Bool → DanglingColumn m)
    (hE : ∀ j e, (E j e).owner = runtimeEndpoint m hm ha j e)
    (j k : Fin (lengths m).length) (hne : j ≠ k) :
    Disjoint
      (foldSites (cappedRuntimePieceWithColumns m hm ha j (E j false) (E j true) (hE j false) (hE j true)).fold)
      (foldSites (cappedRuntimePieceWithColumns m hm ha k (E k false) (E k true) (hE k false) (hE k true)).fold) := by
  have hcap (e f : Bool) : (E j e).seed ≠ (E k f).seed := by
    apply dangling_caps_ne_of_owner_ne m (E j e).owner (E k f).owner (E j e).dir (E k f).dir
      (E j e).owner_mem (E k f).owner_mem (E j e).seed_outside
    rw [hE j e, hE k f]
    exact runtimeEndpoints_ne_of_occurrence_ne m hm ha j k hne e f
  change Disjoint
    (foldSites (cappedRuntimeFoldWithColumns m hm ha j (E j false) (E j true) (hE j false) (hE j true)))
    (foldSites (cappedRuntimeFoldWithColumns m hm ha k (E k false) (E k true) (hE k false) (hE k true)))
  rw [cappedRuntimeFoldWithColumns_sites, cappedRuntimeFoldWithColumns_sites]
  apply Finset.disjoint_left.mpr
  intro p hp hq
  simp only [Finset.mem_union, Finset.mem_singleton] at hp hq
  rcases hp with (rfl | hp) | rfl
  · rcases hq with (h | hq) | h
    · exact hcap false false h
    · exact column_seed_not_mem_body m hm ha k (E j false) hq
    · exact hcap false true h
  · rcases hq with (h | hq) | h
    · apply column_seed_not_mem_body m hm ha j (E k false)
      rw [← h]
      exact hp
    · exact Finset.disjoint_left.mp (runtimePiece_disjoint m hm ha j k hne) hp hq
    · apply column_seed_not_mem_body m hm ha j (E k true)
      rw [← h]
      exact hp
  · rcases hq with (h | hq) | h
    · exact hcap true false h
    · exact column_seed_not_mem_body m hm ha k (E j true) hq
    · exact hcap true true h

theorem cappedRuntimePiecesWithColumns_pairwise (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (E : Fin (lengths m).length → Bool → DanglingColumn m)
    (hE : ∀ j e, (E j e).owner = runtimeEndpoint m hm ha j e) :
    (cappedRuntimePiecesWithColumns m hm ha E hE).Pairwise
      (fun a b => Disjoint (foldSites a.fold) (foldSites b.fold)) := by
  apply List.pairwise_ofFn.mpr
  intro j k hjk
  exact cappedRuntimePiecesWithColumns_disjoint m hm ha E hE j k (ne_of_lt hjk)

theorem cappedRuntimePiecesWithColumns_words (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (E : Fin (lengths m).length → Bool → DanglingColumn m)
    (hE : ∀ j e, (E j e).owner = runtimeEndpoint m hm ha j e) :
    (cappedRuntimePiecesWithColumns m hm ha E hE).map PositionedWord.word =
      (lengths m).map (fun n => capWord (List.replicate n Residue.H)) := by
  rw [cappedRuntimePiecesWithColumns, List.map_ofFn]
  exact List.ofFn_getElem_eq_map (lengths m) (fun n => capWord (List.replicate n Residue.H))

theorem mem_pieceHsupport (ps : List PositionedWord) (p : Site) :
    p ∈ pieceHsupport ps ↔ ∃ q ∈ ps, p ∈ hSupport q.word q.fold := by
  induction ps with
  | nil => simp [pieceHsupport]
  | cons q ps ih => simp [pieceHsupport, ih]

theorem cappedRuntimePiecesWithColumns_hSupport (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (E : Fin (lengths m).length → Bool → DanglingColumn m)
    (hE : ∀ j e, (E j e).owner = runtimeEndpoint m hm ha j e) :
    pieceHsupport (cappedRuntimePiecesWithColumns m hm ha E hE) = bulkInterior m := by
  ext p
  rw [mem_pieceHsupport]
  constructor
  · rintro ⟨q, hq, hp⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    change p ∈ hSupport (capWord (List.replicate ((lengths m).get j) Residue.H))
      (cappedRuntimeFoldWithColumns m hm ha j (E j false) (E j true) (hE j false) (hE j true)) at hp
    rw [cappedRuntimeFoldWithColumns_hSupport] at hp
    exact runtimePiece_inside m hm ha j p hp
  · intro hp
    obtain ⟨j, i, hi⟩ := runtimeFold_covers m hm ha p hp
    refine ⟨cappedRuntimePieceWithColumns m hm ha j (E j false) (E j true) (hE j false) (hE j true),
      List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
    change p ∈ hSupport (capWord (List.replicate ((lengths m).get j) Residue.H))
      (cappedRuntimeFoldWithColumns m hm ha j (E j false) (E j true) (hE j false) (hE j true))
    rw [cappedRuntimeFoldWithColumns_hSupport, runtimePiece_sites, mem_foldSites]
    exact ⟨i, hi⟩

noncomputable def runtimeColumns (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (e : Bool) : DanglingColumn m :=
  if e then lastColumn m hm ha j else firstColumn m hm ha j

theorem runtimeColumns_owner (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (e : Bool) : (runtimeColumns m hm ha j e).owner = runtimeEndpoint m hm ha j e := by
  cases e <;> rfl

noncomputable def cappedRuntimePieces (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    List PositionedWord := cappedRuntimePiecesWithColumns m hm ha (runtimeColumns m hm ha) (runtimeColumns_owner m hm ha)

theorem cappedRuntimePieces_pairwise (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    (cappedRuntimePieces m hm ha).Pairwise (fun a b => Disjoint (foldSites a.fold) (foldSites b.fold)) :=
  cappedRuntimePiecesWithColumns_pairwise m hm ha _ _

theorem cappedRuntimePieces_words (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    (cappedRuntimePieces m hm ha).map PositionedWord.word =
      (lengths m).map (fun n => capWord (List.replicate n Residue.H)) :=
  cappedRuntimePiecesWithColumns_words m hm ha _ _

theorem cappedRuntimePieces_hSupport (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    pieceHsupport (cappedRuntimePieces m hm ha) = bulkInterior m :=
  cappedRuntimePiecesWithColumns_hSupport m hm ha _ _

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan
