import ProteinFolding.Tetrahedral.NearFieldCanonicalRingTrackSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalBasePieces
import ProteinFolding.Tetrahedral.NearFieldTetherOwners

/-! Whole capped rings avoid the actual capped separators. The existing
tether consumers handle their low prefixes and their higher row corners. -/

namespace ProteinFolding.Tetrahedral.NearField

attribute [local irreducible] ConstructionParameters.side

theorem tetherSourceColumn_reserved_coordinate (p : ConstructionParameters) (t : TetherIndex p) :
    tetraCoordinate p.side (tetherSourceColumn p t).owner.val 3 ≤ -octRadius p.side := by
  rcases t with ⟨b, k⟩
  cases b
  · change tetraCoordinate p.side
      (faceDanglingColumn p.side (entryAnchorA p k.val) (3 * (k.val + 1)) 0
        (entryAnchor_equation p k.val (Nat.le_of_lt_succ k.isLt))).owner.val 3 ≤ _
    rw [entrySource_owner p k.val (Nat.le_of_lt_succ k.isLt)]
    exact ringEdgePoint_small_coordinate p.side (by have h := p.side_ge; omega) entryEdgeFrame _
  · change tetraCoordinate p.side (exitSourceColumn p k.val (Nat.le_of_lt_succ k.isLt)).owner.val 3 ≤ _
    rw [exitSource_owner p k.val (Nat.le_of_lt_succ k.isLt)]
    exact ringEdgePoint_small_coordinate p.side (by have h := p.side_ge; omega) trackEdgeFrame _

theorem tetherTargetColumn_reserved_coordinate (p : ConstructionParameters) (t : TetherIndex p) :
    tetraCoordinate p.side (tetherTargetColumn p t).owner.val 3 ≤ -octRadius p.side := by
  rcases t with ⟨b, k⟩
  cases b
  · change tetraCoordinate p.side (entryTargetColumn p k.val (Nat.le_of_lt_succ k.isLt)).owner.val 3 ≤ _
    rw [entryTarget_owner p k.val (Nat.le_of_lt_succ k.isLt)]
    exact ringEdgePoint_small_coordinate p.side (by have h := p.side_ge; omega) trackEdgeFrame _
  · change tetraCoordinate p.side (exitTargetColumn p k.val).owner.val 3 ≤ _
    rw [exitTarget_owner]
    exact ringEdgePoint_small_coordinate p.side (by have h := p.side_ge; omega) exitEdgeFrame _

private theorem ringSide_linkOwnerExcluded_reserved (m : ℕ) (hm : 3 ≤ m)
    (F : OctEdgeFrame) (hj : F.j ≠ 3) (s : Fin 3) (x : Site)
    (hx : tetraCoordinate m x.val 3 ≤ -octRadius m) :
    DimerLinkOwnerExcluded m (ringSideFrame F s) 1 (m - 3) false x := by
  apply dimerLinkOwnerExcluded_of_not_mem
  intro hmem
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hmem
  have hb := r.isLt
  exact ringEdgePoint_ne_reserved_site m hm (ringSideFrame F s)
    (by rw [ringSideFrame_small]; exact hj) _ (by omega) (by omega) x hx hr

private theorem ringTerminal_ne_reserved_owner (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (hj : F.j ≠ 3) (s : Fin 3) (e : Fin 2) (x : Site)
    (hx : tetraCoordinate m x.val 3 ≤ -octRadius m) : ringTerminalSite m F s e ≠ x := by
  intro heq
  have h := ringTerminal_reserved_coordinate m hm F hj s e
  rw [heq] at h
  omega

theorem ringFold_ne_actual_tether (p : ConstructionParameters) (F : OctEdgeFrame) (hj : F.j ≠ 3)
    (t : TetherIndex p) (r : Fin (dimerChain (3 * (p.side - 2))).length) (s : Fin (tetherCount p t)) :
    (ringFold p.side (by have h := p.side_ge; omega) p.side_even F).pos r ≠ (tetherFold p t).pos s := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have hs := tetherSourceColumn_reserved_coordinate p t
  have ht := tetherTargetColumn_reserved_coordinate p t
  apply ringFold_property p.side hm p.side_even F (fun x => x ≠ (tetherFold p t).pos s) _ _ r
  · intro j i
    let i' : Fin (dimerChain (p.side - 3 + 1)).length :=
      ⟨i.val, by rw [show p.side - 3 + 1 = p.side - 2 by omega]; exact i.isLt⟩
    exact edgeDimerFold_ne_tetherFold p t (ringSideFrame F j) 1 (p.side - 3) false (by omega)
      (fun _ => Or.inr (by rw [ringSideFrame_small]; exact hj))
      (ringSide_linkOwnerExcluded_reserved p.side hm F hj j _ hs)
      (ringSide_linkOwnerExcluded_reserved p.side hm F hj j _ ht) i' s
  · intro c i
    exact edgePPPFold_ne_tetherFold p t (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) 1 (by omega)
      (Or.inr (by change (ringSideFrame F c.castSucc).j ≠ 3; rw [ringSideFrame_small]; exact hj))
      (by rw [ringCorner_start_owner p.side hm F c]
          exact (ringTerminal_ne_reserved_owner p.side hm F hj c.succ 0 _ hs).symm)
      (by rw [ringCorner_end_owner p.side hm F c]
          exact (ringTerminal_ne_reserved_owner p.side hm F hj c.castSucc 1 _ hs).symm)
      (by rw [ringCorner_start_owner p.side hm F c]
          exact (ringTerminal_ne_reserved_owner p.side hm F hj c.succ 0 _ ht).symm)
      (by rw [ringCorner_end_owner p.side hm F c]
          exact (ringTerminal_ne_reserved_owner p.side hm F hj c.castSucc 1 _ ht).symm) i.rev s

private theorem capped_positions {a b : ℕ} (f : Fold tetrahedralLattice a) (g : Fold tetrahedralLattice b)
    (c d : Site) (hsites : foldSites f = ({c} ∪ foldSites g) ∪ {d}) (P : Site → Prop)
    (hc : P c) (hg : ∀ i, P (g.pos i)) (hd : P d) (i : Fin a) : P (f.pos i) := by
  have hmem := (mem_foldSites f _).mpr ⟨i, rfl⟩
  rw [hsites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]
    exact hc
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    rw [← hj]
    exact hg j
  · rw [h]
    exact hd

theorem canonicalRingWordPiece_ne_tetherFold (p : ConstructionParameters) (i : Fin 3)
    (t : TetherIndex p) (r : Fin (canonicalRingWordPiece p i).word.length) (s : Fin (tetherCount p t)) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (tetherFold p t).pos s := by
  have hm : 30 ≤ p.side := by have h := p.side_ge; omega
  apply capped_positions
    (cappedRingFold p.side hm p.side_even (canonicalRingFrame i)
      (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
      (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i))
    (ringFold p.side (by omega) p.side_even (canonicalRingFrame i))
    (canonicalRingColumn p i 0).seed (canonicalRingColumn p i 1).seed
    (cappedRingFold_sites p.side hm p.side_even (canonicalRingFrame i)
      (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
      (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i))
    (fun x => x ≠ (tetherFold p t).pos s) _ _ _ r
  · apply danglingCap_ne_tetherFold p t (canonicalRingColumn p i 0) _ _ s
    · rw [canonicalRingColumn_first_owner]
      exact ringTerminal_ne_reserved_owner p.side (by omega) (canonicalRingFrame i)
        (canonicalRingFrame_small_ne_reserved i) 0 0 _ (tetherSourceColumn_reserved_coordinate p t)
    · rw [canonicalRingColumn_first_owner]
      exact ringTerminal_ne_reserved_owner p.side (by omega) (canonicalRingFrame i)
        (canonicalRingFrame_small_ne_reserved i) 0 0 _ (tetherTargetColumn_reserved_coordinate p t)
  · intro j
    exact ringFold_ne_actual_tether p (canonicalRingFrame i) (canonicalRingFrame_small_ne_reserved i) t j s
  · apply danglingCap_ne_tetherFold p t (canonicalRingColumn p i 1) _ _ s
    · rw [canonicalRingColumn_last_owner]
      exact ringTerminal_ne_reserved_owner p.side (by omega) (canonicalRingFrame i)
        (canonicalRingFrame_small_ne_reserved i) 2 1 _ (tetherSourceColumn_reserved_coordinate p t)
    · rw [canonicalRingColumn_last_owner]
      exact ringTerminal_ne_reserved_owner p.side (by omega) (canonicalRingFrame i)
        (canonicalRingFrame_small_ne_reserved i) 2 1 _ (tetherTargetColumn_reserved_coordinate p t)

theorem canonicalRingWordPiece_ne_entryTether (p : ConstructionParameters) (i : Fin 3) (k : ℕ)
    (hk : k ≤ p.bins) (r : Fin (canonicalRingWordPiece p i).word.length) (s : Fin (p.entryTether k)) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (entryTetherFold p k hk).pos s :=
  canonicalRingWordPiece_ne_tetherFold p i (false, ⟨k, by omega⟩) r s

theorem canonicalRingWordPiece_ne_exitTether (p : ConstructionParameters) (i : Fin 3) (k : ℕ)
    (hk : k ≤ p.bins) (r : Fin (canonicalRingWordPiece p i).word.length) (s : Fin (p.exitTether k)) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (exitTetherFold p k hk).pos s :=
  canonicalRingWordPiece_ne_tetherFold p i (true, ⟨k, by omega⟩) r s

theorem canonicalRingWordPiece_ne_separatorFold (p : ConstructionParameters) (i : Fin 3) (k : ℕ)
    (hk : k ≤ p.bins) (r : Fin (canonicalRingWordPiece p i).word.length) (s : Fin (p.separatorWord k).length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (separatorFold p k hk).pos s := by
  have hm : 30 ≤ p.side := by have h := p.side_ge; omega
  apply separatorFold_property p k hk (fun x => (canonicalRingWordPiece p i).fold.pos r ≠ x) _ _ _ _ _ s
  · intro j
    exact cappedRingFold_ne_other_edgeDimerFold p.side hm p.side_even (canonicalRingFrame i) entryEdgeFrame
      (canonicalRingFrame_small_ne_reserved i) (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
      (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)
      (6 * (k + 1)) 0 false (separatorEntry_room p k hk) r j
  · intro j
    rw [entryTetherWordFold_pos]
    exact canonicalRingWordPiece_ne_entryTether p i k hk r _
  · intro j
    exact cappedRingFold_ne_other_edgeDimerFold p.side hm p.side_even (canonicalRingFrame i) trackEdgeFrame
      (canonicalRingFrame_small_ne_reserved i) (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
      (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)
      (2 * p.separatorIndex k) 1 true (separatorCenter_room p k hk) r j
  · intro j
    rw [exitTetherWordFold_pos]
    exact canonicalRingWordPiece_ne_exitTether p i k hk r _
  · intro j
    exact cappedRingFold_ne_other_edgeDimerFold p.side hm p.side_even (canonicalRingFrame i) exitEdgeFrame
      (canonicalRingFrame_small_ne_reserved i) (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
      (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i)
      (10 * p.exitSlot k + 6) 2 true (separatorExit_room p k) r j

theorem canonicalRingWordPiece_ne_separatorPiece (p : ConstructionParameters) (i : Fin 3)
    (k : Fin (p.bins + 1)) (r : Fin (canonicalRingWordPiece p i).word.length)
    (s : Fin (canonicalSeparatorPiece p k).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (canonicalSeparatorPiece p k).fold.pos s := by
  have hk : k.val ≤ p.bins := by have h := k.isLt; omega
  apply capped_positions
    (cappedSeparatorFold p k.val hk (entryLocalColumn p (some k)) (exitCapColumn p k.val hk) rfl
      (exitCapColumn_owner p k.val hk))
    (separatorFold p k.val hk) (entryLocalColumn p (some k)).seed (exitCapColumn p k.val hk).seed
    (cappedSeparatorFold_sites p k.val hk _ _ rfl (exitCapColumn_owner p k.val hk))
    (fun x => (canonicalRingWordPiece p i).fold.pos r ≠ x) _ _ _ s
  · exact canonicalRingWordPiece_ne_reserved_edge_cap p i entryEdgeFrame rfl
      (entryLocalColumn p (some k)) (6 * (k.val + 1)) rfl r
  · exact canonicalRingWordPiece_ne_separatorFold p i k.val hk r
  · exact canonicalRingWordPiece_ne_reserved_edge_cap p i exitEdgeFrame rfl
      (exitCapColumn p k.val hk) _ (exitCapColumn_owner p k.val hk) r

theorem canonicalRingWordPiece_separatorPiece_disjoint (p : ConstructionParameters) (i : Fin 3)
    (k : Fin (p.bins + 1)) :
    Disjoint (foldSites (canonicalRingWordPiece p i).fold) (foldSites (canonicalSeparatorPiece p k).fold) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalRingWordPiece_ne_separatorPiece p i k)

end ProteinFolding.Tetrahedral.NearField
