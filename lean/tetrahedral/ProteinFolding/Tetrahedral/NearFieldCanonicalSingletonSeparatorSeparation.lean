import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonReservedSeparation
import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly
import ProteinFolding.Tetrahedral.NearFieldCanonicalBasePieces
import ProteinFolding.Tetrahedral.NearFieldCappedSeparatorFamily

/-! Every actual complete separator avoids each standalone PHP unit. The
tether part uses the existing cap-owner theorem, including height zero. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem outsideFold_ne_inside {m n : ℕ} (f : Fold tetrahedralLattice n)
    (hout : ∀ r, f.pos r ∉ octahedron m) (x : Site) (hx : x ∈ octahedron m) (r : Fin n) :
    f.pos r ≠ x := fun heq => hout r (heq.symm ▸ hx)

theorem singletonOwner_not_mem_separator_hSupport (p : ConstructionParameters) (k : ℕ)
    (hk : k ≤ p.bins) (j : Fin 3) :
    canonicalSingletonOwner p.side j ∉ hSupport (p.separatorWord k) (separatorFold p k hk) := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have hE := singletonOwner_not_mem_reservedHsites p.side hm j entryEdgeFrame rfl (6 * (k + 1)) 0
  have hC := singletonOwner_not_mem_reservedHsites p.side hm j trackEdgeFrame rfl (2 * p.separatorIndex k) 1
  have hX := singletonOwner_not_mem_reservedHsites p.side hm j exitEdgeFrame rfl (10 * p.exitSlot k + 6) 2
  rw [separatorFold_hSupport]
  intro hmem
  simp only [Finset.mem_union] at hmem
  rcases hmem with (h | h) | h
  · exact hE h
  · exact hC h
  · exact hX h

theorem separatorFold_ne_singletonOwner (p : ConstructionParameters) (k : ℕ)
    (hk : k ≤ p.bins) (j : Fin 3) (i : Fin (p.separatorWord k).length) :
    (separatorFold p k hk).pos i ≠ canonicalSingletonOwner p.side j := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have hin := canonicalSingletonOwner_mem p.side (by omega) j
  apply separatorFold_property p k hk (fun x => x ≠ canonicalSingletonOwner p.side j) _ _ _ _ _ i
  · exact edgeDimerFold_ne_octSite_of_not_mem_Hsites (by omega : 1 ≤ p.side)
      entryEdgeFrame (6 * (k + 1)) 0 false (separatorEntry_room p k hk) _ hin
      (singletonOwner_not_mem_reservedHsites p.side hm j entryEdgeFrame rfl _ _)
  · intro r
    rw [entryTetherWordFold_pos]
    exact outsideFold_ne_inside (entryTetherFold p k hk) (entryTetherFold_outside p k hk) _ hin _
  · exact edgeDimerFold_ne_octSite_of_not_mem_Hsites (by omega : 1 ≤ p.side)
      trackEdgeFrame (2 * p.separatorIndex k) 1 true (separatorCenter_room p k hk) _ hin
      (singletonOwner_not_mem_reservedHsites p.side hm j trackEdgeFrame rfl _ _)
  · intro r
    rw [exitTetherWordFold_pos]
    exact outsideFold_ne_inside (exitTetherFold p k hk) (exitTetherFold_outside p k hk) _ hin _
  · exact edgeDimerFold_ne_octSite_of_not_mem_Hsites (by omega : 1 ≤ p.side)
      exitEdgeFrame (10 * p.exitSlot k + 6) 2 true (separatorExit_room p k) _ hin
      (singletonOwner_not_mem_reservedHsites p.side hm j exitEdgeFrame rfl _ _)

theorem separatorFold_ne_singletonCap (p : ConstructionParameters) (k : ℕ)
    (hk : k ≤ p.bins) (j : Fin 3) (last : Bool) (i : Fin (p.separatorWord k).length) :
    (separatorFold p k hk).pos i ≠
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) j last).seed :=
  separatorFold_ne_cap_of_owner_not_mem_hSupport p k hk _ (canonicalSingletonOwner_inA p.side j)
    (singletonOwner_not_mem_separator_hSupport p k hk j) i

theorem cappedSeparatorFold_ne_singletonOwner (p : ConstructionParameters) (k : ℕ)
    (hk : k ≤ p.bins) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (j : Fin 3) (i : Fin (capWord (p.separatorWord k)).length) :
    (cappedSeparatorFold p k hk C D hC hD).pos i ≠ canonicalSingletonOwner p.side j := by
  have hin := canonicalSingletonOwner_mem p.side (by have h := p.side_ge; omega) j
  exact frameTrack_property_of_capped_sites (cappedSeparatorFold p k hk C D hC hD)
    (separatorFold p k hk) C.seed D.seed (cappedSeparatorFold_sites p k hk C D hC hD)
    (fun x => x ≠ canonicalSingletonOwner p.side j)
    (fun heq => C.seed_dangling.1 (heq.symm ▸ hin))
    (separatorFold_ne_singletonOwner p k hk j)
    (fun heq => D.seed_dangling.1 (heq.symm ▸ hin)) i

theorem cappedSeparatorFold_ne_singletonCap (p : ConstructionParameters) (k : ℕ)
    (hk : k ≤ p.bins) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (j : Fin 3) (last : Bool) (i : Fin (capWord (p.separatorWord k)).length) :
    (cappedSeparatorFold p k hk C D hC hD).pos i ≠
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) j last).seed := by
  let E := canonicalSingletonColumn p.side (by have h := p.side_ge; omega) j last
  have hCm : C.owner ≠ E.owner := by
    rw [hC]
    exact (singletonOwner_ne_reservedEdge p.side (by have h := p.side_ge; omega) j
      entryEdgeFrame rfl _).symm
  have hDm : D.owner ≠ E.owner := by
    rw [hD]
    exact (singletonOwner_ne_reservedEdge p.side (by have h := p.side_ge; omega) j
      exitEdgeFrame rfl _).symm
  exact frameTrack_property_of_capped_sites (cappedSeparatorFold p k hk C D hC hD)
    (separatorFold p k hk) C.seed D.seed (cappedSeparatorFold_sites p k hk C D hC hD)
    (fun x => x ≠ E.seed)
    (dangling_caps_ne_of_owner_ne p.side C.owner E.owner C.dir E.dir C.owner_mem E.owner_mem C.seed_outside hCm)
    (separatorFold_ne_singletonCap p k hk j last)
    (dangling_caps_ne_of_owner_ne p.side D.owner E.owner D.dir E.dir D.owner_mem E.owner_mem D.seed_outside hDm) i

theorem canonicalSeparatorPiece_ne_singletonPiece (p : ConstructionParameters)
    (k : Fin (p.bins + 1)) (j : Fin 3) (i : Fin (canonicalSeparatorPiece p k).word.length)
    (s : Fin (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).word.length) :
    (canonicalSeparatorPiece p k).fold.pos i ≠
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).fold.pos s := by
  have hk : k.val ≤ p.bins := by have h := k.isLt; omega
  let C := entryLocalColumn p (some k)
  let D := exitCapColumn p k.val hk
  intro heq
  have hmem := (mem_foldSites
    (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).fold _).mpr ⟨s, heq.symm⟩
  rw [canonicalSingletonPiece_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact cappedSeparatorFold_ne_singletonCap p k.val hk C D rfl (exitCapColumn_owner p k.val hk) j false i h
  · exact cappedSeparatorFold_ne_singletonOwner p k.val hk C D rfl (exitCapColumn_owner p k.val hk) j i h
  · exact cappedSeparatorFold_ne_singletonCap p k.val hk C D rfl (exitCapColumn_owner p k.val hk) j true i h

theorem canonicalSeparatorPiece_singletonPiece_disjoint (p : ConstructionParameters)
    (k : Fin (p.bins + 1)) (j : Fin 3) :
    WordsDisjoint (canonicalSeparatorPiece p k)
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalSeparatorPiece_ne_singletonPiece p k j)

end ProteinFolding.Tetrahedral.NearField
