import ProteinFolding.Tetrahedral.NearFieldSeparatorCapSupport
import ProteinFolding.Tetrahedral.NearFieldSeparatorTetherClearance
import ProteinFolding.Tetrahedral.NearFieldFrameTrackCoreSeparation

/-! Every tether endpoint is an H of its actual separator. This removes
any endpoint-colour restriction from external cap and site clearance. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

private theorem not_mem_of_subset {s t : Finset Site} {x : Site}
    (hst : s ⊆ t) (hx : x ∉ t) : x ∉ s := fun hs => hx (hst hs)

private theorem outside_ne_inside {m : ℕ} (x y : Site)
    (hx : x ∉ octahedron m) (hy : y ∈ octahedron m) : x ≠ y := by
  intro heq
  exact hx (heq.symm ▸ hy)

private theorem column_seed_ne_inside {m : ℕ} (C : DanglingColumn m) (x : Site)
    (hx : x ∈ octahedron m) : C.seed ≠ x :=
  outside_ne_inside C.seed x C.seed_outside hx

private theorem column_seeds_ne_of_owner_mem_not_mem {m : ℕ} (s : Finset Site)
    (C D : DanglingColumn m) (hC : C.owner ∈ s) (hD : D.owner ∉ s) : C.seed ≠ D.seed := by
  apply dangling_caps_ne_of_owner_ne m C.owner D.owner C.dir D.dir
    C.owner_mem D.owner_mem C.seed_outside
  intro heq
  exact hD (heq ▸ hC)

theorem separatorEntryHsites_subset_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0 ⊆
      hSupport (p.separatorWord k) (separatorFold p k hk) := by
  rw [separatorFold_hSupport]
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem separatorCenterHsites_subset_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k) 1 ⊆
      hSupport (p.separatorWord k) (separatorFold p k hk) := by
  rw [separatorFold_hSupport]
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)

theorem separatorExitHsites_subset_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 ⊆
      hSupport (p.separatorWord k) (separatorFold p k hk) := by
  rw [separatorFold_hSupport]
  intro x hx
  exact Finset.mem_union_right _ hx

theorem separator_tetherSource_mem_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) (b : Bool) :
    (tetherSourceColumn p (b, ⟨k, by omega⟩)).owner ∈
      hSupport (p.separatorWord k) (separatorFold p k hk) := by
  cases b
  · change (faceDanglingColumn p.side (entryAnchorA p k) (3 * (k + 1)) 0 _).owner ∈ _
    rw [entrySource_owner p k hk]
    apply separatorEntryHsites_subset_hSupport p k hk
    exact Finset.mem_image.mpr ⟨⟨1, by decide⟩, Finset.mem_univ _, rfl⟩
  · change (exitSourceColumn p k hk).owner ∈ _
    rw [exitSource_owner p k hk]
    apply separatorCenterHsites_subset_hSupport p k hk
    exact Finset.mem_image.mpr ⟨⟨3, by decide⟩, Finset.mem_univ _, rfl⟩

theorem separator_tetherTarget_mem_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) (b : Bool) :
    (tetherTargetColumn p (b, ⟨k, by omega⟩)).owner ∈
      hSupport (p.separatorWord k) (separatorFold p k hk) := by
  cases b
  · change (entryTargetColumn p k hk).owner ∈ _
    rw [entryTarget_owner p k hk]
    apply separatorCenterHsites_subset_hSupport p k hk
    exact Finset.mem_image.mpr ⟨⟨1, by decide⟩, Finset.mem_univ _, rfl⟩
  · change (exitTargetColumn p k).owner ∈ _
    rw [exitTarget_owner p k]
    apply separatorExitHsites_subset_hSupport p k hk
    exact Finset.mem_image.mpr ⟨⟨1, by decide⟩, Finset.mem_univ _, rfl⟩

theorem separatorFold_ne_octSite_of_not_mem_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (x : Site) (hx : x ∈ octahedron p.side)
    (hnot : x ∉ hSupport (p.separatorWord k) (separatorFold p k hk))
    (i : Fin (p.separatorWord k).length) : (separatorFold p k hk).pos i ≠ x := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply separatorFold_property p k hk (fun y => y ≠ x) _ _ _ _ _ i
  · dsimp only [separatorEntryChain]
    with_reducible
      exact edgeDimerFold_ne_octSite_of_not_mem_Hsites (m := p.side) hm entryEdgeFrame (6 * (k + 1)) 0 false
        (separatorEntry_room p k hk) x hx
        (not_mem_of_subset (separatorEntryHsites_subset_hSupport p k hk) hnot)
  · intro j
    rw [entryTetherWordFold_pos]
    with_reducible
      exact outside_ne_inside (m := p.side) _ x (entryTetherFold_outside p k hk _) hx
  · dsimp only [separatorCenterChain]
    with_reducible
      exact edgeDimerFold_ne_octSite_of_not_mem_Hsites (m := p.side) hm trackEdgeFrame (2 * p.separatorIndex k) 1 true
        (separatorCenter_room p k hk) x hx
        (not_mem_of_subset (separatorCenterHsites_subset_hSupport p k hk) hnot)
  · intro j
    rw [exitTetherWordFold_pos]
    with_reducible
      exact outside_ne_inside (m := p.side) _ x (exitTetherFold_outside p k hk _) hx
  · dsimp only [separatorExitChain]
    with_reducible
      exact edgeDimerFold_ne_octSite_of_not_mem_Hsites (m := p.side) hm exitEdgeFrame (10 * p.exitSlot k + 6) 2 true
        (separatorExit_room p k) x hx
        (not_mem_of_subset (separatorExitHsites_subset_hSupport p k hk) hnot)

theorem separatorFold_ne_cap_of_owner_not_mem_all (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C : DanglingColumn p.side) (hnot : C.owner ∉ hSupport (p.separatorWord k) (separatorFold p k hk))
    (i : Fin (p.separatorWord k).length) : (separatorFold p k hk).pos i ≠ C.seed := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hs (b : Bool) : C.owner ≠ (tetherSourceColumn p (b, ⟨k, by omega⟩)).owner := by
    intro heq
    apply hnot
    rw [heq]
    exact separator_tetherSource_mem_hSupport p k hk b
  have ht (b : Bool) : C.owner ≠ (tetherTargetColumn p (b, ⟨k, by omega⟩)).owner := by
    intro heq
    apply hnot
    rw [heq]
    exact separator_tetherTarget_mem_hSupport p k hk b
  apply separatorFold_property p k hk (fun y => y ≠ C.seed) _ _ _ _ _ i
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm entryEdgeFrame _ _ false (separatorEntry_room p k hk) C
      (fun h => hnot (separatorEntryHsites_subset_hSupport p k hk h))
  · intro j
    rw [entryTetherWordFold_pos]
    simpa only [tetherFold] using
      (danglingCap_ne_tetherFold p (false, ⟨k, by omega⟩) C (hs false) (ht false)
        ⟨j.val, by simpa only [List.length_replicate] using j.isLt⟩).symm
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm trackEdgeFrame _ _ true (separatorCenter_room p k hk) C
      (fun h => hnot (separatorCenterHsites_subset_hSupport p k hk h))
  · intro j
    rw [exitTetherWordFold_pos]
    simpa only [tetherFold] using
      (danglingCap_ne_tetherFold p (true, ⟨k, by omega⟩) C (hs true) (ht true)
        ⟨j.val, by simpa only [List.length_replicate] using j.isLt⟩).symm
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm exitEdgeFrame _ _ true (separatorExit_room p k) C
      (fun h => hnot (separatorExitHsites_subset_hSupport p k hk h))

theorem cappedSeparatorFold_ne_octSite_of_not_mem_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (x : Site) (hx : x ∈ octahedron p.side)
    (hnot : x ∉ hSupport (p.separatorWord k) (separatorFold p k hk))
    (i : Fin (capWord (p.separatorWord k)).length) : (cappedSeparatorFold p k hk C D hC hD).pos i ≠ x := by
  with_reducible
    exact frameTrack_property_of_capped_sites (cappedSeparatorFold p k hk C D hC hD) (separatorFold p k hk)
      C.seed D.seed (cappedSeparatorFold_sites p k hk C D hC hD) (fun y => y ≠ x)
      (column_seed_ne_inside C x hx)
      (separatorFold_ne_octSite_of_not_mem_hSupport p k hk x hx hnot)
      (column_seed_ne_inside D x hx) i

theorem cappedSeparatorFold_ne_cap_of_owner_not_mem_all (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (E : DanglingColumn p.side) (hnot : E.owner ∉ hSupport (p.separatorWord k) (separatorFold p k hk))
    (i : Fin (capWord (p.separatorWord k)).length) : (cappedSeparatorFold p k hk C D hC hD).pos i ≠ E.seed := by
  have hcap (X : DanglingColumn p.side)
      (hX : X.owner ∈ hSupport (p.separatorWord k) (separatorFold p k hk)) : X.seed ≠ E.seed := by
    with_reducible
      exact column_seeds_ne_of_owner_mem_not_mem _ X E hX hnot
  with_reducible
    exact frameTrack_property_of_capped_sites (cappedSeparatorFold p k hk C D hC hD) (separatorFold p k hk)
      C.seed D.seed (cappedSeparatorFold_sites p k hk C D hC hD) (fun y => y ≠ E.seed)
      (hcap C (by rw [hC]; exact separatorFirstH_mem_hSupport p k hk))
      (separatorFold_ne_cap_of_owner_not_mem_all p k hk E hnot)
      (hcap D (by rw [hD]; exact separatorLastH_mem_hSupport p k hk)) i

end ProteinFolding.Tetrahedral.NearField
