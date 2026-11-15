import ProteinFolding.Tetrahedral.NearFieldSeparatorFamily
import ProteinFolding.Tetrahedral.NearFieldSeparatorCapSupport

/-! Simultaneous disjointness of all complete capped separator units. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

theorem separatorFold_ne_cap_of_owner_not_mem_hSupport (p : ConstructionParameters) (k : ℕ)
    (hk : k ≤ p.bins) (C : DanglingColumn p.side) (hA : InASublattice C.owner.val)
    (hnot : C.owner ∉ hSupport (p.separatorWord k) (separatorFold p k hk))
    (i : Fin (p.separatorWord k).length) : (separatorFold p k hk).pos i ≠ C.seed := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hnotE : C.owner ∉ edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0 := by
    intro hx
    apply hnot
    rw [separatorFold_hSupport]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hnotC : C.owner ∉ edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k) 1 := by
    intro hx
    apply hnot
    rw [separatorFold_hSupport]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hnotX : C.owner ∉ edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 := by
    intro hx
    apply hnot
    rw [separatorFold_hSupport]
    exact Finset.mem_union_right _ hx
  apply separatorFold_property p k hk (fun x => x ≠ C.seed) _ _ _ _ _ i
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm entryEdgeFrame _ _ false (separatorEntry_room p k hk) C hnotE
  · intro j
    rw [entryTetherWordFold_pos]
    simpa only [tetherFold] using
      (danglingCap_ne_tether_of_owner_inA p (false, ⟨k, by omega⟩) C hA ⟨j.val, by simpa using j.isLt⟩).symm
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm trackEdgeFrame _ _ true (separatorCenter_room p k hk) C hnotC
  · intro j
    rw [exitTetherWordFold_pos]
    simpa only [tetherFold] using
      (danglingCap_ne_tether_of_owner_inA p (true, ⟨k, by omega⟩) C hA ⟨j.val, by simpa using j.isLt⟩).symm
  · exact edgeDimerFold_ne_cap_of_owner_not_mem hm exitEdgeFrame _ _ true (separatorExit_room p k) C hnotX

theorem separatorHsupports_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l) :
    Disjoint (hSupport (p.separatorWord k) (separatorFold p k hk))
      (hSupport (p.separatorWord l) (separatorFold p l hl)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, hi⟩ := (mem_hSupport _ _ x).mp hx
  obtain ⟨j, _, hj⟩ := (mem_hSupport _ _ x).mp hy
  exact separatorFolds_disjoint p k l hk hl hne i j (hi.trans hj.symm)

theorem cappedSeparatorFolds_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (C D C' D' : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (hC' : C'.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (l + 1)))
    (hD' : D'.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot l + 10)) :
    Disjoint (foldSites (cappedSeparatorFold p k hk C D hC hD))
      (foldSites (cappedSeparatorFold p l hl C' D' hC' hD')) := by
  have hdis := separatorHsupports_disjoint p k l hk hl hne
  have hc : C.owner ∈ hSupport (p.separatorWord k) (separatorFold p k hk) := by rw [hC]; exact separatorFirstH_mem_hSupport p k hk
  have hd : D.owner ∈ hSupport (p.separatorWord k) (separatorFold p k hk) := by rw [hD]; exact separatorLastH_mem_hSupport p k hk
  have hc' : C'.owner ∈ hSupport (p.separatorWord l) (separatorFold p l hl) := by rw [hC']; exact separatorFirstH_mem_hSupport p l hl
  have hd' : D'.owner ∈ hSupport (p.separatorWord l) (separatorFold p l hl) := by rw [hD']; exact separatorLastH_mem_hSupport p l hl
  have hca : InASublattice C.owner.val := by rw [hC]; exact separatorFirstH_inA p k
  have hda : InASublattice D.owner.val := by rw [hD]; exact separatorLastH_inA p k
  have hca' : InASublattice C'.owner.val := by rw [hC']; exact separatorFirstH_inA p l
  have hda' : InASublattice D'.owner.val := by rw [hD']; exact separatorLastH_inA p l
  have hcap (X Y : DanglingColumn p.side)
      (hX : X.owner ∈ hSupport (p.separatorWord k) (separatorFold p k hk))
      (hY : Y.owner ∈ hSupport (p.separatorWord l) (separatorFold p l hl)) : X.seed ≠ Y.seed := by
    apply dangling_caps_ne_of_owner_ne p.side X.owner Y.owner X.dir Y.dir X.owner_mem Y.owner_mem X.seed_outside
    intro heq
    rw [heq] at hX
    exact Finset.disjoint_left.mp hdis hX hY
  have hbody (X : DanglingColumn p.side) (hX : X.owner ∈ hSupport (p.separatorWord l) (separatorFold p l hl))
      (hXA : InASublattice X.owner.val) (i : Fin (p.separatorWord k).length) : (separatorFold p k hk).pos i ≠ X.seed :=
    separatorFold_ne_cap_of_owner_not_mem_hSupport p k hk X hXA (fun hx => Finset.disjoint_left.mp hdis hx hX) i
  have hbody' (X : DanglingColumn p.side) (hX : X.owner ∈ hSupport (p.separatorWord k) (separatorFold p k hk))
      (hXA : InASublattice X.owner.val) (i : Fin (p.separatorWord l).length) : (separatorFold p l hl).pos i ≠ X.seed :=
    separatorFold_ne_cap_of_owner_not_mem_hSupport p l hl X hXA (fun hx => Finset.disjoint_left.mp hdis hX hx) i
  rw [cappedSeparatorFold_sites, cappedSeparatorFold_sites]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [Finset.mem_union, Finset.mem_singleton] at hx hy
  rcases hx with (rfl | hx) | rfl
  · rcases hy with (h | h) | h
    · exact hcap C C' hc hc' h
    · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
      exact hbody' C hc hca j hj
    · exact hcap C D' hc hd' h
  · obtain ⟨i, rfl⟩ := (mem_foldSites _ _).mp hx
    rcases hy with (h | h) | h
    · exact hbody C' hc' hca' i h
    · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
      exact separatorFolds_disjoint p k l hk hl hne i j hj.symm
    · exact hbody D' hd' hda' i h
  · rcases hy with (h | h) | h
    · exact hcap D C' hd hc' h
    · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
      exact hbody' D hd hda j hj
    · exact hcap D D' hd hd' h

end ProteinFolding.Tetrahedral.NearField
