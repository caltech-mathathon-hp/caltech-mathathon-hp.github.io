import ProteinFolding.Tetrahedral.NearFieldRingColumns
import ProteinFolding.Tetrahedral.NearFieldCapFoldSites

/-! Capping the actual complete ring, with exact word, H support, occupied
sites, solid bounds, and endpoint positions. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem ringWord_length_pos (m : ℕ) (hm : 3 ≤ m) :
    0 < (dimerChain (3 * (m - 2))).length := by
  have h := dimerChain_length (3 * (m - 2)) (by omega)
  omega

theorem ringCaps_ne (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame)
    (C D : DanglingColumn m) (hC : C.owner = ringTerminalSite m F 0 0)
    (hD : D.owner = ringTerminalSite m F 2 1) : C.seed ≠ D.seed := by
  apply dangling_caps_ne_of_owner_ne m C.owner D.owner C.dir D.dir C.owner_mem D.owner_mem C.seed_outside
  rw [hC, hD]
  exact ringTerminalSite_ne m (by omega) heven F 0 2 0 1 (by decide)

noncomputable def cappedRingFold (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1) :
    Fold tetrahedralLattice (capWord (dimerChain (3 * (m - 2)))).length :=
  cappedWordFold (ringFold m (by omega) heven F) C.seed D.seed (ringWord_length_pos m (by omega))
    (fun i => (ringFold_ne_first_column m hm heven F C hC i 0).symm)
    (fun i => ringFold_ne_last_column m hm heven F D hD i 0)
    (ringCaps_ne m hm heven F C D hC hD)
    (by intro i hi; rw [ringFold_first m (by omega) heven F i hi, ← hC]; exact (step_adj _ _).symm)
    (by intro i hi; rw [ringFold_last m (by omega) heven F i hi, ← hD]; exact step_adj _ _)

theorem cappedRingFold_hSupport (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1) :
    hSupport (capWord (dimerChain (3 * (m - 2)))) (cappedRingFold m hm heven F C D hC hD) =
      ringHsites m F := by
  rw [cappedRingFold, cappedWordFold_hSupport, ringFold_hSupport]

theorem cappedRingFold_hSupport_subset_oct (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1) :
    hSupport (capWord (dimerChain (3 * (m - 2)))) (cappedRingFold m hm heven F C D hC hD) ⊆
      octahedron m := by
  rw [cappedRingFold_hSupport]
  exact ringHsites_subset_oct m (by omega) F

theorem cappedRingFold_sites (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1) :
    foldSites (cappedRingFold m hm heven F C D hC hD) =
      ({C.seed} ∪ foldSites (ringFold m (by omega) heven F)) ∪ {D.seed} :=
  cappedWordFold_sites _ _ _ _ _ _ _ _ _

theorem cappedRingFold_first (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) (hi : i.val = 0) :
    (cappedRingFold m hm heven F C D hC hD).pos i = C.seed :=
  cappedWordFold_first _ _ _ _ _ _ _ _ _ i hi

theorem cappedRingFold_last (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length)
    (hi : i.val + 1 = (capWord (dimerChain (3 * (m - 2)))).length) :
    (cappedRingFold m hm heven F C D hC hD).pos i = D.seed :=
  cappedWordFold_last _ _ _ _ _ _ _ _ _ i hi

theorem cappedRingFold_mem_solid_one (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) :
    (cappedRingFold m hm heven F C D hC hD).pos i ∈ skinSolid m 1 := by
  have hmem := (mem_foldSites (cappedRingFold m hm heven F C D hC hD) _).mpr ⟨i, rfl⟩
  rw [cappedRingFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]; exact C.point_zero_mem_solid_one
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    rw [← hj]
    exact ringFold_mem_solid_one m (by omega) heven F j
  · rw [h]; exact D.point_zero_mem_solid_one

end ProteinFolding.Tetrahedral.NearField
