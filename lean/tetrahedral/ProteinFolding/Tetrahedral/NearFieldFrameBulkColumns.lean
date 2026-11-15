import ProteinFolding.Tetrahedral.NearFieldFrameColumnCertificate
import ProteinFolding.Tetrahedral.NearFieldFrameBounds

/-! Every column met by a frame P-link has a deleted-edge owner.
Consequently the frame links avoid all bulk columns in every skin. -/

namespace ProteinFolding.Tetrahedral

private theorem column_owner_coordinates_first {m q : ℕ} (C : DanglingColumn m)
    (kind : Fin 6) (hq : q % 2 = 1) (r : Fin (nearFrameLength kind))
    (ownerA : Bool) (hcolour : if ownerA then InASublattice C.owner.val else InBSublattice C.owner.val)
    (heq : C.point 0 = nearFramePoint m q kind hq r) :
    C.owner.val = nearFrameColumnOwnerCoordinates m q kind r.val false ownerA C.dir := by
  have h := congrArg (fun p : Site => p.val) heq
  change (step C.owner C.dir).val = nearFrameCoordinates m q kind r.val at h
  cases ownerA with
  | false =>
    rw [step_val_of_B C.owner hcolour] at h
    funext k
    have hk := congrFun h k
    change C.owner.val k - bondVector C.dir k = nearFrameCoordinates m q kind r.val k at hk
    rw [bondVector_eq_bondComponent] at hk
    dsimp [nearFrameColumnOwnerCoordinates]
    omega
  | true =>
    rw [step_val_of_A C.owner hcolour] at h
    funext k
    have hk := congrFun h k
    change C.owner.val k + bondVector C.dir k = nearFrameCoordinates m q kind r.val k at hk
    rw [bondVector_eq_bondComponent] at hk
    dsimp [nearFrameColumnOwnerCoordinates]
    omega

private theorem column_owner_coordinates_second {m q : ℕ} (C : DanglingColumn m)
    (kind : Fin 6) (hq : q % 2 = 1) (r : Fin (nearFrameLength kind))
    (ownerA : Bool) (hcolour : if ownerA then InASublattice C.owner.val else InBSublattice C.owner.val)
    (heq : C.point 1 = nearFramePoint m q kind hq r) :
    C.owner.val = nearFrameColumnOwnerCoordinates m q kind r.val true ownerA C.dir := by
  rw [C.point_one_eq] at heq
  have h := congrArg (fun p : Site => p.val) heq
  change (step (step C.owner C.dir) (columnOpposite C.dir)).val = nearFrameCoordinates m q kind r.val at h
  cases ownerA with
  | false =>
    rw [step_val_of_A _ (step_in_A hcolour C.dir), step_val_of_B C.owner hcolour] at h
    funext k
    have hk := congrFun h k
    change C.owner.val k - bondVector C.dir k + bondVector (columnOpposite C.dir) k =
      nearFrameCoordinates m q kind r.val k at hk
    simp_rw [bondVector_eq_bondComponent] at hk
    dsimp [nearFrameColumnOwnerCoordinates]
    omega
  | true =>
    rw [step_val_of_B _ (step_in_B hcolour C.dir), step_val_of_A C.owner hcolour] at h
    funext k
    have hk := congrFun h k
    change C.owner.val k + bondVector C.dir k - bondVector (columnOpposite C.dir) k =
      nearFrameCoordinates m q kind r.val k at hk
    simp_rw [bondVector_eq_bondComponent] at hk
    dsimp [nearFrameColumnOwnerCoordinates]
    omega

theorem column_owner_deleted_of_first_eq_frameP {m q : ℕ} (C : DanglingColumn m)
    (kind : Fin 6) (hq : q % 2 = 1) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (heq : C.point 0 = nearFramePoint m q kind hq r) : bulkOnDeletedEdge m C.owner := by
  rcases C.owner.property with hpA | hpB
  · have hc := column_owner_coordinates_first C kind hq r true hpA heq
    have hb := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m C.owner).mp C.owner_mem)
    have hd := (step_not_mem_octahedron_A m hpA C.owner_mem C.dir).mp C.seed_outside
    rw [hc] at hb hd
    obtain ⟨hne, hother⟩ := nearFrameColumn_first_A_certificate m q kind r C.dir hr0 hrlast hb hd
    rw [← hc] at hd hother
    exact ⟨C.dir, nearFrameColumnOtherFace kind false C.dir, hne.symm,
      Or.inl ⟨⟨C.owner_mem, hpA, hd⟩, hother⟩⟩
  · have hc := column_owner_coordinates_first C kind hq r false hpB heq
    have hb := (inOctahedron_iff_B m hpB).mp ((mem_octahedron m C.owner).mp C.owner_mem)
    have hd := (step_not_mem_octahedron_B m hpB C.owner_mem C.dir).mp C.seed_outside
    rw [hc] at hb hd
    have hupper : octRadius m - 1 = 2 * (m : ℤ) - 3 := by dsimp [octRadius]; omega
    obtain ⟨hne, hother⟩ := nearFrameColumn_first_B_certificate m q kind r C.dir hr0 hrlast
      (by simpa only [hupper] using hb) hd
    rw [← hc] at hd hother
    exact ⟨nearFrameColumnOtherFace kind false C.dir, C.dir, hne,
      Or.inr ⟨⟨C.owner_mem, hpB, hd⟩, by dsimp [octRadius] at hother; omega⟩⟩

theorem column_owner_deleted_of_second_eq_frameP {m q : ℕ} (C : DanglingColumn m)
    (kind : Fin 6) (hq : q % 2 = 1) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (heq : C.point 1 = nearFramePoint m q kind hq r) : bulkOnDeletedEdge m C.owner := by
  rcases C.owner.property with hpA | hpB
  · have hc := column_owner_coordinates_second C kind hq r true hpA heq
    have hb := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m C.owner).mp C.owner_mem)
    have hd := (step_not_mem_octahedron_A m hpA C.owner_mem C.dir).mp C.seed_outside
    rw [hc] at hb hd
    obtain ⟨hne, hother⟩ := nearFrameColumn_second_A_certificate m q kind r C.dir hr0 hrlast hb hd
    rw [← hc] at hd hother
    exact ⟨C.dir, nearFrameColumnOtherFace kind true C.dir, hne.symm,
      Or.inl ⟨⟨C.owner_mem, hpA, hd⟩, hother⟩⟩
  · have hc := column_owner_coordinates_second C kind hq r false hpB heq
    have hb := (inOctahedron_iff_B m hpB).mp ((mem_octahedron m C.owner).mp C.owner_mem)
    have hd := (step_not_mem_octahedron_B m hpB C.owner_mem C.dir).mp C.seed_outside
    rw [hc] at hb hd
    have hupper : octRadius m - 1 = 2 * (m : ℤ) - 3 := by dsimp [octRadius]; omega
    obtain ⟨hne, hother⟩ := nearFrameColumn_second_B_certificate m q kind r C.dir hr0 hrlast
      (by simpa only [hupper] using hb) hd
    rw [← hc] at hd hother
    exact ⟨nearFrameColumnOtherFace kind true C.dir, C.dir, hne,
      Or.inr ⟨⟨C.owner_mem, hpB, hd⟩, by dsimp [octRadius] at hother; omega⟩⟩

theorem column_owner_deleted_of_eq_frameP {m q : ℕ} (C : DanglingColumn m)
    (kind : Fin 6) (hq : q % 2 = 1) (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (n : ℕ) (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (heq : C.point n = nearFramePoint m q kind hq r) : bulkOnDeletedEdge m C.owner := by
  have hs := nearFramePoint_mem_skin_one m q kind hq hqlo hqhi r hr0 hrlast
  rw [← heq] at hs
  have hn := (C.point_mem_skin_iff_two_indices n 1 (by decide)).mp hs
  rcases hn with hn | hn
  · have he : n = 0 := by omega
    rw [he] at heq
    exact column_owner_deleted_of_first_eq_frameP C kind hq r hr0 hrlast heq
  · have he : n = 1 := by omega
    rw [he] at heq
    exact column_owner_deleted_of_second_eq_frameP C kind hq r hr0 hrlast heq

theorem bulkColumn_ne_frameP {m q : ℕ} (C : DanglingColumn m) (hbulk : C.owner ∈ bulkInterior m)
    (kind : Fin 6) (hq : q % 2 = 1) (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (n : ℕ) (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    C.point n ≠ nearFramePoint m q kind hq r := by
  intro heq
  have hdel := column_owner_deleted_of_eq_frameP C kind hq hqlo hqhi n r hr0 hrlast heq
  exact (Finset.mem_sdiff.mp hbulk).2 (Finset.mem_filter.mpr ⟨C.owner_mem, hdel⟩)

end ProteinFolding.Tetrahedral
