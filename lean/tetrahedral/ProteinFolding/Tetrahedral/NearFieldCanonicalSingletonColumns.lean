import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletons
import ProteinFolding.Tetrahedral.NearFieldRingFrameColumns
import ProteinFolding.Tetrahedral.NearFieldCanonicalRingVertices
import ProteinFolding.Tetrahedral.NearFieldExitCapFamily

/-! The six actual columns owned by the standalone vertex units. Their
reserved face coordinate separates them from the frame; three scalar
halfspaces separate them from every separator tether. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem canonicalSingletonOwner_vertex (m : ℕ) (r : Fin 3) :
    ∃ a positive, canonicalSingletonOwner m r = octVertexSite m a positive := by
  fin_cases r
  · exact ⟨2, true, rfl⟩
  · exact ⟨1, false, rfl⟩
  · exact ⟨0, false, rfl⟩

theorem canonicalSingletonColumn_sy (m : ℕ) (hm : 1 ≤ m) (r : Fin 3) (last : Bool) :
    (canonicalSingletonColumn m hm r last).sy =
      bigFaceY (if last then 3 else r.castSucc) := by
  change (if InASublattice (canonicalSingletonOwner m r).val then _ else _) = _
  rw [if_pos (canonicalSingletonOwner_inA m r)]
  rfl

theorem canonicalSingletonColumn_sz (m : ℕ) (hm : 1 ≤ m) (r : Fin 3) (last : Bool) :
    (canonicalSingletonColumn m hm r last).sz =
      bigFaceZ (if last then 3 else r.castSucc) := by
  change (if InASublattice (canonicalSingletonOwner m r).val then _ else _) = _
  rw [if_pos (canonicalSingletonOwner_inA m r)]
  rfl

theorem canonicalSingletonColumn_seed_val (m : ℕ) (hm : 1 ≤ m) (r : Fin 3)
    (last : Bool) (d : Fin 3) :
    (canonicalSingletonColumn m hm r last).seed.val d =
      (canonicalSingletonOwner m r).val d + bondComponent (if last then 3 else r.castSucc) d := by
  change (step (canonicalSingletonOwner m r) _).val d = _
  rw [step_val_of_A _ (canonicalSingletonOwner_inA m r)]
  change _ + bondVector _ d = _
  rw [bondVector_eq_bondComponent]
  rfl

theorem canonicalSingletonColumn_zero_positiveZ (m : ℕ) (hm : 1 ≤ m)
    (last : Bool) (n : ℕ) :
    ((canonicalSingletonColumn m hm 0 last).point n).val 2 = octRadius m + 1 + n := by
  let C := canonicalSingletonColumn m hm 0 last
  have hz := bulkArmPoint_z C.sy C.sz C.sy_unit C.sz_unit C.seed n
  change (C.point n).val 2 - 1 = C.seed.val 2 - 1 + (n : ℤ) * C.sz at hz
  have hsz : C.sz = 1 := by
    rw [canonicalSingletonColumn_sz]
    cases last <;> rfl
  have hseed : C.seed.val 2 = octRadius m + 1 := by
    have h := canonicalSingletonColumn_seed_val m hm 0 last 2
    change C.seed.val 2 = _ at h
    cases last <;> dsimp [canonicalSingletonOwner, octVertexForFaces, octVertexSite,
      octVertexCoordinates, octCentre, bondComponent] at h <;> omega
  rw [hsz, hseed] at hz
  change (C.point n).val 2 = _
  omega

theorem canonicalSingletonColumn_one_negativeY (m : ℕ) (hm : 1 ≤ m)
    (last : Bool) (n : ℕ) :
    ((canonicalSingletonColumn m hm 1 last).point n).val 1 = -1 - (n : ℤ) := by
  let C := canonicalSingletonColumn m hm 1 last
  have hy := bulkArmPoint_y m C.sy C.sz C.sy_unit C.sz_unit C.seed n
  change (C.point n).val 1 - octRadius m =
    C.seed.val 1 - octRadius m + (n : ℤ) * C.sy at hy
  have hsy : C.sy = -1 := by
    rw [canonicalSingletonColumn_sy]
    cases last <;> rfl
  have hseed : C.seed.val 1 = -1 := by
    have h := canonicalSingletonColumn_seed_val m hm 1 last 1
    change C.seed.val 1 = _ at h
    cases last <;> dsimp [canonicalSingletonOwner, octVertexForFaces, octVertexSite,
      octVertexCoordinates, octCentre, bondComponent] at h <;> omega
  rw [hsy, hseed] at hy
  change (C.point n).val 1 = _
  omega

theorem canonicalSingletonColumn_two_negativeX (m : ℕ) (hm : 1 ≤ m)
    (last : Bool) (n : ℕ) :
    ((canonicalSingletonColumn m hm 2 last).point n).val 0 ≤ -octRadius m := by
  let C := canonicalSingletonColumn m hm 2 last
  have hx := bulkArmPoint_x_charge C.sy C.sz C.sy_unit C.sz_unit C.seed n
  change (C.point n).val 0 = C.seed.val 0 +
    (siteCharge (C.point n) - siteCharge C.seed) * (C.sy * C.sz) at hx
  have hc0 : siteCharge C.seed = 1 := siteCharge_B
    (step_in_B (canonicalSingletonOwner_inA m 2) C.dir)
  have hc := siteCharge_bounds (C.point n)
  have hsign : C.sy * C.sz = -1 := by
    rw [canonicalSingletonColumn_sy, canonicalSingletonColumn_sz]
    cases last <;> rfl
  have hseed : C.seed.val 0 = -octRadius m - 1 := by
    have h := canonicalSingletonColumn_seed_val m hm 2 last 0
    change C.seed.val 0 = _ at h
    cases last <;> dsimp [canonicalSingletonOwner, octVertexForFaces, octVertexSite,
      octVertexCoordinates, octCentre, bondComponent] at h <;> omega
  rw [hc0, hsign, hseed] at hx
  change (C.point n).val 0 ≤ _
  omega

theorem canonicalSingletonColumn_ne_tetherRegion (m : ℕ) (hm : 3 ≤ m)
    (r : Fin 3) (last : Bool) (n : ℕ) (s : Site) (hs : FacePositive m s)
    (hz : s.val 2 ≤ 0) :
    (canonicalSingletonColumn m (by omega) r last).point n ≠ s := by
  intro heq
  fin_cases r
  · have h := canonicalSingletonColumn_zero_positiveZ m (by omega) last n
    change (canonicalSingletonColumn m (by omega) 0 last).point n = s at heq
    rw [heq] at h
    dsimp [octRadius] at h
    omega
  · have h := canonicalSingletonColumn_one_negativeY m (by omega) last n
    change (canonicalSingletonColumn m (by omega) 1 last).point n = s at heq
    rw [heq] at h
    have hy := hs.2
    dsimp [bulkY, octRadius] at hy
    omega
  · have h := canonicalSingletonColumn_two_negativeX m (by omega) last n
    change (canonicalSingletonColumn m (by omega) 2 last).point n = s at heq
    rw [heq] at h
    have hx := hs.1
    dsimp [octRadius] at h
    omega

theorem canonicalSingletonColumn_ne_entryTether (p : ConstructionParameters)
    (r : Fin 3) (last : Bool) (n k : ℕ) (hk : k ≤ p.bins) (i : Fin (p.entryTether k)) :
    (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last).point n ≠
      (entryTetherFold p k hk).pos i :=
  canonicalSingletonColumn_ne_tetherRegion p.side (by have h := p.side_ge; omega)
    r last n _ (entryTetherFold_positive p k hk i) (entryTetherFold_nonpositiveZ p k hk i)

theorem canonicalSingletonColumn_ne_exitTether (p : ConstructionParameters)
    (r : Fin 3) (last : Bool) (n k : ℕ) (hk : k ≤ p.bins) (i : Fin (p.exitTether k)) :
    (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last).point n ≠
      (exitTetherFold p k hk).pos i :=
  canonicalSingletonColumn_ne_tetherRegion p.side (by have h := p.side_ge; omega)
    r last n _ (exitTetherFold_positive p k hk i) (exitTetherFold_nonpositiveZ p k hk i)

theorem Acolumn_first_two_reserved_coordinate (m : ℕ) (hm : 3 ≤ m)
    (C : DanglingColumn m) (hA : InASublattice C.owner.val)
    (hp : tetraCoordinate m C.owner.val 3 = octRadius m)
    (n : ℕ) (hn : n = 0 ∨ n = 1) :
    -octRadius m < tetraCoordinate m (C.point n).val 3 := by
  rcases hn with rfl | rfl
  · have hs := tetraCoordinate_step_A m hA C.dir 3
    change -octRadius m < tetraCoordinate m (step C.owner C.dir).val 3
    dsimp [octRadius] at hp ⊢
    split_ifs at hs <;> omega
  · rw [C.point_one_eq]
    have h := (twoStep_tetraCoordinate_bounds m C.owner C.dir (columnOpposite C.dir) 3).1
    dsimp [octRadius] at hp ⊢
    omega

theorem canonicalSingletonColumn_ne_frameP (m : ℕ) (hm : 3 ≤ m)
    (r : Fin 3) (last : Bool) (n q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (s : Fin (nearFrameLength kind)) (hs0 : 0 < s.val)
    (hslast : s.val + 1 < nearFrameLength kind) :
    (canonicalSingletonColumn m (by omega) r last).point n ≠ nearFramePoint m q kind hq s := by
  let C := canonicalSingletonColumn m (by omega) r last
  intro heq
  have hskin := nearFramePoint_mem_skin_one m q kind hq hqlo hqhi s hs0 hslast
  rw [← heq] at hskin
  have hn : n = 0 ∨ n = 1 := by
    have h := (C.point_mem_skin_iff_two_indices n 1 (by decide)).mp hskin
    omega
  have hlo := Acolumn_first_two_reserved_coordinate m hm C
    (canonicalSingletonOwner_inA m r) (canonicalSingletonOwner_faces m r).2 n hn
  have hhi := nearFramePoint_reserved_small_coordinate m q kind hq s
  rw [heq] at hlo
  omega

theorem canonicalSingletonColumn_ne_framePFold (m : ℕ) (hm : 3 ≤ m)
    (r : Fin 3) (last : Bool) (n q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (s : Fin (nearFrameLength kind - 2)) :
    (canonicalSingletonColumn m (by omega) r last).point n ≠ (framePFold m q kind hq).pos s :=
  canonicalSingletonColumn_ne_frameP m hm r last n q kind hq hqlo hqhi
    ⟨s.val + 1, by have h := s.isLt; omega⟩
    (by change 0 < s.val + 1; omega)
    (by change s.val + 1 + 1 < _; have h := s.isLt; omega)

theorem canonicalSingletonColumn_ne_innerPPP (m : ℕ) (hm : 3 ≤ m)
    (r : Fin 3) (last : Bool) (n : ℕ) (F : OctEdgeFrame) (i : ℕ)
    (hlo : 1 ≤ i) (hhi : i + 4 ≤ 2 * m - 1) (s : Fin 3) :
    (canonicalSingletonColumn m (by omega) r last).point n ≠ (edgePPPFold m F i).pos s := by
  obtain ⟨a, positive, ha⟩ := canonicalSingletonOwner_vertex m r
  exact (edgePPPFold_ne_vertex_column m hm F i (by omega)
    (canonicalSingletonColumn m (by omega) r last) a positive ha
    (by
      change canonicalSingletonOwner m r ≠ _
      rw [ha]
      exact (ringEdgePoint_ne_vertex m hm F i hlo (by omega) a positive).symm)
    (by
      change canonicalSingletonOwner m r ≠ _
      rw [ha]
      exact (ringEdgePoint_ne_vertex m hm F (i + 2) (by omega) hhi a positive).symm)
    s n).symm

end ProteinFolding.Tetrahedral.NearField
