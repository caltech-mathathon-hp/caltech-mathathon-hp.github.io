import ProteinFolding.Tetrahedral.NearFieldFrameFaceColumns
import ProteinFolding.Tetrahedral.NearFieldTetherSupport

/-! The actual N4 tether constructors avoid every literal Appendix C frame
P-link at the reduction's two-slot and six-slot index congruences. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem higherSkin_ne_frameP (m j q : ℕ) (hj : 2 ≤ j) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    {p : Site} (hp : p ∈ skin m j) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    p ≠ nearFramePoint m q kind hq r := by
  intro heq
  have hframe := nearFramePoint_mem_skin_one m q kind hq hqlo hqhi r hr0 hrlast
  rw [heq] at hp
  exact Finset.disjoint_left.mp (skins_disjoint m 1 j (by omega)) hframe hp

theorem entryUp_ne_frameP (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (q : ℕ) (hq : q % 2 = 1) (kind : Fin 6) (hslot : kind = 1 → q % 6 = 5)
    (i : Fin (2 * p.entrySkin k - 1)) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (entryUp p k hk).pos i ≠ nearFramePoint p.side q kind hq r := by
  have ht := p.entry_column_triangle_room k hk
  have ha : 2 ≤ entryAnchorA p k := by unfold entryAnchorA; omega
  have hm : 1 ≤ p.side := by omega
  change borrowedPoint p.side (entryAnchorA p k) (3 * (k + 1)) 0
    (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) i.val ≠ _
  cases hn : i.val with
  | zero =>
    apply faceEntryCap_ne_frameP _ _ _ _ _ (by omega) q hq kind _ _ r hr0 hrlast
    · intro _ heq
      have hy := congrArg (fun s : Site => s.val 1) heq
      change (faceSurfaceSite p.side 0 (entryAnchorA p k) (3 * (k + 1)) 0
        (entryAnchor_equation p k hk)).val 1 = (octEdgeZigzag p.side entryEdgeFrame 3).val 1 at hy
      rw [entryEdgeZigzag_coordinates hm] at hy
      dsimp [faceSurfaceSite, faceSurfaceCoordinates, entryEdgeCoordinates] at hy
      omega
    · intro hkind heq
      have hmod := hslot hkind
      have hy := congrArg (fun s : Site => s.val 1) heq
      change (faceSurfaceSite p.side 0 (entryAnchorA p k) (3 * (k + 1)) 0
        (entryAnchor_equation p k hk)).val 1 = (octEdgeZigzag p.side entryEdgeFrame q).val 1 at hy
      rw [entryEdgeZigzag_coordinates hm] at hy
      dsimp [faceSurfaceSite, faceSurfaceCoordinates, entryEdgeCoordinates] at hy
      omega
  | succ n =>
    exact interiorFaceColumn_ne_frameP p.side (entryAnchorA p k - 1) (3 * (k + 1)) (0 + 1)
      (by have he := entryAnchor_equation p k hk; omega) (by omega) (by omega)
      q hq kind (n + 1) r hr0 hrlast

theorem entryDown_ne_frameP (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (q : ℕ) (hq : q % 2 = 1) (kind : Fin 6)
    (i : Fin (2 * p.entrySkin k - 1)) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (entryDown p k hk).pos i ≠ nearFramePoint p.side q kind hq r := by
  have hr := p.separator_room k hk
  have hc := separatorIndex_ge_two p k
  exact interiorFaceColumn_ne_frameP p.side (p.side - 2 - p.separatorIndex k) 0 (p.separatorIndex k)
    (by omega) (by omega) (by omega) q hq kind i.rev.val r hr0 hrlast

theorem exitUp_ne_frameP (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (q : ℕ) (hq : q % 2 = 1) (kind : Fin 6)
    (i : Fin (exitColumnCount p k)) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (exitUp p k hk).pos i ≠ nearFramePoint p.side q kind hq r := by
  have hr := p.separator_room k hk
  have hf : 1 ≤ p.rightFiller := by unfold ConstructionParameters.rightFiller; omega
  exact interiorFaceColumn_ne_frameP p.side (p.side - 3 - p.separatorIndex k) 0 (p.separatorIndex k + 1)
    (by omega) (by omega) (by omega) q hq kind i.val r hr0 hrlast

theorem exitDown_ne_frameP (p : ConstructionParameters) (k : ℕ)
    (q : ℕ) (hq : q % 2 = 1) (kind : Fin 6) (hslot : kind = 4 → q % 10 = 5)
    (i : Fin (exitColumnCount p k)) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (exitDown p k).pos i ≠ nearFramePoint p.side q kind hq r := by
  have ht := p.exit_column_triangle_room k
  apply faceColumn_ne_frameP p.side 0 (5 * p.exitSlot k + 3) (p.side - 5 - 5 * p.exitSlot k)
    (by omega) (by omega) q hq kind _ i.rev.val r hr0 hrlast
  intro hkind heq
  have hmod := hslot hkind
  have hy := congrArg (fun s : Site => s.val 1) heq
  change (faceSurfaceSite p.side 0 0 (5 * p.exitSlot k + 3) (p.side - 5 - 5 * p.exitSlot k)
    (by omega)).val 1 = (octEdgeZigzag p.side exitEdgeFrame q).val 1 at hy
  rw [exitEdgeZigzag_coordinates (by omega)] at hy
  dsimp [faceSurfaceSite, faceSurfaceCoordinates, exitEdgeCoordinates] at hy
  omega

theorem entryTetherFold_ne_frameP (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (q : ℕ) (hq : q % 2 = 1) (kind : Fin 6) (hslot : kind = 1 → q % 6 = 5)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius p.side)
    (i : Fin (p.entryTether k)) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (entryTetherFold p k hk).pos i ≠ nearFramePoint p.side q kind hq r := by
  apply entryTetherFold_property p k hk (fun s => s ≠ nearFramePoint p.side q kind hq r) _ _ _ i
  · intro t
    exact entryUp_ne_frameP p k hk q hq kind hslot t r hr0 hrlast
  · intro t
    exact higherSkin_ne_frameP p.side (p.entrySkin k) q (p.tether_skin_bounds k hk).1 kind hq hqlo hqhi
      (entryRow_mem_skin p k hk t) r hr0 hrlast
  · intro t
    exact entryDown_ne_frameP p k hk q hq kind t r hr0 hrlast

theorem exitTetherFold_ne_frameP (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (q : ℕ) (hq : q % 2 = 1) (kind : Fin 6) (hslot : kind = 4 → q % 10 = 5)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius p.side)
    (i : Fin (p.exitTether k)) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (exitTetherFold p k hk).pos i ≠ nearFramePoint p.side q kind hq r := by
  apply exitTetherFold_property p k hk (fun s => s ≠ nearFramePoint p.side q kind hq r) _ _ _ i
  · intro t
    exact exitUp_ne_frameP p k hk q hq kind t r hr0 hrlast
  · intro t
    exact higherSkin_ne_frameP p.side (p.exitSkin k) q (by have h := p.tether_skin_bounds k hk; omega)
      kind hq hqlo hqhi (exitRow_mem_skin p k hk t) r hr0 hrlast
  · intro t
    exact exitDown_ne_frameP p k q hq kind hslot t r hr0 hrlast

end ProteinFolding.Tetrahedral.NearField
