import ProteinFolding.Tetrahedral.NearFieldFramePortFormulas
import ProteinFolding.Tetrahedral.NearFieldSeparatorChains

/-! All finite endpoint classification takes place in Bool × Nat. Mapping
these metadata through a walk uses opaque generic function lemmas. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 150000

def framePortMetadata (m f : ℕ) (kind : Fin 6) (last : Bool) : Bool × ℕ :=
  if kind = 0 then (false, if last then 3 else 0)
  else if kind = 1 then (false, if last then f + 3 else f)
  else if kind = 2 then (false, if last then 2 * m - 2 else 2 * m - 4)
  else if kind = 3 then (true, if last then 2 * m - 4 else 2 * m - 2)
  else if kind = 4 then (true, if last then f else f + 7)
  else (true, if last then 0 else 2)

def frameMetadataPair (d : Bool × ℕ) : OctEdgeFrame × ℕ :=
  if d.1 then (exitEdgeFrame, d.2) else (entryEdgeFrame, d.2)

def interpretFramePort {α : Type*} (u v : ℕ → α) (d : Bool × ℕ) : α :=
  if d.1 then v d.2 else u d.2

theorem framePortMetadata_eq_original (m f : ℕ) (kind : Fin 6) (last : Bool) :
    (if last then (nearFrameRouteFrame kind, nearFrameEndIndex m f kind)
     else (nearFrameRouteFrame kind, nearFrameStartIndex m f kind)) =
      frameMetadataPair (framePortMetadata m f kind last) := by
  fin_cases kind <;> cases last <;>
    norm_num [framePortMetadata, frameMetadataPair, nearFrameRouteFrame, nearFrameStartIndex,
      nearFrameEndIndex, Fin.ext_iff]

theorem map_pair_choice {α β γ : Type*} (g : α → β → γ) (b : Bool) (a : α) (r s : β) :
    g (if b then (a, r) else (a, s)).1 (if b then (a, r) else (a, s)).2 =
      if b then g a r else g a s := by cases b <;> rfl

theorem map_frameMetadataPair {α : Type*} (g : OctEdgeFrame → ℕ → α) (d : Bool × ℕ) :
    g (frameMetadataPair d).1 (frameMetadataPair d).2 =
      interpretFramePort (g entryEdgeFrame) (g exitEdgeFrame) d := by
  rcases d with ⟨b, r⟩
  cases b <;> rfl

theorem frameEndpoint_eq_metadata (m f : ℕ) (kind : Fin 6) (last : Bool) :
    (if last then frameEndH m f kind else frameStartH m f kind) =
      interpretFramePort (octEdgeZigzag m entryEdgeFrame) (octEdgeZigzag m exitEdgeFrame)
        (framePortMetadata m f kind last) := by
  have h := congrArg (fun d : OctEdgeFrame × ℕ => octEdgeZigzag m d.1 d.2)
    (framePortMetadata_eq_original m f kind last)
  simpa only [map_pair_choice, map_frameMetadataPair, frameStartH, frameEndH] using h

theorem interpretFramePort_not_mem {α : Type*} [DecidableEq α] (u v : ℕ → α) (d : Bool × ℕ)
    (T : Finset α) (hu : d.1 = false → u d.2 ∉ T) (hv : d.1 = true → v d.2 ∉ T) :
    interpretFramePort u v d ∉ T := by
  rcases d with ⟨b, r⟩
  cases b
  · exact hu rfl
  · exact hv rfl

theorem framePortMetadata_index_lt (m f : ℕ) (hm : 3 ≤ m) (kind : Fin 6) (last : Bool)
    (hf : (f : ℤ) + 10 ≤ octRadius m) : (framePortMetadata m f kind last).2 < 2 * m - 1 := by
  have hfb : f + 10 ≤ 2 * m - 2 := by dsimp [octRadius] at hf; omega
  fin_cases kind <;> cases last <;> norm_num [framePortMetadata, Fin.ext_iff] <;> omega

theorem framePortMetadata_entry_allowed (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (f : ℕ) (kind : Fin 6) (last : Bool) (hf : (f : ℤ) + 10 ≤ octRadius p.side)
    (hslot : kind = 1 → f % 6 = 5) :
    if (framePortMetadata p.side f kind last).1 then
      (framePortMetadata p.side f kind last).2 < 2 * p.side - 1
    else ∀ t, t < 2 → 6 * (k + 1) + t ≠ (framePortMetadata p.side f kind last).2 := by
  have hm := p.side_ge
  have ht := p.entry_column_triangle_room k hk
  have hfb : f + 10 ≤ 2 * p.side - 2 := by dsimp [octRadius] at hf; omega
  fin_cases kind
  all_goals try have hfslot := hslot rfl
  all_goals cases last <;> norm_num [framePortMetadata, Fin.ext_iff]
  all_goals first | (intro t ht; omega) | omega

theorem framePortMetadata_exit_allowed (p : ConstructionParameters) (k f : ℕ) (kind : Fin 6) (last : Bool)
    (hf : (f : ℤ) + 10 ≤ octRadius p.side) (hslot : kind = 4 → f % 10 = 5) :
    if (framePortMetadata p.side f kind last).1 then
      ∀ t, t < 6 → 10 * p.exitSlot k + 6 + t ≠ (framePortMetadata p.side f kind last).2
    else (framePortMetadata p.side f kind last).2 < 2 * p.side - 1 := by
  have hm := p.side_ge
  have ht := p.exit_column_triangle_room k
  have hfb : f + 10 ≤ 2 * p.side - 2 := by dsimp [octRadius] at hf; omega
  fin_cases kind
  all_goals try have hfslot := hslot rfl
  all_goals cases last <;> norm_num [framePortMetadata, Fin.ext_iff]
  all_goals first | (intro t ht; omega) | omega

end ProteinFolding.Tetrahedral.NearField
