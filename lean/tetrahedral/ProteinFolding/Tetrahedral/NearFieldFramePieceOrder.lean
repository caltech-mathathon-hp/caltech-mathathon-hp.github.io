import ProteinFolding.Tetrahedral.NearFieldFramePieces
import Mathlib.Data.List.FinRange

/-! The retained runs and links in the exact order of the builder's frame word. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def frameSlotPair (p : ConstructionParameters) (b : Bool) (t : Fin (p.bins + 1)) :
    List (FrameCoreIndex p) := [.inr (.inr (b, t)), .inl (.inr (b, t))]

def frameEntryPairs (p : ConstructionParameters) : List (FrameCoreIndex p) :=
  (List.finRange p.bins).flatMap (fun t => frameSlotPair p false t.castSucc)

def frameExitPairs (p : ConstructionParameters) : List (FrameCoreIndex p) :=
  (List.finRange (p.bins + 1)).reverse.flatMap (frameSlotPair p true)

def frameCoreOrder (p : ConstructionParameters) : List (FrameCoreIndex p) :=
  [.inl (.inl 0), .inr (.inl 0), .inl (.inl 1)] ++ frameEntryPairs p ++
    (frameSlotPair p false (Fin.last p.bins) ++
      [.inr (.inl 1), .inl (.inl 2), .inr (.inl 2), .inl (.inl 3)]) ++
    frameExitPairs p ++ [.inr (.inl 3), .inl (.inl 4)]

theorem frameSlotPairs_nodup (p : ConstructionParameters) (b : Bool)
    (ts : List (Fin (p.bins + 1))) (hts : ts.Nodup) :
    (ts.flatMap (frameSlotPair p b)).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun t _ => by simp [frameSlotPair], ?_⟩
  apply hts.imp
  intro t u hne
  apply List.disjoint_left.mpr
  intro x hx hy
  simp [frameSlotPair] at hx hy
  rcases hx with rfl | rfl <;> simp_all

theorem mem_frameEntryPairs (p : ConstructionParameters) (x : FrameCoreIndex p) :
    x ∈ frameEntryPairs p ↔ ∃ t : Fin p.bins,
      x = .inr (.inr (false, t.castSucc)) ∨ x = .inl (.inr (false, t.castSucc)) := by
  simp [frameEntryPairs, frameSlotPair, List.mem_flatMap, List.mem_finRange]

theorem mem_frameExitPairs (p : ConstructionParameters) (x : FrameCoreIndex p) :
    x ∈ frameExitPairs p ↔ ∃ t : Fin (p.bins + 1),
      x = .inr (.inr (true, t)) ∨ x = .inl (.inr (true, t)) := by
  simp [frameExitPairs, frameSlotPair, List.mem_flatMap, List.mem_finRange]

theorem frameEntryPairs_nodup (p : ConstructionParameters) : (frameEntryPairs p).Nodup := by
  have hts := (List.nodup_finRange p.bins).map (Fin.castSucc_injective p.bins)
  simpa only [frameEntryPairs, List.flatMap_map, Function.comp_def] using
    frameSlotPairs_nodup p false ((List.finRange p.bins).map Fin.castSucc) hts

theorem frameExitPairs_nodup (p : ConstructionParameters) : (frameExitPairs p).Nodup :=
  frameSlotPairs_nodup p true _ (List.nodup_reverse.mpr (List.nodup_finRange _))

theorem frameCoreOrder_nodup (p : ConstructionParameters) : (frameCoreOrder p).Nodup := by
  have he := frameEntryPairs_nodup p
  have hx := frameExitPairs_nodup p
  simp [frameCoreOrder, List.nodup_append, he, hx, frameSlotPair,
    mem_frameEntryPairs, mem_frameExitPairs]

def frameCorePieces (p : ConstructionParameters) : List PositionedWord :=
  (frameCoreOrder p).map (frameCorePiece p)

theorem frameCorePieces_pairwise (p : ConstructionParameters) :
    (frameCorePieces p).Pairwise (fun a b => Disjoint (foldSites a.fold) (foldSites b.fold)) := by
  apply List.pairwise_map.mpr
  exact (frameCoreOrder_nodup p).imp (fun hne => frameCorePieces_disjoint p _ _ hne)

end ProteinFolding.Tetrahedral.NearField
