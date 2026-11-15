import ProteinFolding.Tetrahedral.NearFieldFrameHRunSeparation
import ProteinFolding.Tetrahedral.NearFieldFrameLinkFamily

/-! The literal H-runs and P-links as one finite family of positioned words. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def frameLinkWord (p : ConstructionParameters) (i : FrameLinkIndex p) : Sequence :=
  List.replicate (nearFrameLength (frameLinkKind i) - 2) .P

def frameLinkWordFold (p : ConstructionParameters) (i : FrameLinkIndex p) :
    Fold tetrahedralLattice (frameLinkWord p i).length :=
  (frameLinkFold p i).onLength (by simp [frameLinkWord])

theorem frameLinkWordFold_pos (p : ConstructionParameters) (i : FrameLinkIndex p)
    (r : Fin (frameLinkWord p i).length) :
    (frameLinkWordFold p i).pos r =
      (frameLinkFold p i).pos ⟨r.val, by simpa only [frameLinkWord, List.length_replicate] using r.isLt⟩ := by
  apply congrArg (frameLinkFold p i).pos
  exact Fin.ext rfl

def frameLinkFirst (p : ConstructionParameters) (i : FrameLinkIndex p) : Site :=
  (frameLinkFold p i).pos ⟨0, by have h := nearFrameLength_ge_five (frameLinkKind i); omega⟩

def frameLinkLast (p : ConstructionParameters) (i : FrameLinkIndex p) : Site :=
  (frameLinkFold p i).pos ⟨nearFrameLength (frameLinkKind i) - 3,
    by have h := nearFrameLength_ge_five (frameLinkKind i); omega⟩

def frameLinkPiece (p : ConstructionParameters) (i : FrameLinkIndex p) : PositionedWord where
  word := frameLinkWord p i
  fold := frameLinkWordFold p i
  length_pos := by have h := nearFrameLength_ge_five (frameLinkKind i); simp only [frameLinkWord, List.length_replicate]; omega
  first := frameLinkFirst p i
  last := frameLinkLast p i
  first_eq r hr := by
    rw [frameLinkWordFold_pos]
    apply congrArg (frameLinkFold p i).pos
    exact Fin.ext hr
  last_eq r hr := by
    rw [frameLinkWordFold_pos]
    apply congrArg (frameLinkFold p i).pos
    apply Fin.ext
    change r.val = nearFrameLength (frameLinkKind i) - 3
    change r.val + 1 = (frameLinkWord p i).length at hr
    simp only [frameLinkWord, List.length_replicate] at hr
    have h := nearFrameLength_ge_five (frameLinkKind i)
    omega

theorem frameLinkPiece_first_seam (p : ConstructionParameters) (i : FrameLinkIndex p) :
    tetrahedralLattice.Adj
      (octEdgeZigzag p.side (nearFrameRouteFrame (frameLinkKind i))
        (nearFrameStartIndex p.side (frameLinkParameter i) (frameLinkKind i)))
      (frameLinkPiece p i).first :=
  framePFold_first_seam p.side (frameLinkParameter i) (frameLinkKind i)
    (frameLinkParameter_odd p i) (frameLinkParameter_ge p i) (frameLinkParameter_room p i) _ rfl

theorem frameLinkPiece_last_seam (p : ConstructionParameters) (i : FrameLinkIndex p) :
    tetrahedralLattice.Adj (frameLinkPiece p i).last
      (octEdgeZigzag p.side (nearFrameRouteFrame (frameLinkKind i))
        (nearFrameEndIndex p.side (frameLinkParameter i) (frameLinkKind i))) := by
  apply framePFold_last_seam p.side (frameLinkParameter i) (frameLinkKind i)
    (frameLinkParameter_odd p i) (frameLinkParameter_ge p i) (frameLinkParameter_room p i)
  change nearFrameLength (frameLinkKind i) - 3 + 1 = nearFrameLength (frameLinkKind i) - 2
  have h := nearFrameLength_ge_five (frameLinkKind i)
  omega

abbrev FrameCoreIndex (p : ConstructionParameters) := FrameHRunIndex p ⊕ FrameLinkIndex p

def frameCorePiece (p : ConstructionParameters) : FrameCoreIndex p → PositionedWord
  | .inl i => frameHRunPiece p i
  | .inr i => frameLinkPiece p i

theorem frameLinkWordFold_sites (p : ConstructionParameters) (i : FrameLinkIndex p) :
    foldSites (frameLinkWordFold p i) = foldSites (frameLinkFold p i) := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := (mem_foldSites _ _).mp hx
    exact (mem_foldSites _ _).mpr ⟨_, (frameLinkWordFold_pos p i r).symm.trans hr⟩
  · intro hx
    obtain ⟨r, hr⟩ := (mem_foldSites _ _).mp hx
    refine (mem_foldSites _ _).mpr ⟨⟨r.val, by simpa only [frameLinkWord, List.length_replicate] using r.isLt⟩, ?_⟩
    rw [frameLinkWordFold_pos]
    exact hr

theorem frameCorePieces_disjoint (p : ConstructionParameters) (i j : FrameCoreIndex p) (hne : i ≠ j) :
    Disjoint (foldSites (frameCorePiece p i).fold) (foldSites (frameCorePiece p j).fold) := by
  rcases i with i | i <;> rcases j with j | j
  · exact frameHRunFolds_disjoint p i j (fun heq => hne (congrArg Sum.inl heq))
  · change Disjoint (foldSites (frameHRunFold p i)) (foldSites (frameLinkWordFold p j))
    rw [frameLinkWordFold_sites]
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨r, rfl⟩ := (mem_foldSites _ _).mp hx
    obtain ⟨s, hs⟩ := (mem_foldSites _ _).mp hy
    have hoct := frameHRunFold_mem_oct p i r
    rw [← hs] at hoct
    exact framePFold_outside _ _ _ _ s hoct
  · change Disjoint (foldSites (frameLinkWordFold p i)) (foldSites (frameHRunFold p j))
    rw [frameLinkWordFold_sites]
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨r, hr⟩ := (mem_foldSites _ _).mp hx
    obtain ⟨s, rfl⟩ := (mem_foldSites _ _).mp hy
    have hoct := frameHRunFold_mem_oct p j s
    rw [← hr] at hoct
    exact framePFold_outside _ _ _ _ r hoct
  · change Disjoint (foldSites (frameLinkWordFold p i)) (foldSites (frameLinkWordFold p j))
    rw [frameLinkWordFold_sites, frameLinkWordFold_sites]
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨r, hr⟩ := (mem_foldSites _ _).mp hx
    obtain ⟨s, hs⟩ := (mem_foldSites _ _).mp hy
    exact frameLinkFolds_disjoint p i j (fun heq => hne (congrArg Sum.inr heq)) r s (hr.trans hs.symm)

end ProteinFolding.Tetrahedral.NearField
