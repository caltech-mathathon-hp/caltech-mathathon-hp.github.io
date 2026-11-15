import ProteinFolding.Tetrahedral.FrameForcingCataloguePoints
import ProteinFolding.Tetrahedral.FrameForcingSeparatorBridge

/-! Derive the concrete shared-small-face configuration from complete
declared-chain data and the two anchors of the first actual separator. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

def HasSharedFrame (p : ConstructionParameters) (S : Sequence)
    (f : Fold tetrahedralLattice S.length) (hsupport : hSupport S f = octahedron p.side) : Prop :=
  ∃ (pre post : Sequence) (hframe : S = pre ++ p.frameWord ++ post),
    ∃ F : ActualFrameConfiguration p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe).toFold)
      p.frameGaps1 p.frameGaps2
      (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe).site p.framePart1.length,
      F.second.j = F.first.j ∧ F.second.a = F.first.b

theorem shared_frame_of_actual_catalogue (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    {α : Type} (c : DimerCatalogue α (p.reductionWord items bulkLengths gaps))
    (hpositive : ∀ i, 0 < c.q i)
    (hcount₁ : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 1)).card = p.bins + 1)
    (hcount₃ : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 3)).card = p.bins + 1)
    (sepPre sepPost : Sequence)
    (hsep : p.reductionWord items bulkLengths gaps = sepPre ++ capWord (p.separatorWord 0) ++ sepPost)
    (iE iX : c.Index) (hE : c.q iE = 1) (hX : c.q iX = 3)
    (hpreE : (c.pre iE).length = sepPre.length)
    (hpreX : (c.pre iX).length = sepPre.length + 2 + p.entryTether 0 + 7 + p.exitTether 0) :
    p.HasSharedFrame (p.reductionWord items bulkLengths gaps) f hsupport := by
  letI := c.finiteIndex
  obtain ⟨framePre, framePost, hframe⟩ := p.reductionWord_frame_occurrence items bulkLengths gaps
  let Pframe := OctWordPath.ofFoldOccurrence f p.side hsupport framePre p.frameWord framePost hframe
  obtain ⟨F⟩ := p.frameWord_actual_configuration Pframe
  have hsingles := p.actual_catalogue_singleton_sites items bulkLengths gaps htotal hbulk f hsupport hvertices
    framePre framePost hframe F.toForcedFrameFamily c hpositive hcount₁
  have hexits := p.actual_catalogue_exit_sites items bulkLengths gaps htotal hbulk f hsupport hvertices
    framePre framePost hframe F.toForcedFrameFamily c hpositive hcount₁ hcount₃
  let e : Fin (c.q iE) := ⟨0, by omega⟩
  let x : Fin (c.q iX) := ⟨0, by omega⟩
  obtain ⟨entrySlot, hentry⟩ := c.chain_point_in_slot f _ _ hsingles iE
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE⟩) e true
  obtain ⟨exitSlot, hexit⟩ := c.chain_point_in_slot f _ _ hexits iX
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX⟩) x false
  let Psep := OctWordPath.ofFoldOccurrence f p.side hsupport sepPre (capWord (p.separatorWord 0)) sepPost hsep
  have hentryEq : (c.chainPairs f iE).point (e, true) = Psep.site 2 := by
    change (factorDimerPairs _ f (c.pre iE) (c.post iE) (c.q iE) (c.factor iE)).point (e, true) = _
    rw [factorDimerPairs_point _ f p.side hsupport]
    change foldSiteAt f ((c.pre iE).length + (5 * 0 + if true then 2 else 1)) =
      foldSiteAt f (sepPre.length + 2)
    simp only [Nat.mul_zero, Nat.zero_add, ↓reduceIte, hpreE]
  have hbridge : (p.separatorBridge 0).length = p.entryTether 0 + 7 + p.exitTether 0 := by
    simp only [separatorBridge, List.length_append, List.length_replicate]
    have hlen : (dimerChain 2).length = 7 := rfl
    rw [hlen]
  have hexitEq : (c.chainPairs f iX).point (x, false) = Psep.site (3 + (p.separatorBridge 0).length) := by
    change (factorDimerPairs _ f (c.pre iX) (c.post iX) (c.q iX) (c.factor iX)).point (x, false) = _
    rw [factorDimerPairs_point _ f p.side hsupport]
    change foldSiteAt f ((c.pre iX).length + (5 * 0 + if false then 2 else 1)) =
      foldSiteAt f (sepPre.length + (3 + (p.separatorBridge 0).length))
    congr 1
    simp only [Nat.mul_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, hpreX, hbridge]
    omega
  rw [hentryEq] at hentry
  rw [hexitEq] at hexit
  refine ⟨framePre, framePost, hframe, F, ?_⟩
  exact p.actual_frame_shared_small_face Pframe F 0 (by omega) Psep (entrySlot.val + 1) exitSlot.val
    (by omega) (by omega) hentry hexit

end ProteinFolding.Tetrahedral.ConstructionParameters
