import ProteinFolding.Tetrahedral.FrameForcing
import ProteinFolding.Tetrahedral.FrameForcingSeparatorCentre

/-! All three chains in each separator have one literal occurrence.  Its
two tether anchors lie in the exhausted entry and exit slot families. -/

namespace ProteinFolding.Tetrahedral.ReductionDimerProvenance

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem separator_three_witnesses (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (gaps : ℕ → ℕ) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) (k : ℕ) (hk : k ≤ p.bins) :
    let c := (catalogue p items bulkLengths gaps hbulk).val
    ∃ (pre post : Sequence) (iE iC iX : c.Index),
      p.reductionWord items bulkLengths gaps = pre ++ capWord (p.separatorWord k) ++ post ∧
      c.q iE = 1 ∧ c.q iC = 2 ∧ c.q iX = 3 ∧
      (c.pre iE).length = pre.length ∧
      (c.pre iC).length = pre.length + p.entryTether k + 2 ∧
      (c.pre iX).length = pre.length + separatorExitOffset p k := by
  dsimp only
  obtain ⟨pre, post, hfactor, ⟨e⟩⟩ := body_inclusion p items bulkLengths gaps hbulk
    (separatorBody p items k hk) (separatorBody_mem p items bulkLengths hbulk k hk)
  obtain ⟨i, j, hqi, hqj, _, _, hpi, hpj⟩ := separator_offsets p items k hk
  obtain ⟨c, hqc, _, hpc⟩ := separator_centre_offset p items k hk
  refine ⟨pre, post, e.map i, e.map c, e.map j, ?_, (e.q_eq i).trans hqi,
    (e.q_eq c).trans hqc, (e.q_eq j).trans hqj, ?_, ?_, ?_⟩
  · simpa only [separatorBody_body] using hfactor
  · rw [e.offset_eq, hpi, Nat.add_zero]
  · rw [e.offset_eq, hpc]; omega
  · rw [e.offset_eq, hpj]

end ProteinFolding.Tetrahedral.ReductionDimerProvenance

namespace ProteinFolding.Tetrahedral.ConstructionParameters

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem catalogue_separator_anchor_points (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (framePre framePost : Sequence)
    (hframe : p.reductionWord items bulkLengths gaps = framePre ++ p.frameWord ++ framePost)
    (F : ActualFrameConfiguration p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport framePre p.frameWord framePost hframe).toFold)
      p.frameGaps1 p.frameGaps2
      (OctWordPath.ofFoldOccurrence f p.side hsupport framePre p.frameWord framePost hframe).site p.framePart1.length)
    {α : Type} (c : DimerCatalogue α (p.reductionWord items bulkLengths gaps))
    (hpositive : ∀ i, 0 < c.q i)
    (hcount₁ : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 1)).card = p.bins + 1)
    (hcount₃ : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 3)).card = p.bins + 1)
    (k : ℕ) (pre post : Sequence)
    (hsep : p.reductionWord items bulkLengths gaps = pre ++ capWord (p.separatorWord k) ++ post)
    (iE iX : c.Index) (hE : c.q iE = 1) (hX : c.q iX = 3)
    (hpreE : (c.pre iE).length = pre.length)
    (hpreX : (c.pre iX).length = pre.length + ReductionDimerProvenance.separatorExitOffset p k) :
    ∃ r s, r ≤ 6 * p.bins + 7 ∧ s ≤ 2 * p.side - 2 ∧
      2 * p.side - 2 - s ≤ 10 * p.bins + 11 ∧
      (OctWordPath.ofFoldOccurrence f p.side hsupport pre (capWord (p.separatorWord k)) post hsep).site 2 =
        octEdgeZigzag p.side F.first r ∧
      (OctWordPath.ofFoldOccurrence f p.side hsupport pre (capWord (p.separatorWord k)) post hsep).site
        (p.entryTether k + p.exitTether k + 10) = octEdgeZigzag p.side F.second s := by
  letI := c.finiteIndex
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
  let Psep := OctWordPath.ofFoldOccurrence f p.side hsupport pre (capWord (p.separatorWord k)) post hsep
  have hentryEq : (c.chainPairs f iE).point (e, true) = Psep.site 2 := by
    change (factorDimerPairs _ f (c.pre iE) (c.post iE) (c.q iE) (c.factor iE)).point (e, true) = _
    rw [factorDimerPairs_point _ f p.side hsupport]
    change foldSiteAt f ((c.pre iE).length + (5 * 0 + if true then 2 else 1)) =
      foldSiteAt f (pre.length + 2)
    simp only [Nat.mul_zero, Nat.zero_add, ↓reduceIte, hpreE]
  have hexitEq : (c.chainPairs f iX).point (x, false) =
      Psep.site (p.entryTether k + p.exitTether k + 10) := by
    change (factorDimerPairs _ f (c.pre iX) (c.post iX) (c.q iX) (c.factor iX)).point (x, false) = _
    rw [factorDimerPairs_point _ f p.side hsupport]
    change foldSiteAt f ((c.pre iX).length + (5 * 0 + if false then 2 else 1)) =
      foldSiteAt f (pre.length + (p.entryTether k + p.exitTether k + 10))
    congr 1
    simp only [Nat.mul_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte, hpreX,
      ReductionDimerProvenance.separatorExitOffset]
    omega
  rw [hentryEq] at hentry
  rw [hexitEq] at hexit
  obtain ⟨r, hr, her⟩ := p.entry_slot_index_bound F.first (entrySlot.val + 1) (by omega) _ hentry
  obtain ⟨s, hs, hdef, hxs⟩ := p.exit_slot_index_bound F.second exitSlot.val (by omega) _ hexit
  exact ⟨r, s, hr, hs, hdef, her, hxs⟩

theorem actual_separator_anchors (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hpos : ∀ s ∈ items, 0 < s)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (framePre framePost : Sequence)
    (hframe : p.reductionWord items bulkLengths gaps = framePre ++ p.frameWord ++ framePost)
    (F : ActualFrameConfiguration p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport framePre p.frameWord framePost hframe).toFold)
      p.frameGaps1 p.frameGaps2
      (OctWordPath.ofFoldOccurrence f p.side hsupport framePre p.frameWord framePost hframe).site p.framePart1.length)
    (k : ℕ) (hk : k ≤ p.bins) :
    let c := (ReductionDimerProvenance.catalogue p items bulkLengths gaps hbulk).val
    ∃ (pre post : Sequence) (hsep : p.reductionWord items bulkLengths gaps =
        pre ++ capWord (p.separatorWord k) ++ post) (iC : c.Index),
      c.q iC = 2 ∧ (c.pre iC).length = pre.length + p.entryTether k + 2 ∧
      ∃ r s, r ≤ 6 * p.bins + 7 ∧ s ≤ 2 * p.side - 2 ∧
        2 * p.side - 2 - s ≤ 10 * p.bins + 11 ∧
        (OctWordPath.ofFoldOccurrence f p.side hsupport pre (capWord (p.separatorWord k)) post hsep).site 2 =
          octEdgeZigzag p.side F.first r ∧
        (OctWordPath.ofFoldOccurrence f p.side hsupport pre (capWord (p.separatorWord k)) post hsep).site
          (p.entryTether k + p.exitTether k + 10) = octEdgeZigzag p.side F.second s := by
  let c := (ReductionDimerProvenance.catalogue p items bulkLengths gaps hbulk).val
  have hpositive := ReductionDimerProvenance.chain_positive p items bulkLengths gaps hbulk hpos
  have hcount₁ := ReductionDimerProvenance.small_chain_card p items bulkLengths gaps hbulk hpos 1 (Or.inl rfl)
  have hcount₃ := ReductionDimerProvenance.small_chain_card p items bulkLengths gaps hbulk hpos 3 (Or.inr (Or.inr rfl))
  obtain ⟨pre, post, iE, iC, iX, hsep, hE, hC, hX, hpreE, hpreC, hpreX⟩ :=
    ReductionDimerProvenance.separator_three_witnesses p items bulkLengths gaps hbulk k hk
  change c.q iE = 1 at hE
  change c.q iC = 2 at hC
  change c.q iX = 3 at hX
  change (c.pre iE).length = pre.length at hpreE
  change (c.pre iC).length = pre.length + p.entryTether k + 2 at hpreC
  change (c.pre iX).length = pre.length + ReductionDimerProvenance.separatorExitOffset p k at hpreX
  refine ⟨pre, post, hsep, iC, hC, hpreC, ?_⟩
  exact p.catalogue_separator_anchor_points items bulkLengths gaps htotal hbulk f hsupport hvertices
    framePre framePost hframe F c hpositive hcount₁ hcount₃ k pre post hsep iE iX hE hX hpreE hpreX

end ProteinFolding.Tetrahedral.ConstructionParameters
