import ProteinFolding.Tetrahedral.FrameForcingSlotGuards

/-! A concrete configuration derived from the literal frame, retaining both
incidence alternatives and every forced H index for subsequent soundness. -/

namespace ProteinFolding.Tetrahedral

structure ActualFrameConfiguration (m : ℕ) (H : Finset Site) (g₁ g₂ : List ℕ)
    (site : ℕ → Site) (middle : ℕ) extends ForcedFrameFamily m H g₁ g₂ where
  start_first : site 1 = octEdgeStart m first
  end_first : site middle = octEdgeZigzag m first (2 * m - 2)
  start_second : site middle = octEdgeStart m second
  indices_first : ∀ j ≤ g₁.length, site (1 + frameHOffset g₁ j) =
    octEdgeZigzag m first (frameAdvanceAt g₁ j)
  indices_second : ∀ j ≤ g₂.length, site (middle + frameHOffset g₂ j) =
    octEdgeZigzag m second (frameAdvanceAt g₂ j)
  next_big : second.k = first.a
  next_end_face : second.b = first.k
  incidence : (second.j = first.j ∧ second.a = first.b) ∨
    (second.j = first.b ∧ second.a = first.j)

namespace ConstructionParameters

theorem frameWord_actual_configuration (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord) :
    Nonempty (ActualFrameConfiguration p.side (hSupport p.frameWord P.toFold)
      p.frameGaps1 p.frameGaps2 P.site p.framePart1.length) := by
  obtain ⟨F₁, F₂, hs, he, hs₂, hf₁, hf₂, hdistinct, hbig, hface, hcases⟩ := p.frame_word_forced_incidence P
  refine ⟨{
    first := F₁
    second := F₂
    distinct := hdistinct
    allowed₁ := p.frameGaps1_allowed
    allowed₂ := p.frameGaps2_allowed
    budget₁ := p.frameGaps1_budget
    budget₂ := p.frameGaps2_budget
    nodes₁ := ?_
    nodes₂ := ?_
    support_cases := ?_
    start_first := hs
    end_first := he
    start_second := hs₂
    indices_first := hf₁
    indices_second := hf₂
    next_big := hbig
    next_end_face := hface
    incidence := hcases }⟩
  · intro j hj
    unfold frameAdvanceAt
    rw [← hf₁ j hj]
    exact P.site_mem_Hsupport _ (p.frameWord_gap1_H j hj)
  · intro j hj
    unfold frameAdvanceAt
    rw [← hf₂ j hj]
    exact P.site_mem_Hsupport _ (p.frameWord_gap2_H j hj)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := (mem_hSupport p.frameWord P.toFold x).mp hx
    have hi' := List.getElem?_eq_some_iff.mpr ⟨i.isLt, hi⟩
    rcases p.frame_word_H_cases i.val hi' with ⟨j, hj, heq⟩ | ⟨j, hj, heq⟩
    · exact Or.inl ⟨j, hj, by simpa only [OctWordPath.toFold, heq] using hf₁ j hj⟩
    · exact Or.inr ⟨j, hj, by simpa only [OctWordPath.toFold, heq] using hf₂ j hj⟩

theorem actual_frame_family_slots_covered (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (pre post : Sequence) (heq : p.reductionWord items bulkLengths gaps = pre ++ p.frameWord ++ post)
    (F : ForcedFrameFamily p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq).toFold)
      p.frameGaps1 p.frameGaps2) :
    (∀ k, 1 ≤ k → k ≤ p.bins + 1 → edgeBlock p.side F.first (6 * k) 2 ⊆
      (foldDimerPairs (p.reductionWord items bulkLengths gaps) f).covered) ∧
    (∀ k, k ≤ p.bins → edgeBlock p.side F.second (2 * p.side - (10 * k + 13)) 6 ⊆
      (foldDimerPairs (p.reductionWord items bulkLengths gaps) f).covered) := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  constructor
  · intro k hklo hkhi
    obtain ⟨hW, hclosed⟩ := p.forced_family_entry_slot _ F k hklo hkhi
    exact p.reductionWord_even_component_covered items bulkLengths gaps htotal hbulk f hsupport hvertices
      pre post heq _ hW (by rw [edgeBlock_card p.side hm F.first]) hclosed
  · intro k hk
    obtain ⟨hW, hclosed⟩ := p.forced_family_exit_slot _ F k hk
    exact p.reductionWord_even_component_covered items bulkLengths gaps htotal hbulk f hsupport hvertices
      pre post heq _ hW (by rw [edgeBlock_card p.side hm F.second]) hclosed

end ConstructionParameters

end ProteinFolding.Tetrahedral
