import ProteinFolding.Tetrahedral.FrameForcingOppositeDistance
import ProteinFolding.Tetrahedral.FrameForcingConfiguration

/-! The actual separator bridge excludes the opposite incidence once its
entry and exit anchors occupy the already forced slot families. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

theorem capped_separator_bridge_factor (p : ConstructionParameters) (k : ℕ) :
    capWord (p.separatorWord k) = [.P, .H, .H] ++ p.separatorBridge k ++ (dimerChain 3 ++ [.P]) := by
  simp only [capWord, separatorWord, separatorBridge, dimerChain, repeatWord,
    List.cons_append, List.nil_append, List.append_assoc]

theorem entry_slot_index_bound (p : ConstructionParameters) (F : OctEdgeFrame)
    (k : ℕ) (hk : k ≤ p.bins + 1) (x : Site) (hx : x ∈ edgeBlock p.side F (6 * k) 2) :
    ∃ r ≤ 6 * p.bins + 7, x = octEdgeZigzag p.side F r := by
  obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hx
  have ht' := Finset.mem_range.mp ht
  exact ⟨6 * k + t, by omega, heq.symm⟩

theorem exit_slot_index_bound (p : ConstructionParameters) (F : OctEdgeFrame)
    (k : ℕ) (hk : k ≤ p.bins) (x : Site)
    (hx : x ∈ edgeBlock p.side F (2 * p.side - (10 * k + 13)) 6) :
    ∃ s ≤ 2 * p.side - 2, 2 * p.side - 2 - s ≤ 10 * p.bins + 11 ∧
      x = octEdgeZigzag p.side F s := by
  obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hx
  have ht' := Finset.mem_range.mp ht
  have hfamily := p.family_side_bound
  exact ⟨2 * p.side - (10 * k + 13) + t, by omega, by omega, heq.symm⟩

theorem actual_separator_opposite_impossible (p : ConstructionParameters)
    (F₁ F₂ : OctEdgeFrame) (hbig : F₂.k = F₁.a) (hsmall : F₂.j = F₁.b)
    (ha : F₂.a = F₁.j) (hb : F₂.b = F₁.k)
    (k : ℕ) (hk : k ≤ p.bins) (P : OctWordPath p.side (capWord (p.separatorWord k)))
    (entrySlot exitSlot : ℕ) (hentrySlot : entrySlot ≤ p.bins + 1) (hexitSlot : exitSlot ≤ p.bins)
    (hentry : P.site 2 ∈ edgeBlock p.side F₁ (6 * entrySlot) 2)
    (hexit : P.site (3 + (p.separatorBridge k).length) ∈
      edgeBlock p.side F₂ (2 * p.side - (10 * exitSlot + 13)) 6) : False := by
  obtain ⟨r, hr, hentryEq⟩ := p.entry_slot_index_bound F₁ entrySlot hentrySlot _ hentry
  obtain ⟨s, hs, hfarEnd, hexitEq⟩ := p.exit_slot_index_bound F₂ exitSlot hexitSlot _ hexit
  have hlen : (capWord (p.separatorWord k)).length =
      3 + (p.separatorBridge k).length + (dimerChain 3).length + 1 := by
    rw [p.capped_separator_bridge_factor k]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hbridge : 0 < (p.separatorBridge k).length := by
    rw [p.separatorBridge_length k hk]
    omega
  let n := (p.separatorBridge k).length - 1
  have hstep : ∀ i < n, tetrahedralLattice.Adj (P.site (3 + i)) (P.site (3 + (i + 1))) := by
    intro i hi
    have h := P.adjacent (3 + i) (by dsimp [n] at hi; omega)
    simpa only [Nat.add_assoc] using h
  have hstart := P.adjacent 2 (by omega)
  rw [hentryEq] at hstart
  have hend := P.adjacent (3 + n) (by dsimp [n]; omega)
  have hendIndex : 3 + n + 1 = 3 + (p.separatorBridge k).length := by dsimp [n]; omega
  rw [hendIndex, hexitEq] at hend
  exact p.opposite_frame_anchor_path_impossible k hk F₁ F₂ hbig hsmall ha hb r s hr hs hfarEnd
    (fun i => P.site (3 + i)) n hstep hstart hend le_rfl

theorem actual_frame_shared_small_face (p : ConstructionParameters) (Pframe : OctWordPath p.side p.frameWord)
    (F : ActualFrameConfiguration p.side (hSupport p.frameWord Pframe.toFold)
      p.frameGaps1 p.frameGaps2 Pframe.site p.framePart1.length)
    (k : ℕ) (hk : k ≤ p.bins) (Psep : OctWordPath p.side (capWord (p.separatorWord k)))
    (entrySlot exitSlot : ℕ) (hentrySlot : entrySlot ≤ p.bins + 1) (hexitSlot : exitSlot ≤ p.bins)
    (hentry : Psep.site 2 ∈ edgeBlock p.side F.first (6 * entrySlot) 2)
    (hexit : Psep.site (3 + (p.separatorBridge k).length) ∈
      edgeBlock p.side F.second (2 * p.side - (10 * exitSlot + 13)) 6) :
    F.second.j = F.first.j ∧ F.second.a = F.first.b := by
  rcases F.incidence with h | h
  · exact h
  · exact (p.actual_separator_opposite_impossible F.first F.second F.next_big h.1 h.2 F.next_end_face
      k hk Psep entrySlot exitSlot hentrySlot hexitSlot hentry hexit).elim

end ProteinFolding.Tetrahedral.ConstructionParameters
