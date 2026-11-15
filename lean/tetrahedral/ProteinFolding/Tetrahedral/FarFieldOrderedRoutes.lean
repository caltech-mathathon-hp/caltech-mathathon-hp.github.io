import ProteinFolding.Tetrahedral.FarFieldObstacleAvoidance

namespace ProteinFolding.Tetrahedral.FarField

/-- Lemma F with the original requested ordering of each pair, obtained by
reversing the actual paths when their private slabs have the opposite order. -/
theorem paired_cap_routes_ordered {w k : ℕ} (d : WireData w) (c : CapEntryData d)
    (e : Pairing w k) (O : Set Site) (o : LocalObstacleData c O)
    (m : ℕ) (hH : d.H = 20 * m + 21)
    (hxlow : ∀ i, -d.H ≤ wireBaseXs d.quadrants d.bases i)
    (L : Fin k → ℕ) (hL : ∀ r, uniformLinkerLength m w ≤ L r)
    (hparity : ∀ r, CapParity (c.caps (e.first r)) (c.caps (e.second r)) (L r)) :
    ∃ f : ∀ r : Fin k, Fold tetrahedralLattice (L r),
      (∀ r i, i.val = 0 → (f r).pos i = c.caps (e.first r)) ∧
      (∀ r i, i.val + 1 = L r → (f r).pos i = c.caps (e.second r)) ∧
      (∀ r s, r ≠ s → Disjoint (Set.range (f r).pos) (Set.range (f s).pos)) ∧
      (∀ r s, s ∈ Set.range (f r).pos → s ∈ O → s = c.caps (e.first r) ∨ s = c.caps (e.second r)) := by
  obtain ⟨f, hfirst, hlast, hdisj, havoid⟩ :=
    paired_cap_routes_avoiding d c e O o m hH hxlow L hL hparity
  have hpos (r : Fin k) : 0 < L r := by
    have h := hL r
    unfold uniformLinkerLength at h
    omega
  let g (r : Fin k) : Fold tetrahedralLattice (L r) :=
    if d.slabs (e.first r) < d.slabs (e.second r) then f r else (f r).reverse
  have hrange (r : Fin k) : Set.range (g r).pos ⊆ Set.range (f r).pos := by
    rintro s ⟨a, rfl⟩
    by_cases h : d.slabs (e.first r) < d.slabs (e.second r)
    · exact ⟨a, by simp only [g, if_pos h]⟩
    · exact ⟨a.rev, by simp only [g, if_neg h]; rfl⟩
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro r a ha
    by_cases h : d.slabs (e.first r) < d.slabs (e.second r)
    · have hf := hfirst r a ha
      simpa only [g, if_pos h, Pairing.lower] using hf
    · have hr := reverse_first (f r) (hpos r) a ha
      have hf := hlast r ⟨L r - 1, by have hp := hpos r; omega⟩
        (by change L r - 1 + 1 = L r; have hp := hpos r; omega)
      have heq := hr.trans hf
      simpa only [g, if_neg h, Pairing.upper] using heq
  · intro r a ha
    by_cases h : d.slabs (e.first r) < d.slabs (e.second r)
    · have hf := hlast r a ha
      simpa only [g, if_pos h, Pairing.upper] using hf
    · have hr := reverse_last (f r) (hpos r) a ha
      have hf := hfirst r ⟨0, hpos r⟩ rfl
      have heq := hr.trans hf
      simpa only [g, if_neg h, Pairing.lower] using heq
  · intro r s hrs
    exact (hdisj r s hrs).mono (hrange r) (hrange s)
  · intro r s hs hO
    have ha := havoid r s (hrange r hs) hO
    by_cases h : d.slabs (e.first r) < d.slabs (e.second r)
    · simpa only [Pairing.lower, Pairing.upper, if_pos h] using ha
    · simpa only [Pairing.lower, Pairing.upper, if_neg h, or_comm] using ha

end ProteinFolding.Tetrahedral.FarField
