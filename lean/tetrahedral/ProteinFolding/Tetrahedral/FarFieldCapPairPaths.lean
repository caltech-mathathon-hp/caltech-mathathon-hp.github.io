import ProteinFolding.Tetrahedral.FarFieldCapEntries

namespace ProteinFolding.Tetrahedral.FarField.CapEntryData

variable {w : ℕ} {d : WireData w} (c : CapEntryData d)

noncomputable def baseCapPairCount (p : RoutingPlan d) (i j : Fin w) : ℤ :=
  p.basePairCount i j + c.sites i + c.sites j - 2

theorem reverse_entry_first (j : Fin w) :
    (c.paths j).reverse.pos ⟨0, c.sites_pos j⟩ = d.armCaps j := by
  have hr := reverse_first (c.paths j) (c.sites_pos j) ⟨0, c.sites_pos j⟩ rfl
  have hc := c.last j ⟨c.sites j - 1, by have h := c.sites_pos j; omega⟩
    (by change c.sites j - 1 + 1 = c.sites j; have h := c.sites_pos j; omega)
  exact hr.trans hc

section Pair

variable {p : RoutingPlan d} {i j : Fin w} {Δ : ℕ} (m : MiddleData p i j Δ)

noncomputable def capLeftSites : ℕ := c.sites i + m.pairSites - 1

theorem capLeft_join (hne : i ≠ j) :
    (c.paths i).pos ⟨c.sites i - 1, by have h := c.sites_pos i; omega⟩ =
      (m.pairPath hne).pos ⟨0, m.pairSites_pos⟩ := by
  have hc := c.last i ⟨c.sites i - 1, by have h := c.sites_pos i; omega⟩
    (by change c.sites i - 1 + 1 = c.sites i; have h := c.sites_pos i; omega)
  exact hc.trans (m.pairPath_first hne ⟨0, m.pairSites_pos⟩ rfl).symm

theorem capLeft_intersection (hne : i ≠ j) (a : Fin (c.sites i)) (b : Fin m.pairSites)
    (heq : (c.paths i).pos a = (m.pairPath hne).pos b) : a.val + 1 = c.sites i ∧ b.val = 0 := by
  have hi : a.val + 1 = c.sites i ∧ (c.paths i).pos a = d.armCaps i := by
    rcases c.pair_intersection m hne i a b heq with h | h
    · exact h.2
    · exact False.elim (hne h.1)
  have hb := (m.pairPath hne).injective_pos
    ((heq.symm.trans hi.2).trans (m.pairPath_first hne ⟨0, m.pairSites_pos⟩ rfl).symm)
  have hbval : b.val = 0 := congrArg (fun k : Fin m.pairSites => k.val) hb
  exact ⟨hi.1, hbval⟩

noncomputable def capLeftPath (hne : i ≠ j) : Fold tetrahedralLattice (c.capLeftSites m) :=
  glue (c.paths i) (m.pairPath hne) (c.sites_pos i) m.pairSites_pos (c.capLeft_join m hne)
    (fun a b heq => c.capLeft_intersection m hne a b heq)

theorem capLeftSites_pos : 0 < c.capLeftSites m := by
  have hc := c.sites_pos i
  have hm := m.pairSites_pos
  unfold capLeftSites
  omega

theorem capLeft_first (hne : i ≠ j) (a : Fin (c.capLeftSites m)) (ha : a.val = 0) :
    (c.capLeftPath m hne).pos a = c.caps i := by
  have h := glue_first (c.paths i) (m.pairPath hne) (c.sites_pos i) m.pairSites_pos (c.capLeft_join m hne)
    (fun a b heq => c.capLeft_intersection m hne a b heq) a ha
  exact h.trans (c.first i ⟨0, c.sites_pos i⟩ rfl)

theorem capLeft_last (hne : i ≠ j) (a : Fin (c.capLeftSites m)) (ha : a.val + 1 = c.capLeftSites m) :
    (c.capLeftPath m hne).pos a = d.armCaps j := by
  have h := glue_last (c.paths i) (m.pairPath hne) (c.sites_pos i) m.pairSites_pos (c.capLeft_join m hne)
    (fun a b heq => c.capLeft_intersection m hne a b heq) a ha
  exact h.trans (m.pairPath_last hne _
    (by change m.pairSites - 1 + 1 = m.pairSites; have h := m.pairSites_pos; omega))

theorem capLeft_range (hne : i ≠ j) : Set.range (c.capLeftPath m hne).pos ⊆
    Set.range (c.paths i).pos ∪ Set.range (m.pairPath hne).pos := by
  rintro s ⟨a, rfl⟩
  exact glue_pos_cases (c.paths i) (m.pairPath hne) (c.sites_pos i) m.pairSites_pos (c.capLeft_join m hne)
    (fun a b heq => c.capLeft_intersection m hne a b heq) a

theorem capRight_join (hne : i ≠ j) :
    (c.capLeftPath m hne).pos ⟨c.capLeftSites m - 1, by have h := c.capLeftSites_pos m; omega⟩ =
      (c.paths j).reverse.pos ⟨0, c.sites_pos j⟩ := by
  have hl := c.capLeft_last m hne ⟨c.capLeftSites m - 1, by have h := c.capLeftSites_pos m; omega⟩
    (by change c.capLeftSites m - 1 + 1 = c.capLeftSites m; have h := c.capLeftSites_pos m; omega)
  exact hl.trans (c.reverse_entry_first j).symm

theorem capRight_intersection (hne : i ≠ j) (a : Fin (c.capLeftSites m)) (b : Fin (c.sites j))
    (heq : (c.capLeftPath m hne).pos a = (c.paths j).reverse.pos b) :
    a.val + 1 = c.capLeftSites m ∧ b.val = 0 := by
  have ht : (c.capLeftPath m hne).pos a = d.armCaps j := by
    have hm := c.capLeft_range m hne ⟨a, rfl⟩
    rcases hm with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact False.elim (Set.disjoint_left.mp (c.disjoint i j hne) ⟨s, hs⟩ ⟨b.rev, heq.symm⟩)
    · rcases c.pair_intersection m hne j b.rev s (heq.symm.trans hs.symm) with h | h
      · exact False.elim (hne h.1.symm)
      · exact heq.trans h.2.2
  have hb := (c.paths j).reverse.injective_pos ((heq.symm.trans ht).trans (c.reverse_entry_first j).symm)
  have hbval : b.val = 0 := congrArg (fun k : Fin (c.sites j) => k.val) hb
  have hl := c.capLeft_last m hne ⟨c.capLeftSites m - 1, by have h := c.capLeftSites_pos m; omega⟩
    (by change c.capLeftSites m - 1 + 1 = c.capLeftSites m; have h := c.capLeftSites_pos m; omega)
  have ha := (c.capLeftPath m hne).injective_pos (ht.trans hl.symm)
  have hav := congrArg (fun k : Fin (c.capLeftSites m) => k.val) ha
  change a.val = c.capLeftSites m - 1 at hav
  have hp := c.capLeftSites_pos m
  exact ⟨by omega, hbval⟩

noncomputable def capPairSites : ℕ := c.capLeftSites m + c.sites j - 1

noncomputable def capPairPath (hne : i ≠ j) : Fold tetrahedralLattice (c.capPairSites m) :=
  glue (c.capLeftPath m hne) (c.paths j).reverse (c.capLeftSites_pos m) (c.sites_pos j) (c.capRight_join m hne)
    (fun a b heq => c.capRight_intersection m hne a b heq)

theorem capPairSites_pos : 0 < c.capPairSites m := by
  have hl := c.capLeftSites_pos m
  have hj := c.sites_pos j
  unfold capPairSites
  omega

theorem capPair_first (hne : i ≠ j) (a : Fin (c.capPairSites m)) (ha : a.val = 0) :
    (c.capPairPath m hne).pos a = c.caps i := by
  have h := glue_first (c.capLeftPath m hne) (c.paths j).reverse (c.capLeftSites_pos m) (c.sites_pos j)
    (c.capRight_join m hne) (fun a b heq => c.capRight_intersection m hne a b heq) a ha
  exact h.trans (c.capLeft_first m hne ⟨0, c.capLeftSites_pos m⟩ rfl)

theorem capPair_last (hne : i ≠ j) (a : Fin (c.capPairSites m)) (ha : a.val + 1 = c.capPairSites m) :
    (c.capPairPath m hne).pos a = c.caps j := by
  have h := glue_last (c.capLeftPath m hne) (c.paths j).reverse (c.capLeftSites_pos m) (c.sites_pos j)
    (c.capRight_join m hne) (fun a b heq => c.capRight_intersection m hne a b heq) a ha
  have hr := reverse_last (c.paths j) (c.sites_pos j)
    ⟨c.sites j - 1, by have hp := c.sites_pos j; omega⟩
    (by change c.sites j - 1 + 1 = c.sites j; have hp := c.sites_pos j; omega)
  exact h.trans (hr.trans (c.first j ⟨0, c.sites_pos j⟩ rfl))

theorem capPair_count : (c.capPairSites m : ℤ) = c.baseCapPairCount p i j + Δ := by
  have hi := c.sites_pos i
  have hj := c.sites_pos j
  have hm := m.pairSites_pos
  have hn := m.pairSites_count
  unfold capPairSites capLeftSites baseCapPairCount
  omega

theorem capPair_range (hne : i ≠ j) : Set.range (c.capPairPath m hne).pos ⊆
    (Set.range (c.paths i).pos ∪ Set.range (m.pairPath hne).pos) ∪ Set.range (c.paths j).pos := by
  rintro s ⟨a, rfl⟩
  have hm := glue_pos_cases (c.capLeftPath m hne) (c.paths j).reverse (c.capLeftSites_pos m) (c.sites_pos j)
    (c.capRight_join m hne) (fun a b heq => c.capRight_intersection m hne a b heq) a
  rcases hm with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact Or.inl (c.capLeft_range m hne ⟨b, hb⟩)
  · exact Or.inr ⟨b.rev, hb⟩

theorem disjoint_other_pair (hne : i ≠ j) (k : Fin w) (hki : k ≠ i) (hkj : k ≠ j) :
    Disjoint (Set.range (c.paths k).pos) (Set.range (m.pairPath hne).pos) := by
  apply Set.disjoint_left.mpr
  rintro s ⟨a, rfl⟩ ⟨b, heq⟩
  rcases c.pair_intersection m hne k a b heq.symm with h | h
  · exact hki h.1
  · exact hkj h.1

end Pair

end ProteinFolding.Tetrahedral.FarField.CapEntryData
