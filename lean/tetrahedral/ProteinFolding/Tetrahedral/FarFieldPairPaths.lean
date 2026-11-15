import ProteinFolding.Tetrahedral.FarFieldMiddleSupport
import ProteinFolding.Tetrahedral.FarFieldParity

namespace ProteinFolding.Tetrahedral.FarField

namespace RoutingPlan

noncomputable def basePairCount {w : ℕ} {d : WireData w} (p : RoutingPlan d) (i j : Fin w) : ℤ :=
  (p.wireSites i : ℤ) + p.wireSites j + X (p.approaches j).target - X (p.approaches i).target - 1

end RoutingPlan

namespace MiddleData

variable {w : ℕ} {d : WireData w} {p : RoutingPlan d} {i j : Fin w} {Δ : ℕ} (m : MiddleData p i j Δ)

noncomputable def leftSites : ℕ := p.wireSites i + m.sites - 1

theorem left_join :
    (p.wirePath i).pos ⟨p.wireSites i - 1, by have h := p.wireSites_pos i; omega⟩ =
      m.path.pos ⟨0, m.sites_pos⟩ := by
  have hw := p.wirePath_last i ⟨p.wireSites i - 1, by have h := p.wireSites_pos i; omega⟩
    (by change p.wireSites i - 1 + 1 = p.wireSites i; have h := p.wireSites_pos i; omega)
  exact hw.trans (m.first ⟨0, m.sites_pos⟩ rfl).symm

theorem left_intersection (a : Fin (p.wireSites i)) (b : Fin m.sites)
    (heq : (p.wirePath i).pos a = m.path.pos b) : a.val + 1 = p.wireSites i ∧ b.val = 0 := by
  have ht := m.wire_intersection i b a heq.symm
  have hw := p.wirePath_last i ⟨p.wireSites i - 1, by have h := p.wireSites_pos i; omega⟩
    (by change p.wireSites i - 1 + 1 = p.wireSites i; have h := p.wireSites_pos i; omega)
  have ha := (p.wirePath i).injective_pos ((heq.trans ht).trans hw.symm)
  have hav := congrArg (fun k : Fin (p.wireSites i) => k.val) ha
  change a.val = p.wireSites i - 1 at hav
  have hb := m.path.injective_pos (ht.trans (m.first ⟨0, m.sites_pos⟩ rfl).symm)
  have hbval : b.val = 0 := congrArg (fun k : Fin m.sites => k.val) hb
  have hpos := p.wireSites_pos i
  exact ⟨by omega, hbval⟩

noncomputable def leftPath : Fold tetrahedralLattice m.leftSites :=
  glue (p.wirePath i) m.path (p.wireSites_pos i) m.sites_pos m.left_join
    (fun a b heq => m.left_intersection a b heq)

theorem leftSites_pos : 0 < m.leftSites := by
  have hw := p.wireSites_pos i
  have hm := m.sites_pos
  unfold leftSites
  omega

theorem leftPath_first (a : Fin m.leftSites) (ha : a.val = 0) :
    m.leftPath.pos a = quadrantMap d.R d.R_even (d.quadrants i) (d.bases i) := by
  have h := glue_first (p.wirePath i) m.path (p.wireSites_pos i) m.sites_pos m.left_join
    (fun a b heq => m.left_intersection a b heq) a ha
  exact h.trans (p.wirePath_first i ⟨0, p.wireSites_pos i⟩ rfl)

theorem leftPath_last (a : Fin m.leftSites) (ha : a.val + 1 = m.leftSites) :
    m.leftPath.pos a = (p.approaches j).target := by
  have h := glue_last (p.wirePath i) m.path (p.wireSites_pos i) m.sites_pos m.left_join
    (fun a b heq => m.left_intersection a b heq) a ha
  exact h.trans (m.last _ (by change m.sites - 1 + 1 = m.sites; have hm := m.sites_pos; omega))

theorem leftPath_range : Set.range m.leftPath.pos ⊆ Set.range (p.wirePath i).pos ∪ Set.range m.path.pos := by
  rintro s ⟨a, rfl⟩
  exact glue_pos_cases (p.wirePath i) m.path (p.wireSites_pos i) m.sites_pos m.left_join
    (fun a b heq => m.left_intersection a b heq) a

theorem reverse_wire_first : (p.wirePath j).reverse.pos ⟨0, p.wireSites_pos j⟩ = (p.approaches j).target := by
  have hr := reverse_first (p.wirePath j) (p.wireSites_pos j) ⟨0, p.wireSites_pos j⟩ rfl
  have hw := p.wirePath_last j ⟨p.wireSites j - 1, by have h := p.wireSites_pos j; omega⟩
    (by change p.wireSites j - 1 + 1 = p.wireSites j; have h := p.wireSites_pos j; omega)
  exact hr.trans hw

theorem right_join :
    m.leftPath.pos ⟨m.leftSites - 1, by have h := m.leftSites_pos; omega⟩ =
      (p.wirePath j).reverse.pos ⟨0, p.wireSites_pos j⟩ := by
  have hl := m.leftPath_last ⟨m.leftSites - 1, by have h := m.leftSites_pos; omega⟩
    (by change m.leftSites - 1 + 1 = m.leftSites; have h := m.leftSites_pos; omega)
  exact hl.trans (reverse_wire_first (p := p) (j := j)).symm

theorem right_intersection (hne : i ≠ j) (a : Fin m.leftSites) (b : Fin (p.wireSites j))
    (heq : m.leftPath.pos a = (p.wirePath j).reverse.pos b) : a.val + 1 = m.leftSites ∧ b.val = 0 := by
  have ht : m.leftPath.pos a = (p.approaches j).target := by
    have hm := m.leftPath_range ⟨a, rfl⟩
    rcases hm with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hd := p.wirePaths_disjoint i j hne
      exact False.elim (Set.disjoint_left.mp hd ⟨c, hc⟩ ⟨b.rev, heq.symm⟩)
    · have hmid := m.wire_intersection j c b.rev (hc.trans heq)
      exact hc.symm.trans hmid
  have hb := (p.wirePath j).reverse.injective_pos
    ((heq.symm.trans ht).trans (reverse_wire_first (p := p) (j := j)).symm)
  have hbval : b.val = 0 := congrArg (fun k : Fin (p.wireSites j) => k.val) hb
  have hl := m.leftPath_last ⟨m.leftSites - 1, by have h := m.leftSites_pos; omega⟩
    (by change m.leftSites - 1 + 1 = m.leftSites; have h := m.leftSites_pos; omega)
  have ha := m.leftPath.injective_pos (ht.trans hl.symm)
  have hav := congrArg (fun k : Fin m.leftSites => k.val) ha
  change a.val = m.leftSites - 1 at hav
  have hpos := m.leftSites_pos
  exact ⟨by omega, hbval⟩

noncomputable def pairSites : ℕ := m.leftSites + p.wireSites j - 1

noncomputable def pairPath (hne : i ≠ j) : Fold tetrahedralLattice m.pairSites :=
  glue m.leftPath (p.wirePath j).reverse m.leftSites_pos (p.wireSites_pos j) m.right_join
    (fun a b heq => m.right_intersection hne a b heq)

theorem pairSites_pos : 0 < m.pairSites := by
  have hl := m.leftSites_pos
  have hw := p.wireSites_pos j
  unfold pairSites
  omega

theorem pairPath_first (hne : i ≠ j) (a : Fin m.pairSites) (ha : a.val = 0) :
    (m.pairPath hne).pos a = quadrantMap d.R d.R_even (d.quadrants i) (d.bases i) := by
  have h := glue_first m.leftPath (p.wirePath j).reverse m.leftSites_pos (p.wireSites_pos j) m.right_join
    (fun a b heq => m.right_intersection hne a b heq) a ha
  exact h.trans (m.leftPath_first ⟨0, m.leftSites_pos⟩ rfl)

theorem pairPath_last (hne : i ≠ j) (a : Fin m.pairSites) (ha : a.val + 1 = m.pairSites) :
    (m.pairPath hne).pos a = quadrantMap d.R d.R_even (d.quadrants j) (d.bases j) := by
  have h := glue_last m.leftPath (p.wirePath j).reverse m.leftSites_pos (p.wireSites_pos j) m.right_join
    (fun a b heq => m.right_intersection hne a b heq) a ha
  have hr := reverse_last (p.wirePath j) (p.wireSites_pos j)
    ⟨p.wireSites j - 1, by have h := p.wireSites_pos j; omega⟩
    (by change p.wireSites j - 1 + 1 = p.wireSites j; have h := p.wireSites_pos j; omega)
  exact h.trans (hr.trans (p.wirePath_first j ⟨0, p.wireSites_pos j⟩ rfl))

theorem pairSites_count : (m.pairSites : ℤ) = p.basePairCount i j + Δ := by
  have hi := p.wireSites_pos i
  have hj := p.wireSites_pos j
  have hm := m.sites_pos
  have hn := m.count
  unfold pairSites leftSites RoutingPlan.basePairCount
  omega

theorem pairPath_range (hne : i ≠ j) : Set.range (m.pairPath hne).pos ⊆
    (Set.range (p.wirePath i).pos ∪ Set.range m.path.pos) ∪ Set.range (p.wirePath j).pos := by
  rintro s ⟨a, rfl⟩
  have hm := glue_pos_cases m.leftPath (p.wirePath j).reverse m.leftSites_pos (p.wireSites_pos j) m.right_join
    (fun a b heq => m.right_intersection hne a b heq) a
  rcases hm with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact Or.inl (m.leftPath_range ⟨b, hb⟩)
  · exact Or.inr ⟨b.rev, hb⟩

end MiddleData

end ProteinFolding.Tetrahedral.FarField
