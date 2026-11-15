import ProteinFolding.Tetrahedral.FarFieldWireApproaches

namespace ProteinFolding.Tetrahedral.FarField.RoutingPlan

variable {w : ℕ} {d : WireData w} (p : RoutingPlan d)

theorem wire_join (i : Fin w) :
    (d.prefixPath i (p.heights i) (p.heights_odd i) (p.own_height i)).pos
      ⟨d.prefixSites i (p.heights i) - 1, by have h := d.prefixSites_pos i (p.heights i); omega⟩ =
      (p.approaches i).path.pos ⟨0, (p.approaches i).sites_pos⟩ := by
  have hp := d.prefixPath_last i (p.heights i) (p.heights_odd i) (p.own_height i)
    ⟨d.prefixSites i (p.heights i) - 1, by have h := d.prefixSites_pos i (p.heights i); omega⟩
    (by change d.prefixSites i (p.heights i) - 1 + 1 = d.prefixSites i (p.heights i)
        have h := d.prefixSites_pos i (p.heights i); omega)
  have ha := (p.approaches i).first ⟨0, (p.approaches i).sites_pos⟩ rfl
  exact hp.trans ha.symm

theorem wire_intersection (i : Fin w)
    (a : Fin (d.prefixSites i (p.heights i))) (b : Fin (p.approaches i).sites)
    (heq : (d.prefixPath i (p.heights i) (p.heights_odd i) (p.own_height i)).pos a = (p.approaches i).path.pos b) :
    a.val + 1 = d.prefixSites i (p.heights i) ∧ b.val = 0 := by
  have hpoint : (d.prefixPath i (p.heights i) (p.heights_odd i) (p.own_height i)).pos a = p.radialTops i := by
    have hm := d.prefixPath_range i (p.heights i) (p.heights_odd i) (p.own_height i) ⟨a, rfl⟩
    rcases hm with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hd := p.approach_columnAvenue_disjoint i i
      exact False.elim (Set.disjoint_left.mp hd ⟨b, rfl⟩ ⟨c, hc.trans heq⟩)
    · have hE := d.entries_profile i
      have hp := radialPosition_profile d.R d.R_even (d.quadrants i) (d.entries i).point c.val hE.1 (by omega)
      have hh := radialHeight_exact d.R d.R_even (d.quadrants i) (d.entries i).point hE.1
        (p.heights i) (p.heights_odd i) (by have h := p.own_height i; omega)
      have ha := (p.approaches i).level b
      have hρ := congrArg (rho d.R) (hc.trans heq)
      change rho d.R (radialPosition d.R d.R_even (d.quadrants i) (d.entries i).point (0 + c.val)) =
        rho d.R ((p.approaches i).path.pos b) at hρ
      simp only [zero_add] at hρ
      have hcval : c.val = radialHeight d.R (p.heights i) (d.entries i).point := by omega
      have hcLast := radialFold_last d.R d.R_even (d.quadrants i) (d.entries i).point (p.heights i) c hcval
      exact hc.symm.trans hcLast
  have hfirst := (p.approaches i).first ⟨0, (p.approaches i).sites_pos⟩ rfl
  have hb := (p.approaches i).path.injective_pos ((heq.symm.trans hpoint).trans hfirst.symm)
  have hbval : b.val = 0 := congrArg (fun k : Fin (p.approaches i).sites => k.val) hb
  have hlast := d.prefixPath_last i (p.heights i) (p.heights_odd i) (p.own_height i)
    ⟨d.prefixSites i (p.heights i) - 1, by have h := d.prefixSites_pos i (p.heights i); omega⟩
    (by change d.prefixSites i (p.heights i) - 1 + 1 = d.prefixSites i (p.heights i)
        have h := d.prefixSites_pos i (p.heights i); omega)
  have ha := (d.prefixPath i (p.heights i) (p.heights_odd i) (p.own_height i)).injective_pos (hpoint.trans hlast.symm)
  have hav := congrArg (fun k : Fin (d.prefixSites i (p.heights i)) => k.val) ha
  change a.val = d.prefixSites i (p.heights i) - 1 at hav
  have hpos := d.prefixSites_pos i (p.heights i)
  exact ⟨by omega, hbval⟩

noncomputable def wireSites (i : Fin w) : ℕ := d.prefixSites i (p.heights i) + (p.approaches i).sites - 1

noncomputable def wirePath (i : Fin w) : Fold tetrahedralLattice (p.wireSites i) :=
  glue (d.prefixPath i (p.heights i) (p.heights_odd i) (p.own_height i)) (p.approaches i).path
    (d.prefixSites_pos i (p.heights i)) (p.approaches i).sites_pos (p.wire_join i)
    (fun a b heq => p.wire_intersection i a b heq)

theorem wireSites_pos (i : Fin w) : 0 < p.wireSites i := by
  have hp := d.prefixSites_pos i (p.heights i)
  have ha := (p.approaches i).sites_pos
  unfold wireSites
  omega

theorem wirePath_first (i : Fin w) (k : Fin (p.wireSites i)) (hk : k.val = 0) :
    (p.wirePath i).pos k = quadrantMap d.R d.R_even (d.quadrants i) (d.bases i) := by
  have h := glue_first (d.prefixPath i (p.heights i) (p.heights_odd i) (p.own_height i)) (p.approaches i).path
    (d.prefixSites_pos i (p.heights i)) (p.approaches i).sites_pos (p.wire_join i)
    (fun a b heq => p.wire_intersection i a b heq) k hk
  exact h.trans (d.prefixPath_first i _ _ _ ⟨0, d.prefixSites_pos i (p.heights i)⟩ rfl)

theorem wirePath_last (i : Fin w) (k : Fin (p.wireSites i)) (hk : k.val + 1 = p.wireSites i) :
    (p.wirePath i).pos k = (p.approaches i).target := by
  have h := glue_last (d.prefixPath i (p.heights i) (p.heights_odd i) (p.own_height i)) (p.approaches i).path
    (d.prefixSites_pos i (p.heights i)) (p.approaches i).sites_pos (p.wire_join i)
    (fun a b heq => p.wire_intersection i a b heq) k hk
  exact h.trans ((p.approaches i).last _
    (by change (p.approaches i).sites - 1 + 1 = (p.approaches i).sites
        have h := (p.approaches i).sites_pos; omega))

theorem wirePath_range (i : Fin w) : Set.range (p.wirePath i).pos ⊆
    Set.range (d.prefixPath i (p.heights i) (p.heights_odd i) (p.own_height i)).pos ∪
      Set.range (p.approaches i).path.pos := by
  rintro s ⟨k, rfl⟩
  exact glue_pos_cases (d.prefixPath i (p.heights i) (p.heights_odd i) (p.own_height i)) (p.approaches i).path
    (d.prefixSites_pos i (p.heights i)) (p.approaches i).sites_pos (p.wire_join i)
    (fun a b heq => p.wire_intersection i a b heq) k

theorem wirePaths_disjoint (i j : Fin w) (hne : i ≠ j) :
    Disjoint (Set.range (p.wirePath i).pos) (Set.range (p.wirePath j).pos) := by
  have hpp := d.prefixPaths_disjoint i j hne (p.heights i) (p.heights j)
    (p.heights_odd i) (p.heights_odd j) (p.own_height i) (p.own_height j)
  have hpa := (p.approach_prefix_disjoint j i hne.symm).symm
  have hap := p.approach_prefix_disjoint i j hne
  have haa := p.approaches_pairwise i j hne
  have hUnion : Disjoint
      (Set.range (d.prefixPath i (p.heights i) (p.heights_odd i) (p.own_height i)).pos ∪ Set.range (p.approaches i).path.pos)
      (Set.range (d.prefixPath j (p.heights j) (p.heights_odd j) (p.own_height j)).pos ∪ Set.range (p.approaches j).path.pos) := by
    rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    exact ⟨⟨hpp, hpa⟩, ⟨hap, haa⟩⟩
  exact hUnion.mono (p.wirePath_range i) (p.wirePath_range j)

end ProteinFolding.Tetrahedral.FarField.RoutingPlan
