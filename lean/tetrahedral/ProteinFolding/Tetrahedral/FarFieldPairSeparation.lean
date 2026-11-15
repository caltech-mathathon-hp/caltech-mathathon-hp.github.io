import ProteinFolding.Tetrahedral.FarFieldPairPaths

namespace ProteinFolding.Tetrahedral.FarField.MiddleData

variable {w : ℕ} {d : WireData w} {p : RoutingPlan d} {i j : Fin w} {Δ : ℕ} (m : MiddleData p i j Δ)

theorem pairPaths_disjoint {r s : Fin w} {Δ' : ℕ} (n : MiddleData p r s Δ')
    (hij : i ≠ j) (hrs : r ≠ s)
    (hir : i ≠ r) (his : i ≠ s) (hjr : j ≠ r) (hjs : j ≠ s)
    (hm : p.heights i = p.heights j) (hn : p.heights r = p.heights s)
    (hgap : p.heights i + 4 ≤ p.heights r ∨ p.heights r + 4 ≤ p.heights i) :
    Disjoint (Set.range (m.pairPath hij).pos) (Set.range (n.pairPath hrs).pos) := by
  have h_ir := p.wirePaths_disjoint i r hir
  have h_is := p.wirePaths_disjoint i s his
  have h_jr := p.wirePaths_disjoint j r hjr
  have h_js := p.wirePaths_disjoint j s hjs
  have h_mr := m.avoids_wire_of_level_gap r hgap
  have h_ms := m.avoids_wire_of_level_gap s (by rw [← hn]; exact hgap)
  have h_in := (n.avoids_wire_of_level_gap i (by omega)).symm
  have h_jn := (n.avoids_wire_of_level_gap j (by rw [← hm]; omega)).symm
  have h_mn := m.disjoint_other_middle n hgap
  have hUnion : Disjoint
      ((Set.range (p.wirePath i).pos ∪ Set.range m.path.pos) ∪ Set.range (p.wirePath j).pos)
      ((Set.range (p.wirePath r).pos ∪ Set.range n.path.pos) ∪ Set.range (p.wirePath s).pos) := by
    simp only [Set.disjoint_union_left, Set.disjoint_union_right]
    tauto
  exact hUnion.mono (m.pairPath_range hij) (n.pairPath_range hrs)

end ProteinFolding.Tetrahedral.FarField.MiddleData
