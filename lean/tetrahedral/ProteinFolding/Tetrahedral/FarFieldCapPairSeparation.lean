import ProteinFolding.Tetrahedral.FarFieldCapPairPaths

namespace ProteinFolding.Tetrahedral.FarField.CapEntryData

variable {w : ℕ} {d : WireData w} (c : CapEntryData d)

theorem capPairPaths_disjoint {p : RoutingPlan d} {i j r s : Fin w} {Δ Δ' : ℕ}
    (m : MiddleData p i j Δ) (n : MiddleData p r s Δ')
    (hij : i ≠ j) (hrs : r ≠ s)
    (hir : i ≠ r) (his : i ≠ s) (hjr : j ≠ r) (hjs : j ≠ s)
    (hm : p.heights i = p.heights j) (hn : p.heights r = p.heights s)
    (hgap : p.heights i + 4 ≤ p.heights r ∨ p.heights r + 4 ≤ p.heights i) :
    Disjoint (Set.range (c.capPairPath m hij).pos) (Set.range (c.capPairPath n hrs).pos) := by
  have h_ir := c.disjoint i r hir
  have h_is := c.disjoint i s his
  have h_jr := c.disjoint j r hjr
  have h_js := c.disjoint j s hjs
  have h_in := c.disjoint_other_pair n hrs i hir his
  have h_jn := c.disjoint_other_pair n hrs j hjr hjs
  have h_mr := (c.disjoint_other_pair m hij r hir.symm hjr.symm).symm
  have h_ms := (c.disjoint_other_pair m hij s his.symm hjs.symm).symm
  have h_mn := m.pairPaths_disjoint n hij hrs hir his hjr hjs hm hn hgap
  have hUnion : Disjoint
      ((Set.range (c.paths i).pos ∪ Set.range (m.pairPath hij).pos) ∪ Set.range (c.paths j).pos)
      ((Set.range (c.paths r).pos ∪ Set.range (n.pairPath hrs).pos) ∪ Set.range (c.paths s).pos) := by
    simp only [Set.disjoint_union_left, Set.disjoint_union_right]
    tauto
  exact hUnion.mono (c.capPair_range m hij) (c.capPair_range n hrs)

end ProteinFolding.Tetrahedral.FarField.CapEntryData
