import ProteinFolding.Tetrahedral.FarFieldCanonicalCaps
import ProteinFolding.Tetrahedral.FarFieldOrderedRoutes

namespace ProteinFolding.Tetrahedral.FarField

/-- The simultaneous linker theorem directly for actual distinct dangling
columns of the octahedron, with every scalar and arm-identity input derived. -/
theorem canonical_cap_routes_avoiding {m w k : ℕ} (C : Fin w → DanglingColumn m)
    (hseed : Function.Injective (fun i => (C i).seed)) (e : Pairing w k)
    (O : Set Site) (hlow : ∀ s ∈ O, rho (octRadius m) s < 20 * (m : ℤ) + 21)
    (hclear : ∀ i n, (C i).point n ∈ O → n = 0)
    (L : Fin k → ℕ) (hL : ∀ r, uniformLinkerLength m w ≤ L r)
    (hparity : ∀ r, CapParity (C (e.first r)).seed (C (e.second r)).seed (L r)) :
    ∃ f : ∀ r : Fin k, Fold tetrahedralLattice (L r),
      (∀ r a, a.val = 0 → (f r).pos a = (C (e.first r)).seed) ∧
      (∀ r a, a.val + 1 = L r → (f r).pos a = (C (e.second r)).seed) ∧
      (∀ r s, r ≠ s → Disjoint (Set.range (f r).pos) (Set.range (f s).pos)) ∧
      (∀ r s, s ∈ Set.range (f r).pos → s ∈ O → s = (C (e.first r)).seed ∨ s = (C (e.second r)).seed) := by
  exact paired_cap_routes_ordered (columnsWireData C hseed) (columnsCapEntryData C hseed) e O
    (columnsLocalObstacleData C hseed O hlow hclear) m rfl
    (columnsWireData.x_lower C hseed) L hL hparity

theorem canonical_cap_routes_outside_oct {m w k : ℕ} (C : Fin w → DanglingColumn m)
    (hseed : Function.Injective (fun i => (C i).seed)) (e : Pairing w k)
    (L : Fin k → ℕ) (hL : ∀ r, uniformLinkerLength m w ≤ L r)
    (hparity : ∀ r, CapParity (C (e.first r)).seed (C (e.second r)).seed (L r)) :
    ∃ f : ∀ r : Fin k, Fold tetrahedralLattice (L r),
      (∀ r a, a.val = 0 → (f r).pos a = (C (e.first r)).seed) ∧
      (∀ r a, a.val + 1 = L r → (f r).pos a = (C (e.second r)).seed) ∧
      (∀ r s, r ≠ s → Disjoint (Set.range (f r).pos) (Set.range (f s).pos)) ∧
      (∀ r a, (f r).pos a ∉ octahedron m) := by
  have hlow : ∀ s ∈ (octahedron m : Set Site), rho (octRadius m) s < 20 * (m : ℤ) + 21 := by
    intro s hs
    have hm : s ∈ skinSolid m 0 := by simpa only [skinSolid_zero] using hs
    have h := skinSolid_rho_bound m 0 hm
    change rho (octRadius m) s ≤ 2 * ((m + 2 * 0 : ℕ) : ℤ) at h
    push_cast at h
    omega
  have hclear : ∀ i n, (C i).point n ∈ (octahedron m : Set Site) → n = 0 := by
    intro i n hn
    exact False.elim ((C i).point_outside n hn)
  obtain ⟨f, hf, hl, hd, ho⟩ := canonical_cap_routes_avoiding C hseed e (octahedron m : Set Site)
    hlow hclear L hL hparity
  refine ⟨f, hf, hl, hd, ?_⟩
  intro r a ha
  rcases ho r ((f r).pos a) ⟨a, rfl⟩ ha with he | he
  · exact (C (e.first r)).seed_outside (by rwa [he] at ha)
  · exact (C (e.second r)).seed_outside (by rwa [he] at ha)

end ProteinFolding.Tetrahedral.FarField
