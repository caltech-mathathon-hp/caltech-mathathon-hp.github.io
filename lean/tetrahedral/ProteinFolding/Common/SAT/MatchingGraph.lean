import ProteinFolding.Common.SAT.MatchingEquivalences

/-! Canonical raw 3DM instances obtained by enumerating an explicit finite
ternary relation. This deliberately simple enumeration has at most n³ triples.
It provides the bridge from typed gadget vertices to the frozen raw matching
source interface without arbitrary choices of vertex labels. -/

namespace ProteinFolding.ThreeDimensionalMatching

def graphTriples (n : ℕ) (p : Fin n → Fin n → Fin n → Bool) : List Triple :=
  (List.finRange n).flatMap fun x =>
    (List.finRange n).flatMap fun y =>
      ((List.finRange n).filter (fun z => p x y z)).map (fun z => (x.val, y.val, z.val))

def graphInstance (n : ℕ) (p : Fin n → Fin n → Fin n → Bool) : Instance :=
  ⟨n, graphTriples n p⟩

theorem mem_graphTriples (n : ℕ) (p : Fin n → Fin n → Fin n → Bool)
    (x y z : Fin n) : (x.val, y.val, z.val) ∈ graphTriples n p ↔ p x y z = true := by
  constructor
  · intro h
    obtain ⟨u, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨v, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨w, hw, he⟩ := List.mem_map.mp h
    have hx : u = x := Fin.ext (congrArg Prod.fst he)
    have hy : v = y := Fin.ext (congrArg (fun t : Triple => t.2.1) he)
    have hz : w = z := Fin.ext (congrArg (fun t : Triple => t.2.2) he)
    subst u
    subst v
    subst w
    exact (List.mem_filter.mp hw).2
  · intro h
    apply List.mem_flatMap.mpr
    refine ⟨x, List.mem_finRange _, List.mem_flatMap.mpr ?_⟩
    refine ⟨y, List.mem_finRange _, List.mem_map.mpr ?_⟩
    exact ⟨z, List.mem_filter.mpr ⟨List.mem_finRange _, h⟩, rfl⟩

theorem graphInstance_wellFormed (n : ℕ) (p : Fin n → Fin n → Fin n → Bool) :
    WellFormed (graphInstance n p) := by
  intro t ht
  obtain ⟨x, _, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨y, _, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp ht
  exact ⟨x.isLt, y.isLt, z.isLt⟩

theorem graphInstance_accepts_iff (n : ℕ) (p : Fin n → Fin n → Fin n → Bool) :
    Accepts (graphInstance n p) ↔
      ∃ mx mz : Equiv.Perm (Fin n), ∀ y, p (mx y) y (mz y) = true := by
  rw [accepts_iff_equivMatching]
  simp only [graphInstance_wellFormed, true_and]
  simp only [EquivMatching, graphInstance, mem_graphTriples]

end ProteinFolding.ThreeDimensionalMatching
