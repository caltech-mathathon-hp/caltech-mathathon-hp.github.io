import ProteinFolding.Tetrahedral.OctahedralBoundary
import ProteinFolding.Tetrahedral.FiniteSets

/-!
# The six vertices and outside degrees, Section 5.6(O1)

The six sites are distinct and have two dangling directions when m≥2.
The m=1 singleton is deliberately excluded from those two conclusions.
-/

namespace ProteinFolding.Tetrahedral

def octVertexCoordinates (m : ℕ) (a : Fin 3) (positive : Bool) (k : Fin 3) : ℤ :=
  octCentre m k + if k = a then (if positive then octRadius m else -octRadius m) else 0

theorem octVertexCoordinates_inA (m : ℕ) (a : Fin 3) (positive : Bool) :
    InASublattice (octVertexCoordinates m a positive) := by
  constructor
  · intro k
    fin_cases a <;> cases positive <;> fin_cases k <;>
      dsimp [octVertexCoordinates, octCentre, octRadius] <;> omega
  · fin_cases a <;> cases positive <;>
      dsimp [coordinateSum, octVertexCoordinates, octCentre, octRadius] <;> omega

def octVertexSite (m : ℕ) (a : Fin 3) (positive : Bool) : Site :=
  ⟨octVertexCoordinates m a positive, Or.inl (octVertexCoordinates_inA m a positive)⟩

def octVertices (m : ℕ) : Finset Site :=
  Finset.univ.image (fun ap : Fin 3 × Bool => octVertexSite m ap.1 ap.2)

def OctVertexCoordinateCases (m : ℕ) (p : Coordinates) : Prop :=
  (p 0 = octRadius m ∧ p 1 = octRadius m ∧ p 2 = 0) ∨
  (p 0 = -octRadius m ∧ p 1 = octRadius m ∧ p 2 = 0) ∨
  (p 0 = 0 ∧ p 1 = 2 * octRadius m ∧ p 2 = 0) ∨
  (p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0) ∨
  (p 0 = 0 ∧ p 1 = octRadius m ∧ p 2 = octRadius m) ∨
  (p 0 = 0 ∧ p 1 = octRadius m ∧ p 2 = -octRadius m)

theorem mem_octVertices_iff (m : ℕ) (p : Site) :
    p ∈ octVertices m ↔ OctVertexCoordinateCases m p.val := by
  constructor
  · intro hp
    obtain ⟨⟨a, positive⟩, _, rfl⟩ := Finset.mem_image.mp hp
    fin_cases a <;> cases positive <;>
      dsimp [OctVertexCoordinateCases, octVertexSite, octVertexCoordinates, octCentre] <;> omega
  · intro h
    have hmem : ∀ a positive, p.val = octVertexCoordinates m a positive → p ∈ octVertices m := by
      intro a positive heq
      exact Finset.mem_image.mpr ⟨(a, positive), Finset.mem_univ _,
        Subtype.ext heq.symm⟩
    rcases h with h | h | h | h | h | h
    · apply hmem 0 true
      funext k
      fin_cases k <;> dsimp [octVertexCoordinates, octCentre] <;> omega
    · apply hmem 0 false
      funext k
      fin_cases k <;> dsimp [octVertexCoordinates, octCentre] <;> omega
    · apply hmem 1 true
      funext k
      fin_cases k <;> dsimp [octVertexCoordinates, octCentre] <;> omega
    · apply hmem 1 false
      funext k
      fin_cases k <;> dsimp [octVertexCoordinates, octCentre] <;> omega
    · apply hmem 2 true
      funext k
      fin_cases k <;> dsimp [octVertexCoordinates, octCentre] <;> omega
    · apply hmem 2 false
      funext k
      fin_cases k <;> dsimp [octVertexCoordinates, octCentre] <;> omega

theorem octVertexSite_mem_octahedron {m : ℕ} (hm : 1 ≤ m) (a : Fin 3) (positive : Bool) :
    octVertexSite m a positive ∈ octahedron m := by
  rw [mem_octahedron, inOctahedron_iff_A m (octVertexCoordinates_inA m a positive)]
  intro i
  fin_cases a <;> cases positive <;> fin_cases i <;>
    dsimp [tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre, octRadius]
  all_goals constructor <;> omega

theorem octVertices_subset_octahedron {m : ℕ} (hm : 1 ≤ m) : octVertices m ⊆ octahedron m := by
  intro p hp
  obtain ⟨⟨a, positive⟩, _, rfl⟩ := Finset.mem_image.mp hp
  exact octVertexSite_mem_octahedron hm a positive

theorem octVertices_inA {m : ℕ} {p : Site} (hp : p ∈ octVertices m) : InASublattice p.val := by
  obtain ⟨⟨a, positive⟩, _, rfl⟩ := Finset.mem_image.mp hp
  exact octVertexCoordinates_inA m a positive

theorem octVertexSite_injective {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective (fun ap : Fin 3 × Bool => octVertexSite m ap.1 ap.2) := by
  intro ap bp heq
  obtain ⟨a, positive⟩ := ap
  obtain ⟨b, positive'⟩ := bp
  have h0 := congrArg (fun p : Site => p.val 0) heq
  have h1 := congrArg (fun p : Site => p.val 1) heq
  have h2 := congrArg (fun p : Site => p.val 2) heq
  have hR : 0 < octRadius m := by dsimp [octRadius]; omega
  fin_cases a <;> cases positive <;> fin_cases b <;> cases positive' <;>
    dsimp [octVertexSite, octVertexCoordinates, octCentre] at h0 h1 h2
  all_goals first | rfl | omega

theorem octVertices_card {m : ℕ} (hm : 2 ≤ m) : (octVertices m).card = 6 := by
  unfold octVertices
  rw [Finset.card_image_of_injective _ (octVertexSite_injective hm)]
  decide

def octDanglingDirections (m : ℕ) (p : Site) : Finset (Fin 4) :=
  Finset.univ.filter (fun d => step p d ∉ octahedron m)

theorem octDanglingDirections_A (m : ℕ) {p : Site} (hpA : InASublattice p.val)
    (hp : p ∈ octahedron m) : octDanglingDirections m p =
      Finset.univ.filter (fun d => tetraCoordinate m p.val d = octRadius m) := by
  ext d
  simp only [octDanglingDirections, Finset.mem_filter, Finset.mem_univ, true_and]
  exact step_not_mem_octahedron_A m hpA hp d

theorem octDanglingDirections_B (m : ℕ) {p : Site} (hpB : InBSublattice p.val)
    (hp : p ∈ octahedron m) : octDanglingDirections m p =
      Finset.univ.filter (fun d => tetraCoordinate m p.val d = -(2 * (m : ℤ) - 1)) := by
  ext d
  simp only [octDanglingDirections, Finset.mem_filter, Finset.mem_univ, true_and]
  exact step_not_mem_octahedron_B m hpB hp d

theorem octDanglingDirections_card_eq_external (m : ℕ) (p : Site) :
    (octDanglingDirections m p).card = (externalNeighbours (octahedron m) p).card := by
  unfold externalNeighbours neighbours
  rw [Finset.filter_image, Finset.card_image_of_injective _ (step_injective p)]
  rfl

theorem B_small_face_unique (m : ℕ) {p : Site} (hpB : InBSublattice p.val)
    (hp : p ∈ octahedron m) {i j : Fin 4}
    (hi : tetraCoordinate m p.val i = -(2 * (m : ℤ) - 1))
    (hj : tetraCoordinate m p.val j = -(2 * (m : ℤ) - 1)) : i = j := by
  have h := (inOctahedron_iff_B m hpB).mp ((mem_octahedron m p).mp hp)
  have h0 := (h 0).2
  have h1 := (h 1).2
  have h2 := (h 2).2
  have h3 := (h 3).2
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (dsimp [tetraCoordinate, octRadius] at hi hj h0 h1 h2 h3; omega)

theorem octDanglingDirections_B_le_one (m : ℕ) {p : Site} (hpB : InBSublattice p.val)
    (hp : p ∈ octahedron m) : (octDanglingDirections m p).card ≤ 1 := by
  rw [octDanglingDirections_B m hpB hp]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact B_small_face_unique m hpB hp (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem two_big_faces_mem_octVertices (m : ℕ) {p : Site} (hpA : InASublattice p.val)
    (hp : p ∈ octahedron m) {i j : Fin 4} (hne : i ≠ j)
    (hi : tetraCoordinate m p.val i = octRadius m)
    (hj : tetraCoordinate m p.val j = octRadius m) : p ∈ octVertices m := by
  apply (mem_octVertices_iff m p).mpr
  have h := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m p).mp hp)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  dsimp [tetraCoordinate] at h0 h1 h2 h3
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hne rfl).elim
    | (dsimp [tetraCoordinate] at hi hj; dsimp [OctVertexCoordinateCases]; omega)

theorem two_dangling_implies_vertex (m : ℕ) {p : Site} (hp : p ∈ octahedron m)
    (hcard : 1 < (octDanglingDirections m p).card) : p ∈ octVertices m := by
  rcases p.property with hpA | hpB
  · rw [octDanglingDirections_A m hpA hp] at hcard
    obtain ⟨i, hi, j, hj, hne⟩ := Finset.one_lt_card.mp hcard
    exact two_big_faces_mem_octVertices m hpA hp hne
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  · have h := octDanglingDirections_B_le_one m hpB hp
    omega

theorem nonvertex_dangling_le_one (m : ℕ) {p : Site} (hp : p ∈ octahedron m)
    (hn : p ∉ octVertices m) : (octDanglingDirections m p).card ≤ 1 := by
  by_contra h
  exact hn (two_dangling_implies_vertex m hp (by omega))

theorem octVertex_face_iff {m : ℕ} (hm : 2 ≤ m) (a : Fin 3) (positive : Bool) (d : Fin 4) :
    tetraCoordinate m (octVertexSite m a positive).val d = octRadius m ↔
      (if positive then bondComponent d a = 1 else bondComponent d a = -1) := by
  have hR : 0 < octRadius m := by dsimp [octRadius]; omega
  fin_cases a <;> cases positive <;> fin_cases d <;>
    dsimp [tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre, bondComponent] <;> omega

theorem vertex_direction_count (a : Fin 3) (positive : Bool) :
    (Finset.univ.filter (fun d : Fin 4 =>
      if positive then bondComponent d a = 1 else bondComponent d a = -1)).card = 2 := by
  revert a positive
  decide

theorem octVertex_two_dangling {m : ℕ} (hm : 2 ≤ m) (a : Fin 3) (positive : Bool) :
    (octDanglingDirections m (octVertexSite m a positive)).card = 2 := by
  rw [octDanglingDirections_A m (octVertexCoordinates_inA m a positive)
    (octVertexSite_mem_octahedron (by omega) a positive)]
  have heq : Finset.univ.filter (fun d : Fin 4 =>
      tetraCoordinate m (octVertexSite m a positive).val d = octRadius m) =
    Finset.univ.filter (fun d : Fin 4 =>
      if positive then bondComponent d a = 1 else bondComponent d a = -1) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact octVertex_face_iff hm a positive d
  rw [heq, vertex_direction_count]

/-- Exactly the six vertices have two dangling directions, for m≥2. -/
theorem two_dangling_iff_vertex {m : ℕ} (hm : 2 ≤ m) {p : Site} (hp : p ∈ octahedron m) :
    (octDanglingDirections m p).card = 2 ↔ p ∈ octVertices m := by
  constructor
  · intro hc
    exact two_dangling_implies_vertex m hp (by omega)
  · intro hpv
    obtain ⟨⟨a, positive⟩, _, rfl⟩ := Finset.mem_image.mp hpv
    exact octVertex_two_dangling hm a positive

theorem octahedron_dangling_le_two {m : ℕ} (hm : 2 ≤ m) {p : Site} (hp : p ∈ octahedron m) :
    (octDanglingDirections m p).card ≤ 2 := by
  by_cases hv : p ∈ octVertices m
  · rw [(two_dangling_iff_vertex hm hp).mpr hv]
  · have h := nonvertex_dangling_le_one m hp hv
    omega

theorem nonvertex_surface_one_dangling (m : ℕ) {p : Site} (hp : p ∈ octahedron m)
    (hn : p ∉ octVertices m) (hs : 0 < (octDanglingDirections m p).card) :
    (octDanglingDirections m p).card = 1 := by
  have h := nonvertex_dangling_le_one m hp hn
  omega

end ProteinFolding.Tetrahedral
