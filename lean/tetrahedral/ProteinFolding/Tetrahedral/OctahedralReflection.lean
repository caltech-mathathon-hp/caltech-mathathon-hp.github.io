import ProteinFolding.Tetrahedral.Octahedron
import ProteinFolding.Tetrahedral.OctahedralBoundary
import ProteinFolding.Tetrahedral.GapRuns

/-! The x/z reflection used to identify positive and negative octahedral layers. -/

namespace ProteinFolding.Tetrahedral

def octMirrorCoordinates (p : Coordinates) (k : Fin 3) : ℤ :=
  if k = 1 then p k else -p k

theorem octMirrorCoordinates_inA {p : Coordinates} (hp : InASublattice p) :
    InASublattice (octMirrorCoordinates p) := by
  have h0 := hp.1 0
  have h1 := hp.1 1
  have h2 := hp.1 2
  have hs := hp.2
  constructor
  · intro k
    fin_cases k <;> dsimp [octMirrorCoordinates] <;> omega
  · dsimp [coordinateSum, octMirrorCoordinates] at *
    omega

theorem octMirrorCoordinates_inB {p : Coordinates} (hp : InBSublattice p) :
    InBSublattice (octMirrorCoordinates p) := by
  have h0 := hp.1 0
  have h1 := hp.1 1
  have h2 := hp.1 2
  have hs := hp.2
  constructor
  · intro k
    fin_cases k <;> dsimp [octMirrorCoordinates] <;> omega
  · dsimp [coordinateSum, octMirrorCoordinates] at *
    omega

def octMirror (p : Site) : Site := ⟨octMirrorCoordinates p.val, by
  rcases p.property with hp | hp
  · exact Or.inl (octMirrorCoordinates_inA hp)
  · exact Or.inr (octMirrorCoordinates_inB hp)⟩

@[simp] theorem octMirror_involutive (p : Site) : octMirror (octMirror p) = p := by
  apply Subtype.ext
  funext k
  fin_cases k <;> dsimp [octMirror, octMirrorCoordinates] <;> omega

theorem octMirror_injective : Function.Injective octMirror :=
  Function.LeftInverse.injective octMirror_involutive

def octMirrorFace (i : Fin 4) : Fin 4 :=
  if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0 else 1

theorem tetraCoordinate_octMirror (m : ℕ) (p : Site) (i : Fin 4) :
    tetraCoordinate m (octMirror p).val i = tetraCoordinate m p.val (octMirrorFace i) := by
  fin_cases i <;> dsimp [tetraCoordinate, octMirror, octMirrorCoordinates, octMirrorFace] <;> omega

theorem octMirror_step (p : Site) (d : Fin 4) :
    octMirror (step p d) = step (octMirror p) (octMirrorFace d) := by
  apply Subtype.ext
  by_cases hp : InASublattice p.val
  · have hm : InASublattice (octMirror p).val := octMirrorCoordinates_inA hp
    change octMirrorCoordinates (step p d).val = (step (octMirror p) (octMirrorFace d)).val
    rw [step_val_of_A p hp d, step_val_of_A (octMirror p) hm (octMirrorFace d)]
    simp_rw [bondVector_eq_bondComponent]
    funext k
    fin_cases d <;> fin_cases k <;>
      dsimp [octMirrorCoordinates, octMirrorFace, bondComponent, octMirror] <;> omega
  · have hpB := (inB_iff_not_inA p).mpr hp
    have hm : InBSublattice (octMirror p).val := octMirrorCoordinates_inB hpB
    change octMirrorCoordinates (step p d).val = (step (octMirror p) (octMirrorFace d)).val
    rw [step_val_of_B p hpB d, step_val_of_B (octMirror p) hm (octMirrorFace d)]
    simp_rw [bondVector_eq_bondComponent]
    funext k
    fin_cases d <;> fin_cases k <;>
      dsimp [octMirrorCoordinates, octMirrorFace, bondComponent, octMirror] <;> omega

theorem octMirror_adj {p q : Site} (h : tetrahedralLattice.Adj p q) :
    tetrahedralLattice.Adj (octMirror p) (octMirror q) := by
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp h
  rw [octMirror_step]
  exact step_adj _ _

@[simp] theorem octMirror_adj_iff (p q : Site) :
    tetrahedralLattice.Adj (octMirror p) (octMirror q) ↔ tetrahedralLattice.Adj p q := by
  constructor
  · intro h
    simpa only [octMirror_involutive] using octMirror_adj h
  · exact octMirror_adj

theorem octMirror_inOctahedron (m : ℕ) {p : Site} (hp : InOctahedron m p) :
    InOctahedron m (octMirror p) := by
  intro i
  rw [tetraCoordinate_octMirror]
  exact hp (octMirrorFace i)

@[simp] theorem octMirror_mem_octahedron (m : ℕ) (p : Site) :
    octMirror p ∈ octahedron m ↔ p ∈ octahedron m := by
  constructor
  · intro hp
    have h := octMirror_inOctahedron m ((mem_octahedron m _).mp hp)
    simpa only [octMirror_involutive, mem_octahedron] using h
  · intro hp
    exact (mem_octahedron m _).mpr (octMirror_inOctahedron m ((mem_octahedron m p).mp hp))

theorem octMirror_image_layer (m : ℕ) (k : ℤ) :
    (finiteLayer (octahedron m) k).image octMirror = finiteLayer (octahedron m) (-k) := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have h := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨(octMirror_mem_octahedron m q).mpr h.1, ?_⟩
    change -q.val 0 = -k
    omega
  · intro hp
    have h := Finset.mem_filter.mp hp
    apply Finset.mem_image.mpr
    refine ⟨octMirror p, ?_, octMirror_involutive p⟩
    apply Finset.mem_filter.mpr
    refine ⟨(octMirror_mem_octahedron m p).mpr h.1, ?_⟩
    change -p.val 0 = k
    omega

theorem card_octahedron_layer_neg (m : ℕ) (k : ℤ) :
    (finiteLayer (octahedron m) (-k)).card = (finiteLayer (octahedron m) k).card := by
  rw [← octMirror_image_layer]
  exact Finset.card_image_of_injective _ octMirror_injective

end ProteinFolding.Tetrahedral
