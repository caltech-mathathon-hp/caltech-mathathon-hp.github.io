import ProteinFolding.Tetrahedral.Octahedron
import ProteinFolding.Tetrahedral.GapRuns
import ProteinFolding.Tetrahedral.RootSum

/-! Explicit layer parametrisations and counts for Section 5.1. -/

namespace ProteinFolding.Tetrahedral

def evenLayerCoordinates (j u v : ℕ) (k : Fin 3) : ℤ :=
  if k = 0 then 2 * (j : ℤ)
  else if k = 1 then 2 * (j : ℤ) + 2 * (u : ℤ) + 2 * (v : ℤ)
  else 2 * (u : ℤ) - 2 * (v : ℤ)

theorem evenLayerCoordinates_inA (j u v : ℕ) : InASublattice (evenLayerCoordinates j u v) := by
  constructor
  · intro k
    fin_cases k <;> dsimp [evenLayerCoordinates] <;> omega
  · dsimp [coordinateSum, evenLayerCoordinates]
    omega

def evenLayerPoint (j u v : ℕ) : Site :=
  ⟨evenLayerCoordinates j u v, Or.inl (evenLayerCoordinates_inA j u v)⟩

def evenLayerImage (m j : ℕ) : Finset Site :=
  Finset.univ.image (fun uv : Fin (m - j) × Fin (m - j) =>
    evenLayerPoint j uv.1.val uv.2.val)

theorem evenLayerPoint_mem (m j u v : ℕ) (hu : u < m - j) (hv : v < m - j) :
    evenLayerPoint j u v ∈ octahedron m := by
  rw [mem_octahedron, inOctahedron_iff_A m (evenLayerCoordinates_inA j u v)]
  intro i
  fin_cases i <;> dsimp [tetraCoordinate, evenLayerPoint, evenLayerCoordinates, octRadius]
  all_goals constructor <;> omega

theorem mem_evenLayerImage (m j : ℕ) (p : Site) :
    p ∈ evenLayerImage m j ↔ p ∈ octahedron m ∧ p.val 0 = 2 * (j : ℤ) := by
  constructor
  · intro hp
    obtain ⟨⟨u, v⟩, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨evenLayerPoint_mem m j u.val v.val u.isLt v.isLt, rfl⟩
  · rintro ⟨hp, hx⟩
    have hpA : InASublattice p.val := (inA_iff_x_even p).mpr (by omega)
    have h := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m p).mp hp)
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have hc1 := tetraCoordinate_mod_A m hpA 1
    have hc2 := tetraCoordinate_mod_A m hpA 2
    dsimp [tetraCoordinate, octRadius] at h0 h1 h2 h3 hc1 hc2
    let u : ℕ := ((p.val 1 - p.val 0 + p.val 2) / 4).toNat
    let v : ℕ := ((p.val 1 - p.val 0 - p.val 2) / 4).toNat
    have hu : 4 * (u : ℤ) = p.val 1 - p.val 0 + p.val 2 := by
      dsimp [u]
      omega
    have hv : 4 * (v : ℤ) = p.val 1 - p.val 0 - p.val 2 := by
      dsimp [v]
      omega
    have hurange : u < m - j := by omega
    have hvrange : v < m - j := by omega
    apply Finset.mem_image.mpr
    refine ⟨(⟨u, hurange⟩, ⟨v, hvrange⟩), Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    funext k
    fin_cases k
    · change 2 * (j : ℤ) = p.val 0
      omega
    · change 2 * (j : ℤ) + 2 * (u : ℤ) + 2 * (v : ℤ) = p.val 1
      omega
    · change 2 * (u : ℤ) - 2 * (v : ℤ) = p.val 2
      omega

theorem evenLayerImage_eq_finiteLayer (m j : ℕ) :
    evenLayerImage m j = finiteLayer (octahedron m) (2 * (j : ℤ)) := by
  ext p
  rw [mem_evenLayerImage]
  simp only [finiteLayer, Finset.mem_filter]

theorem evenLayerImage_card (m j : ℕ) : (evenLayerImage m j).card = (m - j) ^ 2 := by
  unfold evenLayerImage
  rw [Finset.card_image_of_injective]
  · simp [Nat.pow_two]
  · intro uv wz heq
    have hy := congrArg (fun p : Site => p.val 1) heq
    have hz := congrArg (fun p : Site => p.val 2) heq
    dsimp [evenLayerPoint, evenLayerCoordinates] at hy hz
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- The nonnegative even layers have (m-j)^2 sites, including zero outside. -/
theorem card_octahedron_even_layer (m j : ℕ) :
    (finiteLayer (octahedron m) (2 * (j : ℤ))).card = (m - j) ^ 2 := by
  rw [← evenLayerImage_eq_finiteLayer, evenLayerImage_card]

theorem card_octahedron_central_layer (m : ℕ) :
    (finiteLayer (octahedron m) 0).card = m ^ 2 := by
  simpa using card_octahedron_even_layer m 0

def oddLayerCoordinates (j u v : ℕ) (k : Fin 3) : ℤ :=
  if k = 0 then 2 * (j : ℤ) + 1
  else if k = 1 then 2 * (j : ℤ) + 1 + 2 * (u : ℤ) + 2 * (v : ℤ)
  else 1 + 2 * (u : ℤ) - 2 * (v : ℤ)

theorem oddLayerCoordinates_inB (j u v : ℕ) : InBSublattice (oddLayerCoordinates j u v) := by
  constructor
  · intro k
    fin_cases k <;> dsimp [oddLayerCoordinates] <;> omega
  · dsimp [coordinateSum, oddLayerCoordinates]
    omega

def oddLayerPoint (j u v : ℕ) : Site :=
  ⟨oddLayerCoordinates j u v, Or.inr (oddLayerCoordinates_inB j u v)⟩

def oddLayerImage (m j : ℕ) : Finset Site :=
  Finset.univ.image (fun uv : Fin (m - j - 1) × Fin (m - j) =>
    oddLayerPoint j uv.1.val uv.2.val)

theorem oddLayerPoint_mem (m j u v : ℕ) (hu : u < m - j - 1) (hv : v < m - j) :
    oddLayerPoint j u v ∈ octahedron m := by
  rw [mem_octahedron, inOctahedron_iff_B m (oddLayerCoordinates_inB j u v)]
  intro i
  fin_cases i <;> dsimp [tetraCoordinate, oddLayerPoint, oddLayerCoordinates, octRadius]
  all_goals constructor <;> omega

theorem mem_oddLayerImage (m j : ℕ) (p : Site) :
    p ∈ oddLayerImage m j ↔ p ∈ octahedron m ∧ p.val 0 = 2 * (j : ℤ) + 1 := by
  constructor
  · intro hp
    obtain ⟨⟨u, v⟩, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨oddLayerPoint_mem m j u.val v.val u.isLt v.isLt, rfl⟩
  · rintro ⟨hp, hx⟩
    have hpB : InBSublattice p.val := (inB_iff_not_inA p).mpr (by
      intro hpA
      have he := hpA.1 0
      omega)
    have h := (inOctahedron_iff_B m hpB).mp ((mem_octahedron m p).mp hp)
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have hc1 := tetraCoordinate_mod_B m hpB 1
    have hc2 := tetraCoordinate_mod_B m hpB 2
    dsimp [tetraCoordinate, octRadius] at h0 h1 h2 h3 hc1 hc2
    let u : ℕ := ((p.val 1 - p.val 0 + p.val 2 - 1) / 4).toNat
    let v : ℕ := ((p.val 1 - p.val 0 - p.val 2 + 1) / 4).toNat
    have hu : 4 * (u : ℤ) = p.val 1 - p.val 0 + p.val 2 - 1 := by
      dsimp [u]
      omega
    have hv : 4 * (v : ℤ) = p.val 1 - p.val 0 - p.val 2 + 1 := by
      dsimp [v]
      omega
    have hurange : u < m - j - 1 := by omega
    have hvrange : v < m - j := by omega
    apply Finset.mem_image.mpr
    refine ⟨(⟨u, hurange⟩, ⟨v, hvrange⟩), Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    funext k
    fin_cases k
    · change 2 * (j : ℤ) + 1 = p.val 0
      omega
    · change 2 * (j : ℤ) + 1 + 2 * (u : ℤ) + 2 * (v : ℤ) = p.val 1
      omega
    · change 1 + 2 * (u : ℤ) - 2 * (v : ℤ) = p.val 2
      omega

theorem oddLayerImage_eq_finiteLayer (m j : ℕ) :
    oddLayerImage m j = finiteLayer (octahedron m) (2 * (j : ℤ) + 1) := by
  ext p
  rw [mem_oddLayerImage]
  simp only [finiteLayer, Finset.mem_filter]

theorem oddLayerImage_card (m j : ℕ) :
    (oddLayerImage m j).card = (m - j - 1) * (m - j) := by
  unfold oddLayerImage
  rw [Finset.card_image_of_injective]
  · simp
  · intro uv wz heq
    have hy := congrArg (fun p : Site => p.val 1) heq
    have hz := congrArg (fun p : Site => p.val 2) heq
    dsimp [oddLayerPoint, oddLayerCoordinates] at hy hz
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem card_octahedron_odd_layer (m j : ℕ) :
    (finiteLayer (octahedron m) (2 * (j : ℤ) + 1)).card = (m - j - 1) * (m - j) := by
  rw [← oddLayerImage_eq_finiteLayer, oddLayerImage_card]

end ProteinFolding.Tetrahedral
