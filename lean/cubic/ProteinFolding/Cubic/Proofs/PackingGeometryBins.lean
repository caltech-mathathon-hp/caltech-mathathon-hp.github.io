import ProteinFolding.Cubic.Proofs.PackingGeometryWalls

/-! Connected paths cannot cross occupied wall rows, and a rectangular bin
has the product of its side lengths as its exact finite capacity. -/

namespace ProteinFolding.CubicPackingGeometry

theorem coordinate_strip_step (lo hi : ℤ) (axis : Fin 3) {p q : Site}
    (hp : lo < p axis ∧ p axis < hi) (hq : q axis ≠ lo ∧ q axis ≠ hi)
    (hadj : cubicLattice.Adj p q) : lo < q axis ∧ q axis < hi := by
  have h := adjacent_coordinate_bounds hadj axis
  omega

theorem coordinate_strip_path_closed {N : ℕ} (p : Fin N → Site) (hN : 0 < N)
    (lo hi : ℤ) (axis : Fin 3)
    (hfirst : lo < p ⟨0, hN⟩ axis ∧ p ⟨0, hN⟩ axis < hi)
    (havoid : ∀ i, p i axis ≠ lo ∧ p i axis ≠ hi)
    (hstep : ∀ i j : Fin N, i.val + 1 = j.val → cubicLattice.Adj (p i) (p j)) :
    ∀ i, lo < p i axis ∧ p i axis < hi := by
  have h : ∀ k (hk : k < N), lo < p ⟨k, hk⟩ axis ∧ p ⟨k, hk⟩ axis < hi := by
    intro k
    induction k with
    | zero => intro hk; exact hfirst
    | succ k ih =>
      intro hk
      have hk' : k < N := by omega
      exact coordinate_strip_step lo hi axis (ih hk') (havoid ⟨k + 1, hk⟩)
        (hstep ⟨k, hk'⟩ ⟨k + 1, hk⟩ rfl)
  intro i
  exact h i.val i.isLt

def rectanglePoint (a : Site) (x y : Fin 3) (startX startY : ℤ)
    {w h : ℕ} (q : Fin w × Fin h) : Site :=
  Function.update (Function.update a x (startX + q.1.val)) y (startY + q.2.val)

theorem rectanglePoint_x (a : Site) (x y : Fin 3) (hxy : x ≠ y) (startX startY : ℤ)
    {w h : ℕ} (q : Fin w × Fin h) : rectanglePoint a x y startX startY q x = startX + q.1.val := by
  simp only [rectanglePoint, Function.update_of_ne hxy, Function.update_self]

theorem rectanglePoint_y (a : Site) (x y : Fin 3) (startX startY : ℤ)
    {w h : ℕ} (q : Fin w × Fin h) : rectanglePoint a x y startX startY q y = startY + q.2.val := by
  simp only [rectanglePoint, Function.update_self]

theorem rectanglePoint_other (a : Site) (x y k : Fin 3) (hx : k ≠ x) (hy : k ≠ y)
    (startX startY : ℤ) {w h : ℕ} (q : Fin w × Fin h) :
    rectanglePoint a x y startX startY q k = a k := by
  simp only [rectanglePoint, Function.update_of_ne hy, Function.update_of_ne hx]

theorem rectanglePoint_injective (a : Site) (x y : Fin 3) (hxy : x ≠ y) (startX startY : ℤ)
    (w h : ℕ) : Function.Injective (rectanglePoint a x y startX startY : Fin w × Fin h → Site) := by
  intro q r he
  have hx := congrFun he x
  have hy := congrFun he y
  rw [rectanglePoint_x a x y hxy startX startY, rectanglePoint_x a x y hxy startX startY] at hx
  rw [rectanglePoint_y, rectanglePoint_y] at hy
  apply Prod.ext
  · apply Fin.ext; omega
  · apply Fin.ext; omega

def rectangleFinset (a : Site) (x y : Fin 3) (startX startY : ℤ) (w h : ℕ) : Finset Site :=
  Finset.univ.image (rectanglePoint a x y startX startY : Fin w × Fin h → Site)

theorem rectangleFinset_card (a : Site) (x y : Fin 3) (hxy : x ≠ y) (startX startY : ℤ) (w h : ℕ) :
    (rectangleFinset a x y startX startY w h).card = w * h := by
  rw [rectangleFinset, Finset.card_image_of_injective _ (rectanglePoint_injective a x y hxy startX startY w h)]
  simp

theorem mem_rectangleFinset (a : Site) (x y : Fin 3) (hxy : x ≠ y) (startX startY : ℤ)
    (w h : ℕ) (p : Site) :
    p ∈ rectangleFinset a x y startX startY w h ↔
      (startX ≤ p x ∧ p x < startX + (w : ℤ)) ∧
      (startY ≤ p y ∧ p y < startY + (h : ℤ)) ∧
      ∀ k, k ≠ x → k ≠ y → p k = a k := by
  constructor
  · intro hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨?_, ?_, ?_⟩
    · rw [rectanglePoint_x a x y hxy startX startY]
      have hq := q.1.isLt
      omega
    · rw [rectanglePoint_y]
      have hq := q.2.isLt
      omega
    · intro k hkx hky
      exact rectanglePoint_other a x y k hkx hky startX startY q
  · rintro ⟨hx, hy, hother⟩
    let q : Fin w × Fin h :=
      (⟨(p x - startX).toNat, (Int.toNat_lt (by omega)).mpr (by omega)⟩,
       ⟨(p y - startY).toNat, (Int.toNat_lt (by omega)).mpr (by omega)⟩)
    refine Finset.mem_image.mpr ⟨q, Finset.mem_univ _, ?_⟩
    funext k
    by_cases hky : k = y
    · subst k
      rw [rectanglePoint_y]
      dsimp only [q]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    · by_cases hkx : k = x
      · subst k
        rw [rectanglePoint_x a x y hxy startX startY]
        dsimp only [q]
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      · rw [rectanglePoint_other a x y k hkx hky startX startY]
        exact (hother k hkx hky).symm

theorem rectangle_occupancy_bound {ι : Type*} [DecidableEq ι]
    (a : Site) (x y : Fin 3) (hxy : x ≠ y) (startX startY : ℤ) (w h : ℕ)
    (s : Finset ι) (p : ι → Site) (hinj : Function.Injective p)
    (hp : ∀ i ∈ s, p i ∈ rectangleFinset a x y startX startY w h) : s.card ≤ w * h := by
  rw [← Finset.card_image_of_injective s hinj, ← rectangleFinset_card a x y hxy startX startY w h]
  apply Finset.card_le_card
  intro q hq
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
  exact hp i hi

def faceStripFinset (a : Site) (d : ℕ) (normal : Fin 3) (upper : Bool)
    (x y : Fin 3) (lo hi : ℤ) : Finset Site :=
  rectangleFinset (Function.update a normal (endValue (a normal) d (faceSide upper)))
    x y (a x + 1) (lo + 1) d (hi - lo - 1).toNat

theorem faceStripFinset_card (a : Site) (d : ℕ) (normal : Fin 3) (upper : Bool)
    (x y : Fin 3) (hxy : x ≠ y) (lo hi : ℤ) :
    (faceStripFinset a d normal upper x y lo hi).card = d * (hi - lo - 1).toNat :=
  rectangleFinset_card _ x y hxy _ _ _ _

theorem mem_faceStrip_of_faceInterior {a p : Site} {d : ℕ} {normal : Fin 3} {upper : Bool}
    (x y : Fin 3) (hxy : x ≠ y) (hx : x ≠ normal) (hy : y ≠ normal) (lo hi : ℤ)
    (hface : FaceInterior a (d + 2) normal upper p) (hstrip : lo < p y ∧ p y < hi) :
    p ∈ faceStripFinset a d normal upper x y lo hi := by
  apply (mem_rectangleFinset _ x y hxy _ _ _ _ p).mpr
  refine ⟨?_, ?_, ?_⟩
  · have h := hface.2.2 x hx
    omega
  · have hnonneg : 0 ≤ hi - lo - 1 := by omega
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  · intro k hkx hky
    have hkn : k = normal := by apply Fin.ext; omega
    subst k
    rw [Function.update_self]
    exact faceInterior_normal_value hface

theorem faceStrip_occupancy_bound {ι : Type*} [DecidableEq ι]
    (a : Site) (d : ℕ) (normal : Fin 3) (upper : Bool) (x y : Fin 3)
    (hxy : x ≠ y) (hx : x ≠ normal) (hy : y ≠ normal) (lo hi : ℤ)
    (s : Finset ι) (p : ι → Site) (hinj : Function.Injective p)
    (hface : ∀ i ∈ s, FaceInterior a (d + 2) normal upper (p i))
    (hstrip : ∀ i ∈ s, lo < p i y ∧ p i y < hi) : s.card ≤ d * (hi - lo - 1).toNat := by
  rw [← faceStripFinset_card a d normal upper x y hxy lo hi]
  have hsub : s.image p ⊆ faceStripFinset a d normal upper x y lo hi := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact mem_faceStrip_of_faceInterior x y hxy hx hy lo _ (hface i hi) (hstrip i hi)
  rw [← Finset.card_image_of_injective s hinj]
  exact Finset.card_le_card hsub

theorem faceInterior_occupancy_bound_axes {ι : Type*} [DecidableEq ι]
    (a : Site) (d : ℕ) (normal : Fin 3) (upper : Bool) (x y : Fin 3)
    (hxy : x ≠ y) (hx : x ≠ normal) (hy : y ≠ normal)
    (s : Finset ι) (p : ι → Site) (hinj : Function.Injective p)
    (hface : ∀ i ∈ s, FaceInterior a (d + 2) normal upper (p i)) : s.card ≤ d ^ 2 := by
  have hstrip : ∀ i ∈ s, a y < p i y ∧ p i y < a y + (d : ℤ) + 1 := by
    intro i hi
    have h := (hface i hi).2.2 y hy
    omega
  have h := faceStrip_occupancy_bound a d normal upper x y hxy hx hy
    (a y) (a y + (d : ℤ) + 1) s p hinj hface hstrip
  have he : (a y + (d : ℤ) + 1 - a y - 1).toNat = d := by omega
  rw [he, ← Nat.pow_two] at h
  exact h

/-- Every cube face interior has capacity d², in any orientation. -/
theorem faceInterior_occupancy_bound {ι : Type*} [DecidableEq ι]
    (a : Site) (d : ℕ) (normal : Fin 3) (upper : Bool)
    (s : Finset ι) (p : ι → Site) (hinj : Function.Injective p)
    (hface : ∀ i ∈ s, FaceInterior a (d + 2) normal upper (p i)) : s.card ≤ d ^ 2 := by
  fin_cases normal
  · exact faceInterior_occupancy_bound_axes a d 0 upper 1 2 (by decide) (by decide) (by decide) s p hinj hface
  · exact faceInterior_occupancy_bound_axes a d 1 upper 0 2 (by decide) (by decide) (by decide) s p hinj hface
  · exact faceInterior_occupancy_bound_axes a d 2 upper 0 1 (by decide) (by decide) (by decide) s p hinj hface

end ProteinFolding.CubicPackingGeometry
