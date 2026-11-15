import ProteinFolding.Cubic.Proofs.PackingGeometryRails
import ProteinFolding.Cubic.Proofs.PackingGeometryWalls

/-! A simple unit-step path on one geometric edge has no turn: it occupies
an integer interval in one of the two possible orders. This forces E-block
anchor intervals after the two packing rails have been identified. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicCertificates

theorem line_three_no_turn (x y z : ℤ) (hxy : (y - x).natAbs = 1)
    (hyz : (z - y).natAbs = 1) (hxz : x ≠ z) : z - y = y - x := by omega

theorem line_path_no_turn {t : ℕ} (x : Fin t → ℤ) (hinj : Function.Injective x)
    (hstep : ∀ i j : Fin t, i.val + 1 = j.val → (x j - x i).natAbs = 1)
    (i j k : Fin t) (hij : i.val + 1 = j.val) (hjk : j.val + 1 = k.val) :
    x k - x j = x j - x i := by
  have hne : x i ≠ x k := by
    intro he
    have hv := congrArg Fin.val (hinj he)
    omega
  exact line_three_no_turn (x i) (x j) (x k) (hstep i j hij) (hstep j k hjk) hne

theorem line_path_constant_increment {t : ℕ} (ht : 2 ≤ t)
    (x : Fin t → ℤ) (hinj : Function.Injective x)
    (hstep : ∀ i j : Fin t, i.val + 1 = j.val → (x j - x i).natAbs = 1) :
    ∀ k (hk : k + 1 < t),
      x ⟨k + 1, hk⟩ - x ⟨k, by omega⟩ = x ⟨1, by omega⟩ - x ⟨0, by omega⟩ := by
  intro k
  induction k with
  | zero => intro hk; rfl
  | succ k ih =>
    intro hk
    have htriple := line_path_no_turn x hinj hstep
      ⟨k, by omega⟩ ⟨k + 1, by omega⟩ ⟨k + 2, by omega⟩ rfl rfl
    exact htriple.trans (ih (by omega))

theorem line_path_affine {t : ℕ} (ht : 2 ≤ t)
    (x : Fin t → ℤ) (hinj : Function.Injective x)
    (hstep : ∀ i j : Fin t, i.val + 1 = j.val → (x j - x i).natAbs = 1) :
    ∀ i, x i = x ⟨0, by omega⟩ + (x ⟨1, by omega⟩ - x ⟨0, by omega⟩) * (i.val : ℤ) := by
  have hdiff := line_path_constant_increment ht x hinj hstep
  have haux : ∀ k (hk : k < t),
      x ⟨k, hk⟩ = x ⟨0, by omega⟩ + (x ⟨1, by omega⟩ - x ⟨0, by omega⟩) * (k : ℤ) := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have hd := hdiff k hk
      have hi := ih (by omega)
      rw [hi] at hd
      simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      omega
  intro i
  exact haux i.val i.isLt

theorem line_path_interval {t : ℕ} (ht : 0 < t)
    (x : Fin t → ℤ) (hinj : Function.Injective x)
    (hstep : ∀ i j : Fin t, i.val + 1 = j.val → (x j - x i).natAbs = 1) :
    (∀ i, x i = x ⟨0, ht⟩ + (i.val : ℤ)) ∨
      (∀ i, x i = x ⟨0, ht⟩ - (i.val : ℤ)) := by
  by_cases ht2 : 2 ≤ t
  · have h := line_path_affine ht2 x hinj hstep
    have hs := hstep ⟨0, ht⟩ ⟨1, by omega⟩ rfl
    have hsign : x ⟨1, by omega⟩ - x ⟨0, ht⟩ = 1 ∨
        x ⟨1, by omega⟩ - x ⟨0, ht⟩ = -1 := by omega
    rcases hsign with hs | hs
    · left; intro i; simpa only [hs, one_mul] using h i
    · right; intro i; simpa only [hs, neg_one_mul, sub_eq_add_neg] using h i
  · left
    intro i
    have he : i = (⟨0, ht⟩ : Fin t) := by apply Fin.ext; have := i.isLt; omega
    rw [he]
    simp

theorem openEdgePoint_distance (a : Site) (d : ℕ) (e : CubeEdge) (r s : Fin d) :
    latticeDistance (openEdgePoint a d e r) (openEdgePoint a d e s) =
      ((r.val : ℤ) - (s.val : ℤ)).natAbs := by
  rw [distance_eq]
  obtain ⟨axis, b, c⟩ := e
  fin_cases axis <;> simp only [openEdgePoint] <;> omega

/-- The actual geometric sites of an injective edge path occur in consecutive
coordinate order, possibly reversed. Thus each anchor block is an interval. -/
theorem openEdge_path_interval (a : Site) (d t : ℕ) (ht : 0 < t) (e : CubeEdge)
    (p : Fin t → Site) (hinj : Function.Injective p)
    (hstep : ∀ i j : Fin t, i.val + 1 = j.val → cubicLattice.Adj (p i) (p j))
    (hedge : ∀ i, p i ∈ openEdgeFinset a d e) :
    (∀ i, p i = Function.update (p ⟨0, ht⟩) e.axis (p ⟨0, ht⟩ e.axis + (i.val : ℤ))) ∨
      (∀ i, p i = Function.update (p ⟨0, ht⟩) e.axis (p ⟨0, ht⟩ e.axis - (i.val : ℤ))) := by
  have hex : ∀ i, ∃ r : Fin d, openEdgePoint a d e r = p i := by
    intro i
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp (hedge i)
    exact ⟨r, hr⟩
  let r : Fin t → Fin d := fun i => Classical.choose (hex i)
  have hr : ∀ i, openEdgePoint a d e (r i) = p i := fun i => Classical.choose_spec (hex i)
  let x : Fin t → ℤ := fun i => (r i).val
  have hx : Function.Injective x := by
    intro i j he
    have he' : r i = r j := by apply Fin.ext; dsimp [x] at he; omega
    apply hinj
    rw [← hr i, ← hr j, he']
  have hxs : ∀ i j : Fin t, i.val + 1 = j.val → (x j - x i).natAbs = 1 := by
    intro i j hij
    have h := (hstep i j hij).symm
    change latticeDistance (p j) (p i) = 1 at h
    rw [← hr j, ← hr i, openEdgePoint_distance] at h
    exact h
  have hxint := line_path_interval ht x hx hxs
  rcases hxint with hxint | hxint
  · left
    intro i
    funext k
    by_cases hk : k = e.axis
    · subst k
      rw [Function.update_self, ← hr i, ← hr ⟨0, ht⟩, openEdgePoint_axis, openEdgePoint_axis]
      have hi := hxint i
      dsimp only [x] at hi
      omega
    · rw [Function.update_of_ne hk, ← hr i, ← hr ⟨0, ht⟩,
        openEdgePoint_fixed a d e (r i) k hk, openEdgePoint_fixed a d e (r ⟨0, ht⟩) k hk]
  · right
    intro i
    funext k
    by_cases hk : k = e.axis
    · subst k
      rw [Function.update_self, ← hr i, ← hr ⟨0, ht⟩, openEdgePoint_axis, openEdgePoint_axis]
      have hi := hxint i
      dsimp only [x] at hi
      omega
    · rw [Function.update_of_ne hk, ← hr i, ← hr ⟨0, ht⟩,
        openEdgePoint_fixed a d e (r i) k hk, openEdgePoint_fixed a d e (r ⟨0, ht⟩) k hk]

end ProteinFolding.CubicPackingGeometry
