import ProteinFolding.Cubic.Proofs.PackingGeometryIntervals
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Nat

/-! Rigidity of equal anchor intervals tiling a rail. Their order along the
chain is irrelevant: geometric starts must be 1, β+1, ..., (q−1)β+1. -/

namespace ProteinFolding.CubicPackingGeometry

theorem interval_separation_of_disjoint (u v β : ℕ) (hβ : 0 < β)
    (hdisj : Disjoint (Finset.Ico u (u + β)) (Finset.Ico v (v + β))) :
    u + β ≤ v ∨ v + β ≤ u := by
  by_contra h
  by_cases huv : u ≤ v
  · have h1 : v ∈ Finset.Ico u (u + β) := Finset.mem_Ico.mpr ⟨huv, by omega⟩
    have h2 : v ∈ Finset.Ico v (v + β) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    exact Finset.disjoint_left.mp hdisj h1 h2
  · have h1 : u ∈ Finset.Ico u (u + β) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    have h2 : u ∈ Finset.Ico v (v + β) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    exact Finset.disjoint_left.mp hdisj h1 h2

theorem nat_line_interval_image {t : ℕ} (ht : 0 < t) (D : ℕ)
    (x : Fin t → ℕ) (hinj : Function.Injective x)
    (hstep : ∀ i j : Fin t, i.val + 1 = j.val → ((x j : ℤ) - (x i : ℤ)).natAbs = 1)
    (hbound : ∀ i, 1 ≤ x i ∧ x i ≤ D) :
    ∃ start : ℕ, 1 ≤ start ∧ start + t ≤ D + 1 ∧
      Finset.univ.image x = Finset.Ico start (start + t) := by
  let z : Fin t → ℤ := fun i => x i
  have hz : Function.Injective z := by
    intro i j hij
    apply hinj
    dsimp only [z] at hij
    omega
  have hline := line_path_interval ht z hz hstep
  let first : Fin t := ⟨0, ht⟩
  let last : Fin t := ⟨t - 1, by omega⟩
  have h0 := hbound first
  have hlast := hbound last
  rcases hline with hplus | hminus
  · have hvalue : ∀ i, x i = x first + i.val := by
      intro i
      have h := hplus i
      dsimp only [z, first] at h ⊢
      omega
    have hl := hvalue last
    change x last = x first + (t - 1) at hl
    refine ⟨x first, h0.1, by omega, ?_⟩
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨i, rfl⟩
      have hi := hvalue i
      have ht' := i.isLt
      omega
    · rintro ⟨hy0, hy1⟩
      let i : Fin t := ⟨y - x first, by omega⟩
      refine ⟨i, ?_⟩
      have hi := hvalue i
      change x i = x first + (y - x first) at hi
      omega
  · have hvalue : ∀ i, x i + i.val = x first := by
      intro i
      have h := hminus i
      dsimp only [z, first] at h ⊢
      omega
    have hl := hvalue last
    change x last + (t - 1) = x first at hl
    let start := x first + 1 - t
    have hs : 1 ≤ start := by dsimp [start]; omega
    have hsend : start + t = x first + 1 := by dsimp [start]; omega
    refine ⟨start, hs, by omega, ?_⟩
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨i, rfl⟩
      have hi := hvalue i
      have ht' := i.isLt
      dsimp only [start] at *
      omega
    · rintro ⟨hy0, hy1⟩
      let i : Fin t := ⟨x first - y, by omega⟩
      refine ⟨i, ?_⟩
      have hi := hvalue i
      change x i + (x first - y) = x first at hi
      omega

def railCoordinate (a : Site) (axis : Fin 3) (p : Site) : ℕ := (p axis - a axis).toNat

theorem railCoordinate_openEdgePoint (a : Site) (d : ℕ) (e : CubeEdge) (r : Fin d) :
    railCoordinate a e.axis (openEdgePoint a d e r) = r.val + 1 := by
  unfold railCoordinate
  rw [openEdgePoint_axis]
  omega

/-- The finite coordinate image of an actual edge path is precisely a
half-open interval of t successive rail sites, even when traversed backwards. -/
theorem openEdge_path_coordinate_image (a : Site) (d t : ℕ) (ht : 0 < t) (e : CubeEdge)
    (p : Fin t → Site) (hinj : Function.Injective p)
    (hstep : ∀ i j : Fin t, i.val + 1 = j.val → cubicLattice.Adj (p i) (p j))
    (hedge : ∀ i, p i ∈ openEdgeFinset a d e) :
    ∃ start : ℕ, 1 ≤ start ∧ start + t ≤ d + 1 ∧
      Finset.univ.image (fun i => railCoordinate a e.axis (p i)) = Finset.Ico start (start + t) := by
  have hex : ∀ i, ∃ r : Fin d, openEdgePoint a d e r = p i := by
    intro i
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp (hedge i)
    exact ⟨r, hr⟩
  let r : Fin t → Fin d := fun i => Classical.choose (hex i)
  have hr : ∀ i, openEdgePoint a d e (r i) = p i := fun i => Classical.choose_spec (hex i)
  let x : Fin t → ℕ := fun i => railCoordinate a e.axis (p i)
  have hx : ∀ i, x i = (r i).val + 1 := by
    intro i
    dsimp only [x]
    rw [← hr i, railCoordinate_openEdgePoint]
  apply nat_line_interval_image ht d x
  · intro i j he
    rw [hx i, hx j] at he
    have hrij : r i = r j := by apply Fin.ext; omega
    apply hinj
    rw [← hr i, ← hr j, hrij]
  · intro i j hij
    have h := (hstep i j hij).symm
    change latticeDistance (p j) (p i) = 1 at h
    rw [← hr j, ← hr i, openEdgePoint_distance] at h
    rw [hx i, hx j]
    omega
  · intro i
    rw [hx i]
    have hi := (r i).isLt
    omega

theorem tiled_interval_start_multiple (β D : ℕ) (hβ : 0 < β) (starts : Finset ℕ)
    (hlower : ∀ u ∈ starts, 1 ≤ u)
    (hupper : ∀ u ∈ starts, u + β ≤ D + 1)
    (hseparate : ∀ u ∈ starts, ∀ v ∈ starts, u ≠ v → u + β ≤ v ∨ v + β ≤ u)
    (hcover : ∀ y, 1 ≤ y → y ≤ D → ∃ u ∈ starts, u ≤ y ∧ y < u + β) :
    ∀ u ∈ starts, ∃ j : ℕ, u = j * β + 1 := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro hu
    have hu0 := hlower u hu
    by_cases hu1 : u = 1
    · exact ⟨0, by simpa using hu1⟩
    · have huD := hupper u hu
      obtain ⟨v, hv, hvu, huv⟩ := hcover (u - 1) (by omega) (by omega)
      have hvlt : v < u := by omega
      have hneq : v ≠ u := by omega
      have hsep := hseparate v hv u hu hneq
      have hnext : v + β = u := by omega
      obtain ⟨j, hj⟩ := ih v hvlt hv
      refine ⟨j + 1, ?_⟩
      rw [← hnext, hj]
      ring

/-- Every tiling by disjoint β-site anchor intervals has the same endpoints,
without assuming any ordering of those intervals in the protein sequence. -/
theorem tiled_interval_starts (β q : ℕ) (hβ : 0 < β) (starts : Finset ℕ)
    (hlower : ∀ u ∈ starts, 1 ≤ u)
    (hupper : ∀ u ∈ starts, u + β ≤ q * β + 1)
    (hseparate : ∀ u ∈ starts, ∀ v ∈ starts, u ≠ v → u + β ≤ v ∨ v + β ≤ u)
    (hcover : ∀ y, 1 ≤ y → y ≤ q * β → ∃ u ∈ starts, u ≤ y ∧ y < u + β) :
    starts = (Finset.range q).image (fun j => j * β + 1) := by
  have hmultiple := tiled_interval_start_multiple β (q * β) hβ starts hlower hupper hseparate hcover
  apply Finset.Subset.antisymm
  · intro u hu
    obtain ⟨j, hj⟩ := hmultiple u hu
    have hb := hupper u hu
    rw [hj] at hb
    have hm : (j + 1) * β ≤ q * β := by rw [Nat.add_mul, Nat.one_mul]; omega
    have hjq : j < q := by have := Nat.le_of_mul_le_mul_right hm hβ; omega
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjq, hj.symm⟩
  · intro u hu
    obtain ⟨j, hjq, rfl⟩ := Finset.mem_image.mp hu
    have hj : j < q := Finset.mem_range.mp hjq
    have hm := Nat.mul_le_mul_right β (by omega : j + 1 ≤ q)
    rw [Nat.add_mul, Nat.one_mul] at hm
    obtain ⟨v, hv, hvj, hjv⟩ := hcover (j * β + 1) (by omega) (by omega)
    obtain ⟨i, hi⟩ := hmultiple v hv
    rw [hi] at hvj hjv
    have hij : i ≤ j := Nat.le_of_mul_le_mul_right (by omega : i * β ≤ j * β) hβ
    have hji : j ≤ i := by
      by_contra hji
      have hn := Nat.mul_le_mul_right β (by omega : i + 1 ≤ j)
      rw [Nat.add_mul, Nat.one_mul] at hn
      omega
    have he : i = j := Nat.le_antisymm hij hji
    simpa only [hi, he] using hv

end ProteinFolding.CubicPackingGeometry
