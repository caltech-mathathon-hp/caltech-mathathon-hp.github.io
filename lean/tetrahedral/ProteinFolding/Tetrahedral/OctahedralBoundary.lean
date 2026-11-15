import ProteinFolding.Tetrahedral.Octahedron
import ProteinFolding.Tetrahedral.LocalStructure

/-! The coordinate changes and dangling-bond facts in Section 5.6(O1). -/

namespace ProteinFolding.Tetrahedral

/-- Scalar form of the four fixed bond vectors, avoiding vector-notation
normalisation in the affine coordinate calculations. -/
def bondComponent (d : Fin 4) (k : Fin 3) : ℤ :=
  if d = 0 then 1
  else if d = 1 then if k = 0 then 1 else -1
  else if d = 2 then if k = 1 then 1 else -1
  else if k = 2 then 1 else -1

theorem bondVector_eq_bondComponent (d : Fin 4) (k : Fin 3) :
    bondVector d k = bondComponent d k := by
  revert d k
  decide

theorem step_in_B {p : Site} (hp : InASublattice p.val) (d : Fin 4) :
    InBSublattice (step p d).val := by
  rw [step_val_of_A p hp d]
  exact add_bondVector_inB p.val hp d

theorem step_in_A {p : Site} (hp : InBSublattice p.val) (d : Fin 4) :
    InASublattice (step p d).val := by
  rw [step_val_of_B p hp d]
  exact sub_bondVector_inA p.val hp d

theorem tetraCoordinate_step_A (m : ℕ) {p : Site} (hp : InASublattice p.val)
    (d i : Fin 4) :
    tetraCoordinate m (step p d).val i = tetraCoordinate m p.val i +
      (if i = d then 3 else -1) := by
  rw [step_val_of_A p hp d]
  simp_rw [bondVector_eq_bondComponent]
  fin_cases i <;> fin_cases d <;> dsimp [tetraCoordinate, bondComponent] <;> omega

theorem tetraCoordinate_step_B (m : ℕ) {p : Site} (hp : InBSublattice p.val)
    (d i : Fin 4) :
    tetraCoordinate m (step p d).val i = tetraCoordinate m p.val i +
      (if i = d then -3 else 1) := by
  rw [step_val_of_B p hp d]
  simp_rw [bondVector_eq_bondComponent]
  fin_cases i <;> fin_cases d <;> dsimp [tetraCoordinate, bondComponent] <;> omega

theorem step_mem_octahedron_A (m : ℕ) {p : Site} (hpA : InASublattice p.val)
    (hp : p ∈ octahedron m) (d : Fin 4) :
    step p d ∈ octahedron m ↔ tetraCoordinate m p.val d < octRadius m := by
  have hinside := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m p).mp hp)
  rw [mem_octahedron, inOctahedron_iff_B m (step_in_B hpA d)]
  constructor
  · intro hq
    have h := hq d
    have ht := tetraCoordinate_step_A m hpA d d
    dsimp [octRadius] at *
    omega
  · intro hd i
    have hi := hinside i
    have hc := tetraCoordinate_mod_A m hpA i
    rw [tetraCoordinate_step_A m hpA d i]
    by_cases hid : i = d
    · subst i
      rw [if_pos rfl]
      dsimp [octRadius] at *
      exact ⟨by omega, by omega⟩
    · rw [if_neg hid]
      dsimp [octRadius] at *
      exact ⟨by omega, by omega⟩

theorem step_mem_octahedron_B (m : ℕ) {p : Site} (hpB : InBSublattice p.val)
    (hp : p ∈ octahedron m) (d : Fin 4) :
    step p d ∈ octahedron m ↔ -(2 * (m : ℤ) - 1) < tetraCoordinate m p.val d := by
  have hinside := (inOctahedron_iff_B m hpB).mp ((mem_octahedron m p).mp hp)
  rw [mem_octahedron, inOctahedron_iff_A m (step_in_A hpB d)]
  constructor
  · intro hq
    have h := hq d
    have ht := tetraCoordinate_step_B m hpB d d
    dsimp [octRadius] at *
    omega
  · intro hd i
    have hi := hinside i
    have hc := tetraCoordinate_mod_B m hpB i
    rw [tetraCoordinate_step_B m hpB d i]
    by_cases hid : i = d
    · subst i
      rw [if_pos rfl]
      dsimp [octRadius] at *
      exact ⟨by omega, by omega⟩
    · rw [if_neg hid]
      dsimp [octRadius] at *
      exact ⟨by omega, by omega⟩

/-- At A-sites, dangling directions are precisely the incident big faces. -/
theorem step_not_mem_octahedron_A (m : ℕ) {p : Site} (hpA : InASublattice p.val)
    (hp : p ∈ octahedron m) (d : Fin 4) :
    step p d ∉ octahedron m ↔ tetraCoordinate m p.val d = octRadius m := by
  rw [step_mem_octahedron_A m hpA hp d]
  have h := ((mem_octahedron m p).mp hp d).2
  omega

/-- At B-sites, dangling directions are precisely the incident small faces. -/
theorem step_not_mem_octahedron_B (m : ℕ) {p : Site} (hpB : InBSublattice p.val)
    (hp : p ∈ octahedron m) (d : Fin 4) :
    step p d ∉ octahedron m ↔ tetraCoordinate m p.val d = -(2 * (m : ℤ) - 1) := by
  rw [step_mem_octahedron_B m hpB hp d]
  have h := ((mem_octahedron m p).mp hp d).1
  omega

/-- An outside neighbour of an octahedron site has no second neighbour inside. -/
theorem outside_step_unique_inside (m : ℕ) {p : Site} (hp : p ∈ octahedron m)
    (d : Fin 4) (hout : step p d ∉ octahedron m) {r : Site}
    (hadj : tetrahedralLattice.Adj (step p d) r) (hr : r ∈ octahedron m) : r = p := by
  obtain ⟨e, rfl⟩ := (adj_iff_exists_step (step p d) r).mp hadj
  by_cases he : e = d
  · subst e
    exact step_step p d
  · have hde : d ≠ e := Ne.symm he
    have hi := (mem_octahedron m _).mp hr d
    rcases p.property with hpA | hpB
    · have hf := (step_not_mem_octahedron_A m hpA hp d).mp hout
      have hq := tetraCoordinate_step_A m hpA d d
      have hr' := tetraCoordinate_step_B m (step_in_B hpA d) e d
      simp only [if_neg hde] at hr'
      dsimp [octRadius] at *
      omega
    · have hf := (step_not_mem_octahedron_B m hpB hp d).mp hout
      have hq := tetraCoordinate_step_B m hpB d d
      have hr' := tetraCoordinate_step_A m (step_in_A hpB d) e d
      simp only [if_neg hde] at hr'
      dsimp [octRadius] at *
      omega

def IsDangling (m : ℕ) (q : Site) : Prop :=
  q ∉ octahedron m ∧ ∃ p ∈ octahedron m, tetrahedralLattice.Adj p q

theorem dangling_unique_inside (m : ℕ) {q : Site} (hq : IsDangling m q) :
    ∃! p : Site, p ∈ octahedron m ∧ tetrahedralLattice.Adj p q := by
  obtain ⟨hpout, p, hp, hpq⟩ := hq
  obtain ⟨d, hd⟩ := (adj_iff_exists_step p q).mp hpq
  refine ⟨p, ⟨hp, hpq⟩, ?_⟩
  intro r hr
  apply outside_step_unique_inside m hp d
  · simpa [hd] using hpout
  · simpa [hd] using hr.2.symm
  · exact hr.1

/-- Two dangling sites are never adjacent, the final clause of (O1). -/
theorem dangling_not_adjacent (m : ℕ) {q r : Site}
    (hq : IsDangling m q) (hr : IsDangling m r) : ¬ tetrahedralLattice.Adj q r := by
  intro hqr
  obtain ⟨hqout, p, hp, hpq⟩ := hq
  obtain ⟨hrout, s, hs, hsr⟩ := hr
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp hpq
  obtain ⟨e, rfl⟩ := (adj_iff_exists_step (step p d) r).mp hqr
  obtain ⟨f, hf⟩ := (adj_iff_exists_step (step (step p d) e) s).mp hsr.symm
  have hs' : step (step (step p d) e) f ∈ octahedron m := by rw [hf]; exact hs
  have he : e ≠ d := by
    intro he
    subst e
    exact hrout (by simpa only [step_step] using hp)
  have hde : d ≠ e := Ne.symm he
  have hi := (mem_octahedron m _).mp hs' d
  rcases p.property with hpA | hpB
  · have hface := (step_not_mem_octahedron_A m hpA hp d).mp hqout
    have hqf := tetraCoordinate_step_A m hpA d d
    have hrf := tetraCoordinate_step_B m (step_in_B hpA d) e d
    have hsf := tetraCoordinate_step_A m (step_in_A (step_in_B hpA d) e) f d
    simp only [if_neg hde] at hrf
    by_cases hdf : d = f
    · rw [if_pos hdf] at hsf
      dsimp [octRadius] at *
      omega
    · rw [if_neg hdf] at hsf
      dsimp [octRadius] at *
      omega
  · have hface := (step_not_mem_octahedron_B m hpB hp d).mp hqout
    have hqf := tetraCoordinate_step_B m hpB d d
    have hrf := tetraCoordinate_step_A m (step_in_A hpB d) e d
    have hsf := tetraCoordinate_step_B m (step_in_B (step_in_A hpB d) e) f d
    simp only [if_neg hde] at hrf
    by_cases hdf : d = f
    · rw [if_pos hdf] at hsf
      dsimp [octRadius] at *
      omega
    · rw [if_neg hdf] at hsf
      dsimp [octRadius] at *
      omega

end ProteinFolding.Tetrahedral
