import ProteinFolding.Tetrahedral.Geometry

namespace ProteinFolding.Tetrahedral.FarField

def colour (p : Site) : Bool := decide (InASublattice p.val)

theorem adj_colour {p q : Site} (h : tetrahedralLattice.Adj p q) : colour q = !colour p := by
  by_cases hp : InASublattice p.val
  · have hq := (adj_not_same_sublattice h).1 hp
    simp [colour, hp, hq]
  · have hq : InASublattice q.val := by
      by_contra hn
      exact hp ((adj_not_same_sublattice h).2 hn)
    simp [colour, hp, hq]

theorem fold_colour {n : ℕ} (f : Fold tetrahedralLattice n) (hn : 0 < n) (k : ℕ) (hk : k < n) :
    colour (f.pos ⟨k, hk⟩) =
      if k % 2 = 0 then colour (f.pos ⟨0, hn⟩) else !colour (f.pos ⟨0, hn⟩) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < n := by omega
    have hadj := f.consecutive ⟨k, hk'⟩ ⟨k + 1, hk⟩ rfl
    rw [adj_colour hadj, ih hk']
    by_cases h : k % 2 = 0
    · have h' : (k + 1) % 2 ≠ 0 := by omega
      simp [h, h']
    · have h' : (k + 1) % 2 = 0 := by omega
      simp [h, h']

theorem fold_endpoint_colour {n : ℕ} (f : Fold tetrahedralLattice n) (hn : 0 < n) :
    colour (f.pos ⟨0, hn⟩) = colour (f.pos ⟨n - 1, by omega⟩) ↔ n % 2 = 1 := by
  have h := fold_colour f hn (n - 1) (by omega)
  rw [h]
  by_cases hp : (n - 1) % 2 = 0
  · have hn' : n % 2 = 1 := by omega
    simp [hp, hn']
  · have hn' : n % 2 = 0 := by omega
    cases hc : colour (f.pos ⟨0, hn⟩) <;> simp [hp, hn', hc]

/-- Site-count parity of a path including both caps: odd for equal colours,
even for opposite colours. This is proved from actual lattice edges. -/
def CapParity (p q : Site) (L : ℕ) : Prop :=
  if colour p = colour q then L % 2 = 1 else L % 2 = 0

theorem fold_capParity {n : ℕ} (f : Fold tetrahedralLattice n) (hn : 0 < n) :
    CapParity (f.pos ⟨0, hn⟩) (f.pos ⟨n - 1, by omega⟩) n := by
  have hp := fold_endpoint_colour f hn
  by_cases h : colour (f.pos ⟨0, hn⟩) = colour (f.pos ⟨n - 1, by omega⟩)
  · simp only [CapParity, if_pos h]
    exact hp.1 h
  · simp only [CapParity, if_neg h]
    have hodd : n % 2 ≠ 1 := fun he => h (hp.2 he)
    omega

theorem capParity_mod_eq (p q : Site) (N L : ℕ) (hN : CapParity p q N) (hL : CapParity p q L) :
    L % 2 = N % 2 := by
  by_cases h : colour p = colour q <;> simp only [CapParity, h, ite_true, ite_false] at hN hL <;> omega

end ProteinFolding.Tetrahedral.FarField
