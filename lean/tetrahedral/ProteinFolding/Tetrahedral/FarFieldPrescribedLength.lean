import ProteinFolding.Tetrahedral.FarFieldPadding

/-! The uniform size calculation in Lemma F(E), connected to the actual
padding paths of Part D. The old linker length beta is an explicit hypothesis
until the routing bounds in Parts A-C are proved. -/

namespace ProteinFolding.Tetrahedral.FarField

def baseRouteBound (m w : ℕ) : ℕ := 280 * m + 240 * w + 406
def uniformLinkerLength (m w : ℕ) : ℕ := 1000 * (m + w + 1) + 6

theorem baseRouteBound_lt (m w : ℕ) : baseRouteBound m w < 1000 * (m + w + 1) := by
  unfold baseRouteBound
  omega

theorem prescribed_increase (m w β L : ℕ) (hβ : β ≤ baseRouteBound m w)
    (hL : uniformLinkerLength m w ≤ L) (hparity : L % 2 = β % 2) :
    6 ≤ L - β ∧ (L - β) % 2 = 0 := by
  have hb := baseRouteBound_lt m w
  unfold uniformLinkerLength at hL
  omega

/-- Replacing the original avenue segment by this path increases the total
linker from beta to the prescribed length L. The returned identity is the
exact site accounting for that replacement. -/
theorem padding_for_prescribed_length (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool)
    (r b m w β L : ℕ) (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c)
    (hβ : β ≤ baseRouteBound m w) (hL : uniformLinkerLength m w ≤ L)
    (hparity : L % 2 = β % 2) :
    ∃ (n : ℕ) (f : Fold tetrahedralLattice n),
      n + β = (b - r + 1) + L ∧
      (∀ i, i.val = 0 → f.pos i = avenue c hc up r) ∧
      (∀ i, i.val + 1 = n → f.pos i = avenue c hc up b) ∧
      (∀ i, PositiveQuadrant R (f.pos i) ∧
        (rho R (f.pos i) = privateLevel R c up ∨ rho R (f.pos i) = privateLevel R c up + 2) ∧
        (alpha R (f.pos i) = privateStrip R c ∨ alpha R (f.pos i) = privateStrip R c + 2 ∨
          alpha R (f.pos i) = privateStrip R c + 4 ∨ alpha R (f.pos i) = privateStrip R c + 6)) := by
  have hinc := prescribed_increase m w β L hβ hL hparity
  obtain ⟨n, f, hn, hfirst, hlast, hprivate⟩ :=
    exists_even_padding_path R c hc up r b (L - β) hr hb hinc.1 hinc.2 hy hz
  refine ⟨n, f, ?_, hfirst, hlast, hprivate⟩
  have hβL : β ≤ L := by omega
  omega

end ProteinFolding.Tetrahedral.FarField
