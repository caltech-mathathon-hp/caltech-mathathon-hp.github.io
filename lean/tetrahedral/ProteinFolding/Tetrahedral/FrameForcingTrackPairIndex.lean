import ProteinFolding.Tetrahedral.FrameForcingTrackMatching
import ProteinFolding.Tetrahedral.FrameForcingHeightBounds

/-! Every actual HH pair on the complete track is one of its physical
even/odd pairs.  A P3-linked pair of distinct HH pairs is consecutive. -/

namespace ProteinFolding.Tetrahedral.FinitePairFamily

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

variable {ι : Type*}

def OnTrackPair (P : FinitePairFamily ι Site) (m : ℕ) (F : OctEdgeFrame) (i : ι) (k : ℕ) : Prop :=
  (P.point (i, false) = frameTrackPoint m F (2 * k) ∧
    P.point (i, true) = frameTrackPoint m F (2 * k + 1)) ∨
  (P.point (i, false) = frameTrackPoint m F (2 * k + 1) ∧
    P.point (i, true) = frameTrackPoint m F (2 * k))

theorem track_pair_index [Fintype ι] (P : FinitePairFamily ι Site) (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame)
    (hW : frameTrackSites m F ⊆ P.covered)
    (hclosed : ∀ i, P.point (i, false) ∈ frameTrackSites m F ↔ P.point (i, true) ∈ frameTrackSites m F)
    (hadj : ∀ i, tetrahedralLattice.Adj (P.point (i, false)) (P.point (i, true)))
    (i : ι) (hi : P.point (i, false) ∈ frameTrackSites m F) :
    ∃ k, 2 * k < 2 * m - 2 ∧ P.OnTrackPair m F i k := by
  obtain ⟨r, hr, hri⟩ := Finset.mem_image.mp hi
  have hr' := Finset.mem_range.mp hr
  let k := r / 2
  have hk : 2 * k < 2 * m - 2 := by dsimp only [k]; omega
  obtain ⟨j, b, heven, hodd⟩ := P.track_even_pair m hm F hW hclosed hadj k hk
  have hmod := Nat.mod_lt r (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div r 2
  refine ⟨k, hk, ?_⟩
  by_cases he : r % 2 = 0
  · have hrk : r = 2 * k := by dsimp only [k]; omega
    have hp : P.point (j, b) = P.point (i, false) := by rw [← heven, ← hrk]; exact hri
    have hid := P.injective hp
    have hj : j = i := congrArg Prod.fst hid
    have hb : b = false := congrArg Prod.snd hid
    subst j
    subst b
    exact Or.inl ⟨heven.symm, hodd.symm⟩
  · have hrk : r = 2 * k + 1 := by dsimp only [k]; omega
    have hp : P.point (j, !b) = P.point (i, false) := by rw [← hodd, ← hrk]; exact hri
    have hid := P.injective hp
    have hj : j = i := congrArg Prod.fst hid
    have hb : (!b : Bool) = false := congrArg Prod.snd hid
    have hb' : b = true := by cases b <;> simp_all
    subst j
    subst b
    exact Or.inr ⟨hodd.symm, heven.symm⟩

theorem OnTrackPair.index_ne (P : FinitePairFamily ι Site) (m : ℕ) (F : OctEdgeFrame)
    {i j : ι} {k l : ℕ} (hi : P.OnTrackPair m F i k) (hj : P.OnTrackPair m F j l)
    (hne : i ≠ j) : k ≠ l := by
  intro h
  subst l
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact hne (congrArg Prod.fst (P.injective (hi.1.trans hj.1.symm)))
  · exact hne (congrArg Prod.fst (P.injective (hi.1.trans hj.2.symm)))
  · exact hne (congrArg Prod.fst (P.injective (hi.2.trans hj.1.symm)))
  · exact hne (congrArg Prod.fst (P.injective (hi.2.trans hj.2.symm)))

theorem OnTrackPair.link_consecutive (P : FinitePairFamily ι Site) (m : ℕ) (hm : 1 ≤ m)
    (F : OctEdgeFrame) {i j : ι} {k l : ℕ}
    (hi : P.OnTrackPair m F i k) (hj : P.OnTrackPair m F j l) (hne : i ≠ j)
    (hlink : OctTriangularNeighbours m (P.point (i, true)) (P.point (j, false))) :
    k + 1 = l ∨ l + 1 = k := by
  have hkl := OnTrackPair.index_ne P m F hi hj hne
  have hh := frameH2_triangular_bounds m F hlink
  rcases hi with hi | hi <;> rcases hj with hj | hj
  all_goals rw [hi.2, hj.1, frameTrackPoint_H2 m hm F, frameTrackPoint_H2 m hm F] at hh
  all_goals push_cast at hh
  all_goals omega

end ProteinFolding.Tetrahedral.FinitePairFamily
