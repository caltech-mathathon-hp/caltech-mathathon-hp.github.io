import ProteinFolding.Tetrahedral.FarFieldThroughAvenue

namespace ProteinFolding.Tetrahedral.FarField

theorem margins_of_level (R : ℤ) (p : Site) (hp : PositiveQuadrant R p)
    (hlevel : |alpha R p| + 8 < rho R p) : 5 ≤ Y R p ∧ 5 ≤ Z p := by
  have hplus : alpha R p ≤ |alpha R p| := le_abs_self _
  have hminus : -alpha R p ≤ |alpha R p| := neg_le_abs _
  simp only [rho, alpha, abs_of_pos hp.1, abs_of_pos hp.2] at hlevel hplus hminus
  omega

def wireAvenue (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (T : Site) (x : ℤ) : Site :=
  let p := quadrantUnmap R hR q T
  let c := throughAnchor p
  quadrantAvenue R hR q c (throughAnchor_A p) (throughUp p) (x - X (quadrantMap R hR q c))

@[simp] theorem wireAvenue_x (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (T : Site) (x : ℤ) :
    X (wireAvenue R hR q T x) = x := by
  simp only [wireAvenue, quadrantAvenue_x]
  omega

theorem wireAvenue_injective (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (T : Site) :
    Function.Injective (wireAvenue R hR q T) := by
  intro x y h
  simpa only [wireAvenue_x] using congrArg X h

theorem wireAvenue_adj (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (T : Site) (x : ℤ) :
    tetrahedralLattice.Adj (wireAvenue R hR q T x) (wireAvenue R hR q T (x + 1)) := by
  unfold wireAvenue
  have h : x - X (quadrantMap R hR q (throughAnchor (quadrantUnmap R hR q T))) + 1 =
      (x + 1) - X (quadrantMap R hR q (throughAnchor (quadrantUnmap R hR q T))) := by omega
  simpa only [h] using quadrantAvenue_adj R hR q (throughAnchor (quadrantUnmap R hR q T))
    (throughAnchor_A (quadrantUnmap R hR q T)) (throughUp (quadrantUnmap R hR q T)) (x - X (quadrantMap R hR q (throughAnchor (quadrantUnmap R hR q T))))

theorem wireAvenue_setup (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (T : Site)
    (hq : InQuadrant R q T) (hlevel : |alpha R T| + 8 < rho R T) :
    let p := quadrantUnmap R hR q T
    (4 ≤ Y R (throughAnchor p) ∧ 4 ≤ Z (throughAnchor p)) ∧
      privateLevel R (throughAnchor p) (throughUp p) = rho R T ∧
      privateStrip R (throughAnchor p) = alpha R T := by
  let p := quadrantUnmap R hR q T
  have hpos : PositiveQuadrant R p :=
    (quadrantMap_positive_iff R hR q p).1 (by simpa only [p, quadrantMap_unmap] using hq)
  have hlev : |alpha R p| + 8 < rho R p := by
    simpa only [p, quadrantUnmap_rho, quadrantUnmap_alpha] using hlevel
  have hm := margins_of_level R p hpos hlev
  have hm' := throughAnchor_margins R p (by omega) hm.2
  have hp := throughAnchor_private R p (by omega) hm.2
  refine ⟨hm', ?_, ?_⟩
  · simpa only [p, quadrantUnmap_rho] using hp.1
  · simpa only [p, quadrantUnmap_alpha] using hp.2

theorem wireAvenue_member (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (T : Site) (x : ℤ)
    (hq : InQuadrant R q T) (hlevel : |alpha R T| + 8 < rho R T) :
    AvenueMembership R (rho R T) (alpha R T) q (wireAvenue R hR q T x) := by
  have hsetup := wireAvenue_setup R hR q T hq hlevel
  dsimp only at hsetup
  have hmem := quadrantAvenue_member R hR q (throughAnchor (quadrantUnmap R hR q T))
    (throughAnchor_A (quadrantUnmap R hR q T)) (throughUp (quadrantUnmap R hR q T)) (x - X (quadrantMap R hR q (throughAnchor (quadrantUnmap R hR q T))))
    hsetup.1.1 hsetup.1.2
  simpa only [wireAvenue, hsetup.2.1, hsetup.2.2] using hmem

theorem wireAvenue_self (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (T : Site)
    (hq : InQuadrant R q T) (hlevel : |alpha R T| + 8 < rho R T) :
    wireAvenue R hR q T (X T) = T := by
  have hsetup := wireAvenue_setup R hR q T hq hlevel
  dsimp only at hsetup
  have hmem : AvenueMembership R
      (privateLevel R (throughAnchor (quadrantUnmap R hR q T)) (throughUp (quadrantUnmap R hR q T)))
      (privateStrip R (throughAnchor (quadrantUnmap R hR q T))) q T := by
    rw [hsetup.2.1, hsetup.2.2]
    exact ⟨hq, Or.inl rfl, Or.inl rfl⟩
  obtain ⟨n, hn⟩ := quadrantAvenue_exhaustive R hR q (throughAnchor (quadrantUnmap R hR q T))
    (throughAnchor_A (quadrantUnmap R hR q T)) (throughUp (quadrantUnmap R hR q T)) T hsetup.1.1 hsetup.1.2 hmem
  have hX := congrArg X hn
  rw [quadrantAvenue_x] at hX
  have hindex : X T - X (quadrantMap R hR q (throughAnchor (quadrantUnmap R hR q T))) = n := by omega
  simpa only [wireAvenue, hindex] using hn

theorem wireAvenue_upper_rung (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (T : Site) (ξ : ℤ)
    (hq : InQuadrant R q T) (hlevel : |alpha R T| + 8 < rho R T) :
    ∃ x : ℤ, ξ ≤ x ∧ x ≤ ξ + 3 ∧
      rho R (wireAvenue R hR q T x) = rho R T + 2 ∧
      rho R (wireAvenue R hR q T (x - 1)) = rho R T ∧
      alpha R (wireAvenue R hR q T x) = alpha R (wireAvenue R hR q T (x - 1)) := by
  let p := quadrantUnmap R hR q T
  let c := throughAnchor p
  have hsetup := wireAvenue_setup R hR q T hq hlevel
  dsimp only at hsetup
  obtain ⟨n, hn0, hn1, hn2, hn3, hn4, _⟩ :=
    exists_upper_rung_at_X R hR q c (throughAnchor_A p) (throughUp p) ξ hsetup.1.1 hsetup.1.2
  let E := quadrantAvenue R hR q c (throughAnchor_A p) (throughUp p) n
  have he : wireAvenue R hR q T (X E) = E := by
    have hX := quadrantAvenue_x R hR q c (throughAnchor_A p) (throughUp p) n
    have hidx : X E - X (quadrantMap R hR q c) = n := by dsimp only [E]; omega
    change quadrantAvenue R hR q c (throughAnchor_A p) (throughUp p)
      (X E - X (quadrantMap R hR q c)) = E
    rw [hidx]
  have heprev : wireAvenue R hR q T (X E - 1) =
      quadrantAvenue R hR q c (throughAnchor_A p) (throughUp p) (n - 1) := by
    have hX := quadrantAvenue_x R hR q c (throughAnchor_A p) (throughUp p) n
    have hidx : X E - 1 - X (quadrantMap R hR q c) = n - 1 := by dsimp only [E]; omega
    simp only [wireAvenue, p, c, hidx]
  refine ⟨X E, hn0, hn1, ?_, ?_, ?_⟩
  · rw [he, ← hsetup.2.1]
    exact hn2
  · rw [heprev, ← hsetup.2.1]
    exact hn3
  · rw [he, heprev]
    exact hn4

end ProteinFolding.Tetrahedral.FarField
