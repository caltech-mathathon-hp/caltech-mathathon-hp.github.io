import ProteinFolding.Cubic.Proofs.PackingRoutingInitial
import ProteinFolding.Cubic.Proofs.PackingItemAllocation
import ProteinFolding.Common.FoldConcatenation

/-! Ordinary exterior connectors with arbitrary ordering of their two port
rows. The chosen orientation changes the traversal, never the literal number
of inserted P residues. Distinct connector depths and distinct ports separate
the complete paths. -/

namespace ProteinFolding.CubicPackingRouting

open CubicCertificates

def portWidth (u v : ℕ) : ℕ := max u v - min u v

theorem portWidth_pos (u v : ℕ) (hne : u ≠ v) : 0 < portWidth u v := by
  unfold portWidth
  omega

theorem portWidth_endpoints (u v : ℕ) :
    min u v + portWidth u v = max u v := by
  unfold portWidth
  omega

def portConnector (d : ℤ) (u v h r n : ℕ) (hh : 0 < h) (hr : 0 < r) (huv : u ≠ v)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3) : Fold cubicLattice (4 * n) :=
  let f := rectangleConnector d ((min u v : ℕ) : ℤ) h r (portWidth u v) n hh hr (portWidth_pos u v huv) hlen
  if u ≤ v then f else f.reverse

theorem portConnector_below (d : ℤ) (u v h r n : ℕ) (hh : 2 ≤ h) (hr : 0 < r) (huv : u ≠ v)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3) (i : Fin (4 * n)) :
    (portConnector d u v h r n (by omega) hr huv hlen).pos i 2 ≤ -2 := by
  unfold portConnector
  split_ifs
  · exact rectangleConnector_below_face_P d ((min u v : ℕ) : ℤ) h r (portWidth u v) n hh hr
      (portWidth_pos u v huv) hlen i
  · exact rectangleConnector_below_face_P d ((min u v : ℕ) : ℤ) h r (portWidth u v) n hh hr
      (portWidth_pos u v huv) hlen i.rev

theorem portConnector_pillar_or_depth (d : ℤ) (u v h r n : ℕ)
    (hh : 0 < h) (hr : 0 < r) (huv : u ≠ v)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3) (i : Fin (4 * n)) :
    ((portConnector d u v h r n hh hr huv hlen).pos i 0 = d ∧
      ((portConnector d u v h r n hh hr huv hlen).pos i 1 = u ∨
        (portConnector d u v h r n hh hr huv hlen).pos i 1 = v)) ∨
    (d < (portConnector d u v h r n hh hr huv hlen).pos i 0 ∧
      (portConnector d u v h r n hh hr huv hlen).pos i 2 = -(h : ℤ)) := by
  have he : ((min u v : ℕ) : ℤ) + portWidth u v = ((max u v : ℕ) : ℤ) := by
    exact_mod_cast portWidth_endpoints u v
  unfold portConnector
  split_ifs with huvle
  · have hp := routePos_pillar_or_depth d ((min u v : ℕ) : ℤ) h r (portWidth u v) hr
      (connectorIndex h r (portWidth u v) n hlen i)
    change _ ∨ _
    change ((routePos d ((min u v : ℕ) : ℤ) h r (portWidth u v) _ 0 = d ∧ _) ∨ _)
    rw [he] at hp
    simpa only [min_eq_left huvle, max_eq_right huvle] using hp
  · have hvule : v ≤ u := by omega
    have hp := routePos_pillar_or_depth d ((min u v : ℕ) : ℤ) h r (portWidth u v) hr
      (connectorIndex h r (portWidth u v) n hlen i.rev)
    change _ ∨ _
    change ((routePos d ((min u v : ℕ) : ℤ) h r (portWidth u v) _ 0 = d ∧ _) ∨ _)
    rw [he] at hp
    simpa only [min_eq_right hvule, max_eq_left hvule, or_comm] using hp

theorem portConnector_left_seam (d : ℤ) (u v h r n : ℕ)
    (hh : 0 < h) (hr : 0 < r) (huv : u ≠ v)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3)
    (i : Fin (4 * n)) (hi : i.val = 0) :
    cubicLattice.Adj (point d u (-1)) ((portConnector d u v h r n hh hr huv hlen).pos i) := by
  unfold portConnector
  split_ifs with huvle
  · have hs := rectangleConnector_left_seam d ((min u v : ℕ) : ℤ) h r (portWidth u v) n hh hr
      (portWidth_pos u v huv) hlen i hi
    rw [routePos_first_P d ((min u v : ℕ) : ℤ) h r (portWidth u v) hh] at hs
    simpa only [min_eq_left huvle] using hs
  · have hvule : v ≤ u := by omega
    have hir : i.rev.val + 1 = 4 * n := by simp only [Fin.val_rev, hi]; have := i.isLt; omega
    have hs := rectangleConnector_right_seam d ((min u v : ℕ) : ℤ) h r (portWidth u v) n hh hr
      (portWidth_pos u v huv) hlen i.rev hir
    have hend : (⟨4 * n + 2, by omega⟩ : Fin (routeSteps h r (portWidth u v) + 1)) =
        ⟨routeSteps h r (portWidth u v) - 1, by omega⟩ := by
      apply Fin.ext
      change 4 * n + 2 = routeSteps h r (portWidth u v) - 1
      omega
    rw [hend, routePos_last_P d ((min u v : ℕ) : ℤ) h r (portWidth u v) hh] at hs
    have he : ((min u v : ℕ) : ℤ) + portWidth u v = (u : ℤ) := by
      exact_mod_cast (by simpa only [max_eq_left hvule] using portWidth_endpoints u v)
    rw [he] at hs
    exact hs.symm

theorem portConnector_right_seam (d : ℤ) (u v h r n : ℕ)
    (hh : 0 < h) (hr : 0 < r) (huv : u ≠ v)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3)
    (i : Fin (4 * n)) (hi : i.val + 1 = 4 * n) :
    cubicLattice.Adj ((portConnector d u v h r n hh hr huv hlen).pos i) (point d v (-1)) := by
  unfold portConnector
  split_ifs with huvle
  · have hs := rectangleConnector_right_seam d ((min u v : ℕ) : ℤ) h r (portWidth u v) n hh hr
      (portWidth_pos u v huv) hlen i hi
    have hend : (⟨4 * n + 2, by omega⟩ : Fin (routeSteps h r (portWidth u v) + 1)) =
        ⟨routeSteps h r (portWidth u v) - 1, by omega⟩ := by
      apply Fin.ext
      change 4 * n + 2 = routeSteps h r (portWidth u v) - 1
      omega
    rw [hend, routePos_last_P d ((min u v : ℕ) : ℤ) h r (portWidth u v) hh] at hs
    have he : ((min u v : ℕ) : ℤ) + portWidth u v = (v : ℤ) := by
      exact_mod_cast (by simpa only [max_eq_right huvle] using portWidth_endpoints u v)
    rwa [he] at hs
  · have hvule : v ≤ u := by omega
    have hir : i.rev.val = 0 := by simp only [Fin.val_rev]; omega
    have hs := rectangleConnector_left_seam d ((min u v : ℕ) : ℤ) h r (portWidth u v) n hh hr
      (portWidth_pos u v huv) hlen i.rev hir
    rw [routePos_first_P d ((min u v : ℕ) : ℤ) h r (portWidth u v) hh] at hs
    simpa only [min_eq_right hvule] using hs.symm

theorem exists_ordinary_frame_radius (d k i u v : ℕ) (hk : k ≤ d) (hi : i < k)
    (hu : 1 ≤ u ∧ u ≤ d) (hv : 1 ≤ v ∧ v ≤ d)
    (hue : u % 2 = 1) (hve : v % 2 = 0) :
    ∃ r : ℕ, 0 < r ∧ routeSteps (5 + i) r (portWidth u v) = 4 * (d + 2) + 3 := by
  apply exists_radius_for_length
  · unfold routeSteps portWidth
    omega
  · unfold portWidth
    omega

/-- Port order and radius do not matter for disjointness: four distinct
terminal rows and distinct depths suffice for the complete inserted words. -/
theorem portConnectors_disjoint (d : ℤ) (u v s t h h' r r' n : ℕ)
    (hh : 0 < h) (hh' : 0 < h') (hr : 0 < r) (hr' : 0 < r')
    (huv : u ≠ v) (hst : s ≠ t) (hdepth : h ≠ h')
    (hus : u ≠ s) (hut : u ≠ t) (hvs : v ≠ s) (hvt : v ≠ t)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3)
    (hlen' : routeSteps h' r' (portWidth s t) = 4 * n + 3)
    (i j : Fin (4 * n)) :
    (portConnector d u v h r n hh hr huv hlen).pos i ≠
      (portConnector d s t h' r' n hh' hr' hst hlen').pos j := by
  intro he
  have hx := congrFun he 0
  have hy := congrFun he 1
  have hz := congrFun he 2
  have hp := portConnector_pillar_or_depth d u v h r n hh hr huv hlen i
  have hq := portConnector_pillar_or_depth d s t h' r' n hh' hr' hst hlen' j
  rcases hp with ⟨hp, hpu | hpv⟩ | ⟨hp, hpz⟩
  · rcases hq with ⟨hq, hqs | hqt⟩ | ⟨hq, hqz⟩
    · exact hus (by omega)
    · exact hut (by omega)
    · omega
  · rcases hq with ⟨hq, hqs | hqt⟩ | ⟨hq, hqz⟩
    · exact hvs (by omega)
    · exact hvt (by omega)
    · omega
  · rcases hq with ⟨hq, _⟩ | ⟨hq, hqz⟩ <;> omega

theorem initial_portConnectors_disjoint (d : ℤ) (Y first u v h r₀ r n : ℕ)
    (hdeep : 5 ≤ h) (hdepth : 5 ≠ h) (hr₀ : 0 < r₀) (hr : 0 < r)
    (hfirst : 0 < first) (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v)
    (hfu : first ≠ u) (hfv : first ≠ v)
    (hlen₀ : initialSteps 5 r₀ Y first = 4 * n + 3)
    (hlen : routeSteps h r (portWidth u v) = 4 * n + 3) (i j : Fin (4 * n)) :
    (initialConnector d 5 r₀ Y first n (by decide) hr₀ hfirst hlen₀).pos i ≠
      (portConnector d u v h r n (by omega) hr huv hlen).pos j := by
  have he : ((min u v : ℕ) : ℤ) + portWidth u v = ((max u v : ℕ) : ℤ) := by
    exact_mod_cast portWidth_endpoints u v
  have h0l : (0 : ℤ) ≠ ((min u v : ℕ) : ℤ) := by omega
  have h0r : (0 : ℤ) ≠ ((min u v : ℕ) : ℤ) + portWidth u v := by rw [he]; omega
  have hfl : (first : ℤ) ≠ ((min u v : ℕ) : ℤ) := by omega
  have hfr : (first : ℤ) ≠ ((min u v : ℕ) : ℤ) + portWidth u v := by rw [he]; omega
  have hsep := initialRoute_disjoint_rectangle d ((min u v : ℕ) : ℤ)
    5 h r₀ r Y first (portWidth u v) hr₀ hr hdeep hdepth h0l h0r hfl hfr
    (initialConnectorIndex 5 r₀ Y first n hlen₀ i)
  unfold portConnector
  split_ifs
  · exact hsep (connectorIndex h r (portWidth u v) n hlen j)
  · exact hsep (connectorIndex h r (portWidth u v) n hlen j.rev)

end ProteinFolding.CubicPackingRouting
