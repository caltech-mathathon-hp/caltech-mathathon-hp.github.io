import ProteinFolding.Tetrahedral.NearFieldFramePaths
import ProteinFolding.Tetrahedral.NearFieldFrameBounds

/-! All prescribed frame P-links are pairwise disjoint, uniformly in size. -/

namespace ProteinFolding.Tetrahedral

def nearFrameCoordinateLow (kind : Fin 6) (k : Fin 3) : ℤ :=
  if kind = 0 then if k = 0 then -1 else if k = 1 then 1 else -2
  else if kind = 1 then if k = 0 then -2 else if k = 1 then 1 else -2
  else if kind = 2 then if k = 0 then -2 else if k = 1 then -1 else -3
  else if kind = 3 then if k = 0 then 1 else if k = 1 then -1 else 1
  else if kind = 4 then if k = 0 then -6 else if k = 1 then 1 else -1
  else if k = 0 then -1 else if k = 1 then 1 else 1

def nearFrameCoordinateHigh (kind : Fin 6) (k : Fin 3) : ℤ :=
  if kind = 0 then if k = 0 then 2 else if k = 1 then 5 else 2
  else if kind = 1 then if k = 0 then 1 else if k = 1 then 5 else 2
  else if kind = 2 then if k = 0 then -1 else if k = 1 then 1 else -1
  else if kind = 3 then if k = 0 then 3 else if k = 1 then 1 else 2
  else if kind = 4 then if k = 0 then 2 else if k = 1 then 9 else 2
  else if k = 0 then 1 else if k = 1 then 3 else 2

theorem nearFrameOffset_coordinate_bounds (kind : Fin 6) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) (k : Fin 3) :
    nearFrameCoordinateLow kind k ≤ nearFrameOffset kind r.val k ∧
      nearFrameOffset kind r.val k ≤ nearFrameCoordinateHigh kind k := by
  revert kind r hr0 hrlast k
  decide

theorem nearFramePoint_coordinate_bounds (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (k : Fin 3) :
    nearFrameReference m q kind k + nearFrameCoordinateLow kind k ≤ (nearFramePoint m q kind hq r).val k ∧
      (nearFramePoint m q kind hq r).val k ≤ nearFrameReference m q kind k + nearFrameCoordinateHigh kind k := by
  have h := nearFrameOffset_coordinate_bounds kind r hr0 hrlast k
  change nearFrameReference m q kind k + nearFrameCoordinateLow kind k ≤
      nearFrameReference m q kind k + nearFrameOffset kind r.val k ∧
    nearFrameReference m q kind k + nearFrameOffset kind r.val k ≤
      nearFrameReference m q kind k + nearFrameCoordinateHigh kind k
  omega

def NearFrameRoutesSeparated (kind : Fin 6) (q : ℕ) (kind' : Fin 6) (q' : ℕ) : Prop :=
  kind ≠ kind' ∨
    (kind = 1 ∧ kind' = 1 ∧ (q + 6 ≤ q' ∨ q' + 6 ≤ q)) ∨
    (kind = 4 ∧ kind' = 4 ∧ (q + 10 ≤ q' ∨ q' + 10 ≤ q))

theorem nearFramePoints_ne_of_routes_separated (m q q' : ℕ) (kind kind' : Fin 6)
    (hq : q % 2 = 1) (hq' : q' % 2 = 1) (hqlo : 5 ≤ q) (hqlo' : 5 ≤ q')
    (hqhi : (q : ℤ) + 10 ≤ octRadius m) (hqhi' : (q' : ℤ) + 10 ≤ octRadius m)
    (hsep : NearFrameRoutesSeparated kind q kind' q')
    (r : Fin (nearFrameLength kind)) (s : Fin (nearFrameLength kind'))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (hs0 : 0 < s.val) (hslast : s.val + 1 < nearFrameLength kind') :
    nearFramePoint m q kind hq r ≠ nearFramePoint m q' kind' hq' s := by
  intro heq
  obtain ⟨hxl, hxu⟩ := nearFramePoint_coordinate_bounds m q kind hq r hr0 hrlast 0
  obtain ⟨hyl, hyu⟩ := nearFramePoint_coordinate_bounds m q kind hq r hr0 hrlast 1
  obtain ⟨hzl, hzu⟩ := nearFramePoint_coordinate_bounds m q kind hq r hr0 hrlast 2
  obtain ⟨hxl', hxu'⟩ := nearFramePoint_coordinate_bounds m q' kind' hq' s hs0 hslast 0
  obtain ⟨hyl', hyu'⟩ := nearFramePoint_coordinate_bounds m q' kind' hq' s hs0 hslast 1
  obtain ⟨hzl', hzu'⟩ := nearFramePoint_coordinate_bounds m q' kind' hq' s hs0 hslast 2
  rw [heq] at hxl hxu hyl hyu hzl hzu
  fin_cases kind <;> fin_cases kind'
  all_goals simp [NearFrameRoutesSeparated] at hsep
  all_goals dsimp [nearFrameReference, nearFrameCoordinateLow, nearFrameCoordinateHigh, octRadius]
    at hxl hxu hyl hyu hzl hzu hxl' hxu' hyl' hyu' hzl' hzu' hqhi hqhi'
  all_goals omega

theorem nearFramePLists_disjoint (m q q' : ℕ) (kind kind' : Fin 6)
    (hq : q % 2 = 1) (hq' : q' % 2 = 1) (hqlo : 5 ≤ q) (hqlo' : 5 ≤ q')
    (hqhi : (q : ℤ) + 10 ≤ octRadius m) (hqhi' : (q' : ℤ) + 10 ≤ octRadius m)
    (hsep : NearFrameRoutesSeparated kind q kind' q') :
    List.Disjoint (nearFramePList m q kind hq) (nearFramePList m q' kind' hq') := by
  apply List.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨r, hr⟩ := List.mem_ofFn.mp hp
  obtain ⟨s, hs⟩ := List.mem_ofFn.mp hp'
  exact nearFramePoints_ne_of_routes_separated m q q' kind kind' hq hq' hqlo hqlo' hqhi hqhi' hsep
    ⟨r.val + 1, by have h := r.isLt; omega⟩ ⟨s.val + 1, by have h := s.isLt; omega⟩
    (by change 0 < r.val + 1; omega)
    (by change r.val + 1 + 1 < nearFrameLength kind; have h := r.isLt; omega)
    (by change 0 < s.val + 1; omega)
    (by change s.val + 1 + 1 < nearFrameLength kind'; have h := s.isLt; omega) (hr.trans hs.symm)

theorem nearFramePList_mem_skin_one (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) {p : Site}
    (hp : p ∈ nearFramePList m q kind hq) : p ∈ skin m 1 := by
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hp
  exact nearFramePoint_mem_skin_one m q kind hq hqlo hqhi
    ⟨r.val + 1, by have h := r.isLt; omega⟩
    (by change 0 < r.val + 1; omega)
    (by change r.val + 1 + 1 < nearFrameLength kind; have h := r.isLt; omega)

theorem nearFramePList_outside (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1) {p : Site}
    (hp : p ∈ nearFramePList m q kind hq) : p ∉ octahedron m := by
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hp
  exact nearFramePoint_outside m q kind hq
    ⟨r.val + 1, by have h := r.isLt; omega⟩
    (by change 0 < r.val + 1; omega)
    (by change r.val + 1 + 1 < nearFrameLength kind; have h := r.isLt; omega)

theorem nearFrame_two_slots_separated {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hne : k ≠ l) :
    NearFrameRoutesSeparated 1 (6 * k - 1) 1 (6 * l - 1) := by
  apply Or.inr
  apply Or.inl
  exact ⟨rfl, rfl, by omega⟩

theorem nearFrame_six_slots_separated {k l : ℕ} (hne : k ≠ l) :
    NearFrameRoutesSeparated 4 (10 * k + 5) 4 (10 * l + 5) := by
  apply Or.inr
  apply Or.inr
  exact ⟨rfl, rfl, by omega⟩

end ProteinFolding.Tetrahedral
