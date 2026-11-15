import ProteinFolding.Tetrahedral.CertificatesTM2Expansion
import ProteinFolding.Tetrahedral.CertificatesTM2Geometry
import ProteinFolding.Tetrahedral.CertificatesTM2Inspector

/-! The semantic bridge from actual expansion/counter/inspection stages to
the frozen direction walk and diamond adjacency predicates. -/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Bridge

open CertificatesTM2Directions CertificatesTM2Expansion
open ProteinFolding.TM2WalkCounters

theorem expandFrom_append (a : Bool) (u v : List (Fin 4)) :
    expandFrom a (u ++ v) = expandFrom a u ++ expandFrom (endColour a u) v := by
  induction u generalizing a with
  | nil => rfl
  | cons d u ih => simp [expandFrom, endColour, ih, List.append_assoc]

theorem endColour_length (a : Bool) (u : List (Fin 4)) :
    endColour a u = if u.length % 2 = 0 then a else !a := by
  induction u generalizing a with
  | nil => simp [endColour]
  | cons d u ih =>
    simp only [endColour, ih, List.length_cons]
    by_cases h : u.length % 2 = 0
    · have h' : ¬ (u.length + 1) % 2 = 0 := by omega
      simp [h, h']
    · have h' : (u.length + 1) % 2 = 0 := by omega
      simp [h, h']

theorem endColour_true (u : List (Fin 4)) :
    endColour true u = decide (u.length % 2 = 0) := by
  rw [endColour_length]
  by_cases h : u.length % 2 = 0 <;> simp [h]

theorem expandedPrefix_eq_expand_take (ds : DirectionWord) (n : ℕ) : n ≤ ds.length →
    expandedPrefix ds n = expandFrom true (ds.take n) := by
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hlt : n < ds.length := by omega
    rw [expandedPrefix, ih (by omega), List.take_succ_eq_append_getElem hlt,
      expandFrom_append]
    rw [endColour_true, List.length_take, Nat.min_eq_left (by omega)]
    simp only [expandFrom, List.append_nil, List.getElem?_eq_getElem hlt, Option.getD_some]

theorem expandedPrefix_all (ds : DirectionWord) :
    expandedPrefix ds ds.length = expandFrom true ds := by
  simpa only [List.take_length] using expandedPrefix_eq_expand_take ds ds.length le_rfl

theorem expanded_counters_coordinate (ds : DirectionWord) (k : Fin 3) :
    coordinate (runCounts (fun _ => 0) (expandFrom true ds)) k =
      (walkPosition ds ds.length).val k := by
  rw [← expandedPrefix_all, counters_coordinate]

theorem cap_three_iff_adj (p q : Site) (c : Counts) (hc : Reduced c)
    (hcoord : ∀ k, coordinate c k = q.val k - p.val k) :
    CertificatesTM2Inspector.cap (totalCounts c) = 3 ↔ tetrahedralLattice.Adj p q := by
  rw [CertificatesTM2Inspector.cap_eq_three, totalCounts_eq_manhattan c hc,
    hcoord 0, hcoord 1, hcoord 2]
  exact (CertificatesTM2Geometry.adj_iff_manhattan_three p q).symm

theorem cap_zero_iff_collision (p q : Site) (c : Counts) (hc : Reduced c)
    (hcoord : ∀ k, coordinate c k = q.val k - p.val k) :
    CertificatesTM2Inspector.cap (totalCounts c) = 0 ↔ p = q := by
  rw [CertificatesTM2Inspector.cap_eq_zero, totalCounts_eq_manhattan c hc,
    hcoord 0, hcoord 1, hcoord 2]
  exact CertificatesTM2Geometry.manhattan_eq_zero_iff p q

end ProteinFolding.Tetrahedral.CertificatesTM2Bridge
