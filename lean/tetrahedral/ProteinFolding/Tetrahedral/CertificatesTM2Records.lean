import ProteinFolding.Tetrahedral.CertificatesTM2Bridge
import ProteinFolding.Tetrahedral.CertificatesTM2Row

/-! Incoming-direction records and the exact relative displacement between
original residue checkpoints. No artificial unit-step vertex is treated as
a residue of the protein. -/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Records

open CertificatesTM2Directions CertificatesTM2Expansion CertificatesTM2Bridge
open ProteinFolding.TM2WalkCounters

abbrev Record := Residue × Fin 4

def recordsOfDirections (S : Sequence) (ds : DirectionWord) : List Record :=
  List.ofFn fun i : Fin S.length =>
    (S.get i, if i.val = 0 then 0 else ds[i.val - 1]?.getD 0)

theorem recordsOfDirections_length (S : Sequence) (ds : DirectionWord) :
    (recordsOfDirections S ds).length = S.length := by simp [recordsOfDirections]

theorem recordsOfDirections_labels (S : Sequence) (ds : DirectionWord) :
    (recordsOfDirections S ds).map Prod.fst = S := by
  simp [recordsOfDirections, List.map_ofFn, Function.comp_def]

theorem recordsOfDirections_incoming (S : Sequence) (ds : DirectionWord) (k : ℕ)
    (hk : k + 1 < S.length) :
    (((recordsOfDirections S ds)[k + 1]?).map Prod.snd).getD 0 = ds[k]?.getD 0 := by
  simp [recordsOfDirections, hk]

def recordPosition (rs : List Record) : ℕ → Site
  | 0 => origin
  | k + 1 => step (recordPosition rs k) (((rs[k + 1]?).map Prod.snd).getD 0)

def incomingDirections (rs : List Record) : DirectionWord := (rs.drop 1).map Prod.snd

theorem recordPosition_incoming (rs : List Record) (n : ℕ) :
    recordPosition rs n = walkPosition (incomingDirections rs) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [recordPosition, walkPosition, ih]
    congr 1
    simp [incomingDirections]

theorem recordPosition_eq_walk (S : Sequence) (ds : DirectionWord) (k : ℕ)
    (hk : k < S.length) :
    recordPosition (recordsOfDirections S ds) k = walkPosition ds k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [recordPosition, walkPosition, ih (by omega), recordsOfDirections_incoming S ds k hk]

def suffixDirections (rs : List Record) (i j : ℕ) : DirectionWord :=
  (((rs.drop (i + 1)).take (j - i)).map Prod.snd)

def suffixExpanded (rs : List Record) (i j : ℕ) : List (Fin 6) :=
  expandFrom (decide (i % 2 = 0)) (suffixDirections rs i j)

theorem prefix_expansion_displacement (rs : List Record) (n : ℕ)
    (hn : n ≤ (incomingDirections rs).length) (k : Fin 3) :
    displacement (expandFrom true ((incomingDirections rs).take n)) k =
      (recordPosition rs n).val k := by
  rw [← expandedPrefix_eq_expand_take _ n hn, expandedPrefix_displacement,
    ← recordPosition_incoming]

theorem suffix_counter_coordinate (rs : List Record) (i j : ℕ) (hij : i ≤ j)
    (hj : j < rs.length) (k : Fin 3) :
    coordinate (runCounts (fun _ => 0) (suffixExpanded rs i j)) k =
      (recordPosition rs j).val k - (recordPosition rs i).val k := by
  have hj' : j ≤ (incomingDirections rs).length := by
    simp only [incomingDirections, List.length_map, List.length_drop]
    omega
  have hi' : i ≤ (incomingDirections rs).length := by omega
  have hsplit : (incomingDirections rs).take j =
      (incomingDirections rs).take i ++ suffixDirections rs i j := by
    rw [show j = i + (j - i) by omega, List.take_add]
    simp [incomingDirections, suffixDirections, ← List.map_take, ← List.map_drop]
  have hexpand : expandFrom true ((incomingDirections rs).take j) =
      expandFrom true ((incomingDirections rs).take i) ++ suffixExpanded rs i j := by
    rw [hsplit, expandFrom_append, endColour_true, List.length_take, Nat.min_eq_left hi']
    rfl
  have hd := congrArg (fun ds => displacement ds k) hexpand
  dsimp only at hd
  rw [displacement_append, prefix_expansion_displacement rs i hi' k,
    prefix_expansion_displacement rs j hj' k] at hd
  rw [runCounts_zero_coordinate]
  omega

theorem inspected_suffix_zero_iff (rs : List Record) (i j : ℕ) (hij : i ≤ j)
    (hj : j < rs.length) :
    CertificatesTM2Inspector.cap (totalCounts (runCounts (fun _ => 0) (suffixExpanded rs i j))) = 0 ↔
      recordPosition rs i = recordPosition rs j := by
  apply cap_zero_iff_collision
  · exact runCounts_reduced _ zero_reduced _
  · exact suffix_counter_coordinate rs i j hij hj

theorem inspected_suffix_three_iff (rs : List Record) (i j : ℕ) (hij : i ≤ j)
    (hj : j < rs.length) :
    CertificatesTM2Inspector.cap (totalCounts (runCounts (fun _ => 0) (suffixExpanded rs i j))) = 3 ↔
      tetrahedralLattice.Adj (recordPosition rs i) (recordPosition rs j) := by
  apply cap_three_iff_adj
  · exact runCounts_reduced _ zero_reduced _
  · exact suffix_counter_coordinate rs i j hij hj

theorem rowDirections_eq_expansion (a : Bool) (rs : List Record) :
    CertificatesTM2Row.rowDirections a (rs.map some) = expandFrom a (rs.map Prod.snd) := by
  induction rs generalizing a with
  | nil => rfl
  | cons r rs ih =>
    simp [CertificatesTM2Row.rowDirections, expandFrom, CertificatesTM2Row.direction, ih]

end ProteinFolding.Tetrahedral.CertificatesTM2Records
