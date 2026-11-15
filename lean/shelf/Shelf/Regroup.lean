import Shelf.LayoutTokens
import Shelf.WordAnatomy

/-!
# The string, read token by token

`P D(r) P = (PHP)^r`. Moving one `P` from each side of a dense run into the run
turns the string of Section 3 into the form in which the fold is written down.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue Layout

namespace Regroup

/-- `P D(r) P = (PHP)^r` for `r > 0`, with the rest of the string after it. -/
theorem P_denseRun_P_append {r : ℕ} (hr : 0 < r) (w : Sequence) :
    P :: (denseRun r ++ (P :: w)) = tokWord r ++ w := by
  have h := P_denseRun_P hr
  rw [tokWord, ← h]; simp

/-- `P^(c+2) = P P^c P`, with the rest of the string after it. -/
theorem replicate_add_two_append (c : ℕ) (w : Sequence) :
    List.replicate (c + 2) P ++ w = P :: (List.replicate c P ++ (P :: w)) := by
  rw [List.replicate_succ, List.replicate_succ']; simp

theorem flatMap_const_range (m : ℕ) (w : Sequence) :
    ((List.range m).flatMap fun _ => w) = (List.replicate m w).flatten := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ',
      List.flatten_append]; simp

/-- The inner tethers and separators after the first separator, with one `P` taken from
the block after them. -/
theorem bins_regroup (B m : ℕ) (w : Sequence) :
    (List.replicate m (List.replicate (B + 6) P ++ [H])).flatten ++ (P :: w) =
      P :: ((List.replicate m (List.replicate (B + 4) P ++ tokWord 1)).flatten ++ w) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ (n := m), List.flatten_cons, List.append_assoc, ih,
      List.replicate_succ (n := m), List.flatten_cons, List.append_assoc,
      show B + 6 = (B + 4) + 2 from rfl, replicate_add_two_append (B + 4)]
    simp [tokWord]

theorem separators_regroup (J : Packing.Instance) (w : Sequence) :
    P :: (separators J ++ (P :: w)) =
      (tokWord 1 ++ (List.range J.bins).flatMap fun _ =>
        List.replicate (J.capacity + 4) P ++ tokWord 1) ++ w := by
  rw [separators, List.cons_append, bins_regroup, flatMap_const_range]
  simp [tokWord]

theorem items_regroup (c : ℕ) (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) :
    (l.map fun a => List.replicate (c + 2) P ++ denseRun a).flatten ++ [P] =
      P :: (l.flatMap fun a => List.replicate c P ++ tokWord a) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.flatten_cons, List.append_assoc, List.append_assoc,
      ih (fun b hb => hl b (by simp [hb])), replicate_add_two_append, List.flatMap_cons,
      P_denseRun_P_append (hl a (by simp)), List.append_assoc]

theorem finRange_flatMap_get {α β : Type*} (l : List α) (f : α → List β) :
    ((List.finRange l.length).flatMap fun i => f (l.get i)) = l.flatMap f := by
  simp only [List.flatMap]
  congr 1
  conv_rhs => rw [← List.finRange_map_get l]
  rw [List.map_map]
  rfl

end Regroup

open Regroup in
/-- The string of Section 3 equals the string read token by token: every dense run
takes one `P` from the block before it and one from the block after it. -/
theorem shelfWord_eq_layoutWord {J : Packing.Instance} (hJ : Normalised J) :
    shelfWord J = layoutWord J := by
  have hn := three_le_side J
  have hL := linker_ge J
  obtain ⟨c, hc⟩ : ∃ c, linkerLength J = c + 2 := ⟨linkerLength J - 2, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, side J = t + 2 := ⟨side J - 2, by omega⟩
  have hA : 0 < 9 * side J - 10 := by omega
  have hF : 0 < side J - 2 := by omega
  rw [shelfWord_eq, layoutWord, itemsWord, hc, items_regroup c _ hJ.size_pos,
    show c + 2 - 2 = c by omega,
    finRange_flatMap_get J.sizes (fun a => List.replicate c P ++ tokWord a)]
  rw [ht] at hA hF ⊢
  rw [show t + 2 - 2 = t by omega] at hF ⊢
  rw [replicate_add_two_append c, replicate_add_two_append t, replicate_add_two_append t]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  rw [P_denseRun_P_append hF, P_denseRun_P_append hF, separators_regroup,
    P_denseRun_P_append hA]
  simp only [List.append_assoc]

end ProteinFolding.Shelf
