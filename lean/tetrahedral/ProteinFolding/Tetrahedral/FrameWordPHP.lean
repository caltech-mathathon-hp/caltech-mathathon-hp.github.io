import ProteinFolding.Tetrahedral.FrameWord
import ProteinFolding.Tetrahedral.FoldRigidity

/-! Pure word counting for the PHP monomers used by the soundness proof. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

def IsPHPStart (S : Sequence) (i : ℕ) : Prop :=
  S[i]? = some .P ∧ S[i + 1]? = some .H ∧ S[i + 2]? = some .P

instance (S : Sequence) (i : ℕ) : Decidable (IsPHPStart S i) := by
  unfold IsPHPStart
  infer_instance

def phpStartIndices (S : Sequence) : Finset ℕ :=
  (Finset.range S.length).filter (IsPHPStart S)

def phpStartCount (S : Sequence) : ℕ :=
  ∑ i ∈ Finset.range S.length, if IsPHPStart S i then 1 else 0

theorem phpStartIndices_card (S : Sequence) : (phpStartIndices S).card = phpStartCount S := by
  simp only [phpStartIndices, phpStartCount, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem phpIndices_card_eq_startCount (S : Sequence) :
    (phpIndices S).card = phpStartCount S := by
  rw [← phpStartIndices_card]
  apply Finset.card_bij (fun i _ => i.val - 1)
  · intro i hi
    obtain ⟨hH, l, r, hli, hir, hl, hr⟩ := (Finset.mem_filter.mp hi).2
    have hlval : i.val - 1 = l.val := by omega
    have hival : i.val - 1 + 1 = i.val := by omega
    have hrval : i.val - 1 + 2 = r.val := by omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    unfold IsPHPStart
    rw [hlval, show l.val + 1 = i.val from hli, show l.val + 2 = r.val by omega]
    exact ⟨List.getElem?_eq_some_iff.mpr ⟨l.isLt, hl⟩,
      List.getElem?_eq_some_iff.mpr ⟨i.isLt, hH⟩,
      List.getElem?_eq_some_iff.mpr ⟨r.isLt, hr⟩⟩
  · intro i hi j hj heq
    obtain ⟨_, l, _, hli, _, _, _⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨_, l', _, hlj, _, _, _⟩ := (Finset.mem_filter.mp hj).2
    apply Fin.ext
    omega
  · intro i hi
    have hs := (Finset.mem_filter.mp hi).2
    obtain ⟨hl, hH, hr⟩ := hs
    obtain ⟨hlbound, hl⟩ := List.getElem?_eq_some_iff.mp hl
    obtain ⟨hibound, hH⟩ := List.getElem?_eq_some_iff.mp hH
    obtain ⟨hrbound, hr⟩ := List.getElem?_eq_some_iff.mp hr
    refine ⟨⟨i + 1, hibound⟩, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hH, ⟨i, hlbound⟩, ⟨i + 2, hrbound⟩, ?_, ?_, hl, hr⟩ <;> rfl

theorem phpStartCount_cons (a : Residue) (S : Sequence) :
    phpStartCount (a :: S) =
      (if a = .P ∧ S[0]? = some .H ∧ S[1]? = some .P then 1 else 0) + phpStartCount S := by
  unfold phpStartCount
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [IsPHPStart, List.getElem?_cons_zero, List.getElem?_cons_succ]
  simp only [Option.some.injEq, Nat.add_comm]

@[simp] theorem phpStartCount_nil : phpStartCount [] = 0 := by
  simp [phpStartCount]

@[simp] theorem phpStartCount_H_cons (S : Sequence) :
    phpStartCount (.H :: S) = phpStartCount S := by
  rw [phpStartCount_cons]
  simp

@[simp] theorem phpStartCount_PP_cons (S : Sequence) :
    phpStartCount (.P :: .P :: S) = phpStartCount (.P :: S) := by
  rw [phpStartCount_cons]
  simp

theorem phpStartCount_replicate_H (n : ℕ) (S : Sequence) :
    phpStartCount (List.replicate n .H ++ S) = phpStartCount S := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [List.replicate_succ, List.cons_append, phpStartCount_H_cons] using ih

theorem phpStartCount_replicate_P (n : ℕ) (S : Sequence) :
    phpStartCount (List.replicate (n + 1) .P ++ S) = phpStartCount (.P :: S) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append, phpStartCount_PP_cons] using ih

theorem phpStartCount_long_run_prefix (k n : ℕ) (hk : 0 < k) (hn : 2 ≤ n)
    (S : Sequence) :
    phpStartCount (List.replicate k .P ++ List.replicate n .H ++ S) = phpStartCount S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨n, rfl⟩ : ∃ a, n = a + 2 := ⟨n - 2, by omega⟩
  rw [List.append_assoc, phpStartCount_replicate_P]
  rw [List.replicate_succ, List.cons_append, phpStartCount_cons]
  simp [List.replicate_succ, phpStartCount_replicate_H]

@[simp] theorem phpStartCount_singleton (a : Residue) : phpStartCount [a] = 0 := by
  simp [phpStartCount_cons]

theorem phpStartCount_PP_split (u v : Sequence) :
    phpStartCount (u ++ .P :: .P :: v) =
      phpStartCount (u ++ [.P]) + phpStartCount (.P :: v) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have hpred : (a = .P ∧ (u ++ .P :: .P :: v)[0]? = some .H ∧
        (u ++ .P :: .P :: v)[1]? = some .P) ↔
        (a = .P ∧ (u ++ [.P])[0]? = some .H ∧ (u ++ [.P])[1]? = some .P) := by
      cases u with
      | nil => simp
      | cons b tail => cases tail <;> simp
    simp only [List.cons_append]
    rw [phpStartCount_cons, phpStartCount_cons]
    simp only [hpred]
    omega

def capWord (u : Sequence) : Sequence := .P :: (u ++ [.P])

theorem phpStartCount_capped_append_P (u v : Sequence) :
    phpStartCount (capWord u ++ .P :: v) =
      phpStartCount (capWord u) + phpStartCount (.P :: v) := by
  simpa only [capWord, List.cons_append, List.append_assoc, List.singleton_append] using
    phpStartCount_PP_split (.P :: u) v

theorem phpStartCount_capped_long_H (n : ℕ) (hn : 2 ≤ n) :
    phpStartCount (capWord (List.replicate n .H)) = 0 := by
  have h := phpStartCount_long_run_prefix 1 n (by decide) hn [.P]
  simpa only [capWord, List.replicate_one, List.singleton_append, phpStartCount_singleton] using h

@[simp] theorem phpStartCount_capped_single_H : phpStartCount (capWord [.H]) = 1 := by
  simp [capWord, phpStartCount_cons]

theorem phpStartCount_repeat_long_run_prefix (k n t : ℕ) (hk : 0 < k) (hn : 2 ≤ n)
    (S : Sequence) :
    phpStartCount (repeatWord (List.replicate k .P ++ List.replicate n .H) t ++ S) =
      phpStartCount S := by
  induction t with
  | zero => simp [repeatWord]
  | succ t ih =>
    rw [repeatWord, List.append_assoc,
      phpStartCount_long_run_prefix k n hk hn]
    exact ih

@[simp] theorem phpStartCount_PHP_cons (S : Sequence) :
    phpStartCount (.P :: .H :: .P :: S) = 1 + phpStartCount (.P :: S) := by
  rw [phpStartCount_cons]
  simp

@[simp] theorem phpStartCount_PHH_cons (S : Sequence) :
    phpStartCount (.P :: .H :: .H :: S) = phpStartCount S := by
  rw [phpStartCount_cons]
  simp

theorem phpStartCount_dimer_prefix (q : ℕ) (S : Sequence) :
    phpStartCount (.P :: (dimerChain (q + 1) ++ S)) = phpStartCount S := by
  induction q with
  | zero => simp [dimerChain, repeatWord]
  | succ q ih =>
    simpa only [dimerChain, repeatWord, List.append_assoc, List.cons_append,
      List.nil_append, phpStartCount_PHH_cons, phpStartCount_PP_cons] using ih

@[simp] theorem phpStartCount_capped_dimer (q : ℕ) :
    phpStartCount (capWord (dimerChain q)) = 0 := by
  cases q with
  | zero => simp [capWord, dimerChain]
  | succ q =>
    simpa only [capWord, phpStartCount_singleton] using phpStartCount_dimer_prefix q [.P]

end ProteinFolding.Tetrahedral
