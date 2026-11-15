import ProteinFolding.Tetrahedral.ReductionWordCounts

/-! Counting actual maximal HH runs by their literal P-H-H-P occurrences. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

def IsDimerStart (S : Sequence) (i : ℕ) : Prop :=
  S[i]? = some .P ∧ S[i + 1]? = some .H ∧ S[i + 2]? = some .H ∧ S[i + 3]? = some .P

instance (S : Sequence) (i : ℕ) : Decidable (IsDimerStart S i) := by
  unfold IsDimerStart
  infer_instance

def dimerStartIndices (S : Sequence) : Finset ℕ :=
  (Finset.range S.length).filter (IsDimerStart S)

def dimerStartCount (S : Sequence) : ℕ :=
  ∑ i ∈ Finset.range S.length, if IsDimerStart S i then 1 else 0

theorem dimerStartIndices_card (S : Sequence) :
    (dimerStartIndices S).card = dimerStartCount S := by
  simp only [dimerStartIndices, dimerStartCount, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem dimerStartCount_cons (a : Residue) (S : Sequence) :
    dimerStartCount (a :: S) =
      (if a = .P ∧ S[0]? = some .H ∧ S[1]? = some .H ∧ S[2]? = some .P then 1 else 0) +
        dimerStartCount S := by
  unfold dimerStartCount
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [IsDimerStart, List.getElem?_cons_zero, List.getElem?_cons_succ]
  simp only [Option.some.injEq, Nat.add_comm]

@[simp] theorem dimerStartCount_nil : dimerStartCount [] = 0 := by simp [dimerStartCount]

@[simp] theorem dimerStartCount_singleton (a : Residue) : dimerStartCount [a] = 0 := by
  simp [dimerStartCount_cons]

@[simp] theorem dimerStartCount_H_cons (S : Sequence) : dimerStartCount (.H :: S) = dimerStartCount S := by
  rw [dimerStartCount_cons]
  simp

@[simp] theorem dimerStartCount_PP_cons (S : Sequence) :
    dimerStartCount (.P :: .P :: S) = dimerStartCount (.P :: S) := by
  rw [dimerStartCount_cons]
  simp

@[simp] theorem dimerStartCount_PHP_cons (S : Sequence) :
    dimerStartCount (.P :: .H :: .P :: S) = dimerStartCount (.P :: S) := by
  rw [dimerStartCount_cons]
  simp

@[simp] theorem dimerStartCount_PHHH_cons (S : Sequence) :
    dimerStartCount (.P :: .H :: .H :: .H :: S) = dimerStartCount S := by
  rw [dimerStartCount_cons]
  simp

@[simp] theorem dimerStartCount_PHHP_cons (S : Sequence) :
    dimerStartCount (.P :: .H :: .H :: .P :: S) = 1 + dimerStartCount (.P :: S) := by
  rw [dimerStartCount_cons]
  simp

theorem dimerStartCount_replicate_H (n : ℕ) (S : Sequence) :
    dimerStartCount (List.replicate n .H ++ S) = dimerStartCount S := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [List.replicate_succ, List.cons_append, dimerStartCount_H_cons] using ih

theorem dimerStartCount_replicate_P (n : ℕ) (S : Sequence) :
    dimerStartCount (List.replicate (n + 1) .P ++ S) = dimerStartCount (.P :: S) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append, dimerStartCount_PP_cons] using ih

theorem dimerStartCount_P_prefix (n : ℕ) (S : Sequence) :
    dimerStartCount (List.replicate n .P ++ .P :: S) = dimerStartCount (.P :: S) := by
  cases n with
  | zero => rfl
  | succ n => exact (dimerStartCount_replicate_P n (.P :: S)).trans (dimerStartCount_PP_cons S)

theorem dimerStartCount_long_run_prefix (k n : ℕ) (hk : 0 < k) (hn : 3 ≤ n) (S : Sequence) :
    dimerStartCount (List.replicate k .P ++ (List.replicate n .H ++ S)) = dimerStartCount S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨n, rfl⟩ : ∃ a, n = a + 3 := ⟨n - 3, by omega⟩
  rw [dimerStartCount_replicate_P]
  simp [List.replicate_succ, dimerStartCount_replicate_H]

theorem dimerStartCount_repeat_long_run_prefix (k n t : ℕ) (hk : 0 < k) (hn : 3 ≤ n)
    (S : Sequence) :
    dimerStartCount (repeatWord (List.replicate k .P ++ List.replicate n .H) t ++ S) = dimerStartCount S := by
  induction t with
  | zero => simp [repeatWord]
  | succ t ih =>
    rw [repeatWord, List.append_assoc, List.append_assoc, dimerStartCount_long_run_prefix k n hk hn]
    exact ih

theorem dimerStartCount_between_P_runs (k j : ℕ) (hk : 0 < k) (hj : 0 < j) (S : Sequence) :
    dimerStartCount (List.replicate k .P ++ .H :: (List.replicate j .P ++ S)) =
      dimerStartCount (List.replicate j .P ++ S) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [dimerStartCount_replicate_P]
  simp only [List.replicate_succ, List.cons_append, dimerStartCount_PHP_cons]

theorem dimerStartCount_dimer_prefix (q : ℕ) (S : Sequence) :
    dimerStartCount (.P :: (dimerChain (q + 1) ++ .P :: S)) =
      (q + 1) + dimerStartCount (.P :: S) := by
  induction q with
  | zero => simp [dimerChain, repeatWord]
  | succ q ih =>
    have h := congrArg (fun n : ℕ => 1 + n) ih
    simpa only [dimerChain, repeatWord, List.append_assoc, List.cons_append,
      List.nil_append, dimerStartCount_PHHP_cons, dimerStartCount_PP_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem dimerStartCount_dimer_Ptail (k q j : ℕ) (hk : 0 < k) (hj : 0 < j) (S : Sequence) :
    dimerStartCount (List.replicate k .P ++ (dimerChain (q + 1) ++ (List.replicate j .P ++ S))) =
      (q + 1) + dimerStartCount (List.replicate j .P ++ S) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [dimerStartCount_replicate_P]
  simpa only [List.replicate_succ, List.cons_append] using
    dimerStartCount_dimer_prefix q (List.replicate j .P ++ S)

@[simp] theorem dimerStartCount_capped_dimer (q : ℕ) :
    dimerStartCount (capWord (dimerChain q)) = q := by
  cases q with
  | zero => simp [capWord, dimerChain]
  | succ q =>
    simpa only [capWord, dimerStartCount_singleton, Nat.add_zero] using dimerStartCount_dimer_prefix q []

@[simp] theorem dimerStartCount_capped_single_H : dimerStartCount (capWord [.H]) = 0 := by
  simp [capWord, dimerStartCount_cons]

theorem dimerStartCount_capped_long_H (n : ℕ) (hn : 3 ≤ n) :
    dimerStartCount (capWord (List.replicate n .H)) = 0 := by
  simpa only [List.replicate_one, List.singleton_append, capWord, dimerStartCount_singleton] using
    dimerStartCount_long_run_prefix 1 n (by decide) hn [.P]

theorem dimerStartCount_PP_split (u v : Sequence) :
    dimerStartCount (u ++ .P :: .P :: v) =
      dimerStartCount (u ++ [.P]) + dimerStartCount (.P :: v) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have hpred :
        (a = .P ∧ (u ++ .P :: .P :: v)[0]? = some .H ∧ (u ++ .P :: .P :: v)[1]? = some .H ∧
          (u ++ .P :: .P :: v)[2]? = some .P) ↔
        (a = .P ∧ (u ++ [.P])[0]? = some .H ∧ (u ++ [.P])[1]? = some .H ∧ (u ++ [.P])[2]? = some .P) := by
      cases u with
      | nil => simp
      | cons b tail =>
        cases tail with
        | nil => simp
        | cons c tail => cases tail <;> simp
    simp only [List.cons_append]
    rw [dimerStartCount_cons, dimerStartCount_cons]
    simp only [hpred]
    omega

theorem dimerStartCount_capped_append_P (u v : Sequence) :
    dimerStartCount (capWord u ++ .P :: v) = dimerStartCount (capWord u) + dimerStartCount (.P :: v) := by
  simpa only [capWord, List.cons_append, List.append_assoc, List.singleton_append] using
    dimerStartCount_PP_split (.P :: u) v

theorem dimerStartCount_P_prefix_cap (n : ℕ) (u v : Sequence) :
    dimerStartCount (List.replicate n .P ++ capWord u ++ v) = dimerStartCount (capWord u ++ v) := by
  rw [List.append_assoc]
  change dimerStartCount (List.replicate n .P ++ .P :: ((u ++ [.P]) ++ v)) =
    dimerStartCount (.P :: ((u ++ [.P]) ++ v))
  exact dimerStartCount_P_prefix n _

theorem dimerStartCount_assembleCappedBodies (gaps : ℕ → ℕ) (i : ℕ) (us : List Sequence) :
    dimerStartCount (assembleCappedBodies gaps i us) = (us.map (fun u => dimerStartCount (capWord u))).sum := by
  induction us generalizing i with
  | nil => simp [assembleCappedBodies]
  | cons u us ih =>
    rw [assembleCappedBodies, dimerStartCount_P_prefix_cap]
    cases us with
    | nil => simp [assembleCappedBodies]
    | cons v vs =>
      obtain ⟨tail, htail⟩ := assembleCappedBodies_starts_P gaps (i + 1) v vs
      rw [htail, dimerStartCount_capped_append_P, ← htail, ih]
      rfl

theorem dimerStartCount_assembleReductionWord (gaps : ℕ → ℕ) (us : List Sequence) :
    dimerStartCount (assembleReductionWord gaps us) = (us.map (fun u => dimerStartCount (capWord u))).sum := by
  unfold assembleReductionWord
  cases us with
  | nil => simp [assembleCappedBodies, dimerStartCount_cons]
  | cons u us =>
    obtain ⟨tail, htail⟩ := assembleCappedBodies_starts_P gaps 0 u us
    rw [htail]
    simp only [List.cons_append, List.nil_append, dimerStartCount_H_cons, dimerStartCount_PP_cons]
    rw [← htail, dimerStartCount_assembleCappedBodies]

end ProteinFolding.Tetrahedral
