import ProteinFolding.Common.SAT.OccurrenceCycles

/-! The sorted occurrence cycle advances to the least strictly greater
occurrence of the same variable, wrapping to the least occurrence at its end.
All ordering is on explicit occurrence indices, not variable magnitudes. -/

namespace ProteinFolding.ThreeDimensionalMatching

theorem sorted_rotate_next_after {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f)
    (i : Fin n) (hex : ∃ j, f i < f j) :
    f i < f (finRotate n i) ∧ ∀ j, f i < f j → f (finRotate n i) ≤ f j := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hlast : i ≠ Fin.last n := by
      intro he
      obtain ⟨j, hj⟩ := hex
      have hij : i < j := hf.lt_iff_lt.mp hj
      have hjb := j.isLt
      rw [he] at hij
      change n < j.val at hij
      omega
    have hnext := coe_finRotate_of_ne_last hlast
    have hinc : i < finRotate (n + 1) i := by
      change i.val < (finRotate (n + 1) i).val
      omega
    refine ⟨hf hinc, ?_⟩
    intro j hj
    have hij : i < j := hf.lt_iff_lt.mp hj
    have hle : finRotate (n + 1) i ≤ j := by
      change (finRotate (n + 1) i).val ≤ j.val
      omega
    exact hf.monotone hle

theorem sorted_rotate_next_wrap {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f)
    (i : Fin n) (hnone : ∀ j, f j ≤ f i) : ∀ j, f (finRotate n i) ≤ f j := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hlast : i = Fin.last n := by
      have hle : Fin.last n ≤ i := hf.le_iff_le.mp (hnone (Fin.last n))
      apply Fin.ext
      change i.val = n
      change n ≤ i.val at hle
      have hi := i.isLt
      omega
    rw [hlast, finRotate_last]
    intro j
    apply hf.monotone
    change 0 ≤ j.val
    omega

theorem variableFiberEquiv_index_strictMono {q : ℕ} (v : Fin q → ℕ) (a : ℕ) :
    StrictMono (fun r : Fin (variableFiberSet v a).card => (variableFiberEquiv v a r).val.val) := by
  intro i j hij
  exact ((variableFiberSet v a).orderEmbOfFin rfl).strictMono hij

theorem occurrenceCycle_rank {q : ℕ} (v : Fin q → ℕ) (a : ℕ)
    (r : Fin (variableFiberSet v a).card) :
    occurrenceCycle v (variableFiberEquiv v a r).val =
      (variableFiberEquiv v a (finRotate (variableFiberSet v a).card r)).val := by
  rw [occurrenceCycle_fiber v a (variableFiberEquiv v a r)]
  simp [variableFiberCycle, rotateOn]

/-- If a later occurrence exists, the cycle chooses the least such index. -/
theorem occurrenceCycle_next_after {q : ℕ} (v : Fin q → ℕ) (i : Fin q)
    (hex : ∃ k, v k = v i ∧ i.val < k.val) :
    i.val < (occurrenceCycle v i).val ∧
      ∀ k, v k = v i → i.val < k.val → (occurrenceCycle v i).val ≤ k.val := by
  let e := variableFiberEquiv v (v i)
  let r := e.symm ⟨i, rfl⟩
  have hr : (e r).val = i := congrArg Subtype.val (e.apply_symm_apply ⟨i, rfl⟩)
  have hnext := occurrenceCycle_rank v (v i) r
  change occurrenceCycle v (e r).val = (e (finRotate (variableFiberSet v (v i)).card r)).val at hnext
  rw [hr] at hnext
  have hm : StrictMono (fun s => (e s).val.val) := variableFiberEquiv_index_strictMono v (v i)
  have hex' : ∃ s, (e r).val.val < (e s).val.val := by
    obtain ⟨k, hkv, hik⟩ := hex
    let s := e.symm ⟨k, hkv⟩
    have hs : (e s).val = k := congrArg Subtype.val (e.apply_symm_apply ⟨k, hkv⟩)
    exact ⟨s, by simpa only [hr, hs] using hik⟩
  obtain ⟨hafter, hleast⟩ := sorted_rotate_next_after (fun s => (e s).val.val) hm r hex'
  constructor
  · simpa only [hr, ← hnext] using hafter
  · intro k hkv hik
    let s := e.symm ⟨k, hkv⟩
    have hs : (e s).val = k := congrArg Subtype.val (e.apply_symm_apply ⟨k, hkv⟩)
    have hlt : (e r).val.val < (e s).val.val := by simpa only [hr, hs] using hik
    simpa only [hs, ← hnext] using hleast s hlt

/-- At the last occurrence, the cycle wraps to the smallest occurrence index. -/
theorem occurrenceCycle_next_wrap {q : ℕ} (v : Fin q → ℕ) (i : Fin q)
    (hnone : ∀ k, v k = v i → k.val ≤ i.val) :
    ∀ k, v k = v i → (occurrenceCycle v i).val ≤ k.val := by
  let e := variableFiberEquiv v (v i)
  let r := e.symm ⟨i, rfl⟩
  have hr : (e r).val = i := congrArg Subtype.val (e.apply_symm_apply ⟨i, rfl⟩)
  have hnext := occurrenceCycle_rank v (v i) r
  change occurrenceCycle v (e r).val = (e (finRotate (variableFiberSet v (v i)).card r)).val at hnext
  rw [hr] at hnext
  have hm : StrictMono (fun s => (e s).val.val) := variableFiberEquiv_index_strictMono v (v i)
  have hlast : ∀ s, (e s).val.val ≤ (e r).val.val := by
    intro s
    simpa only [hr] using hnone (e s).val (e s).property
  have hleast := sorted_rotate_next_wrap (fun s => (e s).val.val) hm r hlast
  intro k hkv
  let s := e.symm ⟨k, hkv⟩
  have hs : (e s).val = k := congrArg Subtype.val (e.apply_symm_apply ⟨k, hkv⟩)
  simpa only [hs, ← hnext] using hleast s

end ProteinFolding.ThreeDimensionalMatching
