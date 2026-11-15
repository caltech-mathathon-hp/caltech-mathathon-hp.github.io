import ProteinFolding.Common.CookLevinProofRowIndex
import ProteinFolding.Common.CookLevinProofEncodingSize

/-! Semantic renaming from the unchanged row enumeration to the arithmetic
layout. The renaming is a permutation of all natural variable identifiers,
preserves row blocks and sends every original reference to its affine index.
It need not be computed by the frontend: the frontend emits the affine indices
directly, while these lemmas transport the existing CNF correctness theorem. -/

namespace ProteinFolding.SAT.CookLevinRowRename

open Turing TM2 CookLevinRows CookLevinStepCNF CookLevinRowIndex
  CookLevinCircuit CookLevinLocal CookLevinGlobalCNF

def natRows (W : ℕ) (hW : 0 < W) : ℕ ≃ ℕ × Fin W where
  toFun z := (z / W, ⟨z % W, Nat.mod_lt _ hW⟩)
  invFun x := x.1 * W + x.2.val
  left_inv z := Nat.div_add_mod' z W
  right_inv x := by
    rcases x with ⟨t, i⟩
    apply Prod.ext
    · dsimp
      rw [Nat.add_comm (t * W), Nat.add_mul_div_right _ _ hW,
        Nat.div_eq_of_lt i.isLt, Nat.zero_add]
    · apply Fin.ext
      simp [Nat.mod_eq_of_lt i.isLt]

noncomputable def rowPermutation (tm : FinTM2) (M : ℕ) : Fin (width tm M) ≃ Fin (width tm M) :=
  (bitIndex tm M).symm.trans (arithmeticBitIndex tm M)

noncomputable def renameIndex (tm : FinTM2) (M : ℕ) : ℕ ≃ ℕ :=
  ((natRows (width tm M) (width_pos tm M)).trans
    (Equiv.prodCongr (Equiv.refl ℕ) (rowPermutation tm M))).trans
      (natRows (width tm M) (width_pos tm M)).symm

theorem renameIndex_apply (tm : FinTM2) (M z : ℕ) :
    renameIndex tm M z = z / width tm M * width tm M +
      (arithmeticBitIndex tm M ((bitIndex tm M).symm
        ⟨z % width tm M, Nat.mod_lt _ (width_pos tm M)⟩)).val := rfl

theorem renameIndex_reference (tm : FinTM2) (M t : ℕ) (b : Bit tm M) :
    renameIndex tm M (reference tm M t b) = arithmeticReference tm M t b := by
  have hd : (t * width tm M + (bitIndex tm M b).val) / width tm M = t := by
    rw [Nat.add_comm (t * width tm M), Nat.add_mul_div_right _ _ (width_pos tm M),
      Nat.div_eq_of_lt (bitIndex tm M b).isLt, Nat.zero_add]
  have hm : (t * width tm M + (bitIndex tm M b).val) % width tm M = (bitIndex tm M b).val := by
    simp [Nat.mod_eq_of_lt (bitIndex tm M b).isLt]
  have hi : (⟨(t * width tm M + (bitIndex tm M b).val) % width tm M,
      Nat.mod_lt _ (width_pos tm M)⟩ : Fin (width tm M)) = bitIndex tm M b := Fin.ext hm
  rw [renameIndex_apply]
  simp only [reference]
  rw [hd, hi, Equiv.symm_apply_apply]
  rfl

theorem renameIndex_symm_reference (tm : FinTM2) (M t : ℕ) (b : Bit tm M) :
    (renameIndex tm M).symm (arithmeticReference tm M t b) = reference tm M t b := by
  apply (renameIndex tm M).injective
  rw [Equiv.apply_symm_apply, renameIndex_reference]

theorem renameIndex_div (tm : FinTM2) (M z : ℕ) :
    renameIndex tm M z / width tm M = z / width tm M := by
  rw [renameIndex_apply]
  rw [Nat.add_comm (z / width tm M * width tm M),
    Nat.add_mul_div_right _ _ (width_pos tm M),
    Nat.div_eq_of_lt (arithmeticBitIndex tm M _).isLt, Nat.zero_add]

theorem renameIndex_lt_iff (tm : FinTM2) (M B z : ℕ) :
    renameIndex tm M z < B * width tm M ↔ z < B * width tm M := by
  constructor
  · intro h
    have hd := (Nat.div_lt_iff_lt_mul (width_pos tm M)).mpr h
    rw [renameIndex_div] at hd
    exact (Nat.div_lt_iff_lt_mul (width_pos tm M)).mp hd
  · intro h
    have hd := (Nat.div_lt_iff_lt_mul (width_pos tm M)).mpr h
    rw [← renameIndex_div tm M z] at hd
    exact (Nat.div_lt_iff_lt_mul (width_pos tm M)).mp hd

def renameLiteral (f : ℕ → ℕ) (l : Literal) : Literal := ⟨f l.var, l.pos⟩
def renameClause (f : ℕ → ℕ) (c : Clause) : Clause := c.map (renameLiteral f)
def renameCNF (f : ℕ → ℕ) (φ : CNF) : CNF := φ.map (renameClause f)

theorem renameLiteral_eval (f : ℕ → ℕ) (a : ℕ → Bool) (l : Literal) :
    (renameLiteral f l).eval a = l.eval (fun i => a (f i)) := rfl

theorem renameClause_satisfied (f : ℕ → ℕ) (a : ℕ → Bool) (c : Clause) :
    (∃ l ∈ renameClause f c, l.eval a = true) ↔ ∃ l ∈ c, l.eval (fun i => a (f i)) = true := by
  constructor
  · rintro ⟨l, hl, he⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
    exact ⟨k, hk, he⟩
  · rintro ⟨l, hl, he⟩
    exact ⟨renameLiteral f l, List.mem_map.mpr ⟨l, hl, rfl⟩, he⟩

theorem renameCNF_satisfied (f : ℕ → ℕ) (a : ℕ → Bool) (φ : CNF) :
    Satisfied a (renameCNF f φ) ↔ Satisfied (fun i => a (f i)) φ := by
  simp only [renameCNF, Satisfied, List.forall_mem_map, renameClause_satisfied]

theorem renameCNF_satisfiable (e : ℕ ≃ ℕ) (φ : CNF) :
    Satisfiable (renameCNF e φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨fun i => a (e i), (renameCNF_satisfied e a φ).mp ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a (e.symm i), (renameCNF_satisfied e _ φ).mpr ?_⟩
    simpa only [Equiv.symm_apply_apply] using ha

theorem renameCNF_length (f : ℕ → ℕ) (φ : CNF) : (renameCNF f φ).length = φ.length := by
  simp [renameCNF]

theorem renameCNF_literal_count (f : ℕ → ℕ) (φ : CNF) :
    (renameCNF f φ).flatten.length = φ.flatten.length := by
  simp [renameCNF, renameClause, List.length_flatten, List.map_map, Function.comp_def]

theorem rename_blockingClause (f : ℕ → ℕ) (is : List ℕ) (bs : List Bool) :
    renameClause f (blockingClause is bs) = blockingClause (is.map f) bs := by
  induction is generalizing bs with
  | nil => simp [blockingClause, renameClause]
  | cons i is ih =>
    cases bs with
    | nil => simp [blockingClause, renameClause]
    | cons b bs =>
      simpa only [blockingClause, renameClause, List.map_cons, renameLiteral] using
        congrArg (List.cons (⟨f i, !b⟩ : Literal)) (ih bs)

theorem rename_relationCNF (f : ℕ → ℕ) (is : List ℕ) (allowed : List Bool → Bool) :
    renameCNF f (relationCNF is allowed) = relationCNF (is.map f) allowed := by
  simp only [relationCNF, renameCNF, List.length_map, List.map_map]
  apply List.map_congr_left
  intro bs _
  exact rename_blockingClause f is bs

def renameConstraint (f : ℕ → ℕ) (c : Constraint) : Constraint := ⟨c.vars.map f, c.allowed⟩

@[simp] theorem rename_codeRefs {A : Type*} [Fintype A] (tm : FinTM2) (M t : ℕ)
    (tag : A → Bit tm M) :
    (codeRefs tm M t tag).map (renameIndex tm M) = (codeSlots tag).map (arithmeticReference tm M t) := by
  simp only [codeRefs, List.map_map, Function.comp_def, renameIndex_reference]

theorem rename_shifted_component {A : Type*} [Fintype A] (tm : FinTM2) (M t : ℕ)
    (tag : A → Bit tm M) :
    renameConstraint (renameIndex tm M)
      (shiftConstraint (t * width tm M) (componentConstraint tm M tag)) =
        ⟨(codeSlots tag).map (arithmeticReference tm M t), codeAllowed A⟩ := by
  simp only [renameConstraint, shiftConstraint, componentConstraint, List.map_map, Function.comp_def]
  change (⟨(codeSlots tag).map (fun b => renameIndex tm M (t * width tm M + (bitIndex tm M b).val)),
    codeAllowed A⟩ : Constraint) = _
  congr 1
  apply List.map_congr_left
  intro b _
  exact renameIndex_reference tm M t b

theorem rename_functionFactor {A B : Type*} [Fintype A] [Fintype B]
    (tm : FinTM2) (M t u : ℕ) (tagA : A → Bit tm M) (tagB : B → Bit tm M) (f : A → B) :
    renameConstraint (renameIndex tm M) (functionFactor tm M t u tagA tagB f) =
      ⟨(codeSlots tagA).map (arithmeticReference tm M t) ++
        (codeSlots tagB).map (arithmeticReference tm M u), functionAllowed f⟩ := by
  simp only [renameConstraint, functionFactor, List.map_append, rename_codeRefs]

theorem rename_compileConstraints (f : ℕ → ℕ) (cs : List Constraint) :
    renameCNF f (compileConstraints cs) = compileConstraints (cs.map (renameConstraint f)) := by
  simp only [compileConstraints, renameCNF, List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro c _
  exact rename_relationCNF f c.vars c.allowed

noncomputable def arithmeticGlobalCNF (tm : FinTM2) (M T : ℕ) : CNF :=
  renameCNF (renameIndex tm M) (globalCNF tm M T)

theorem arithmeticGlobalCNF_eq_constraints (tm : FinTM2) (M T : ℕ) :
    arithmeticGlobalCNF tm M T =
      compileConstraints ((globalConstraints tm M T).map (renameConstraint (renameIndex tm M))) :=
  rename_compileConstraints (renameIndex tm M) (globalConstraints tm M T)

theorem arithmeticGlobalCNF_satisfiable (tm : FinTM2) (M T : ℕ) :
    Satisfiable (arithmeticGlobalCNF tm M T) ↔ Satisfiable (globalCNF tm M T) :=
  renameCNF_satisfiable (renameIndex tm M) (globalCNF tm M T)

theorem arithmeticGlobalCNF_models (tm : FinTM2) (M T : ℕ) (a : ℕ → Bool) :
    Satisfied a (arithmeticGlobalCNF tm M T) ↔ ∃ rows : ℕ → Row tm M,
      (∀ t ≤ T, ∀ b, a (arithmeticReference tm M t b) = encodeRow (rows t) b) ∧
        (∀ t < T, CookLevinLinks.Links (rows t) (rows (t + 1))) := by
  rw [arithmeticGlobalCNF, renameCNF_satisfied, globalCNF_iff]
  simp only [Reads, renameIndex_reference]

theorem arithmeticGlobalCNF_vars_lt (tm : FinTM2) (M T : ℕ) :
    ∀ c ∈ arithmeticGlobalCNF tm M T, ∀ l ∈ c, l.var < (T + 1) * width tm M := by
  intro c hc l hl
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
  change renameIndex tm M k.var < (T + 1) * width tm M
  exact (renameIndex_lt_iff tm M (T + 1) k.var).mpr
    (CookLevinEncodingSize.globalCNF_vars_lt tm M T d hd k hk)

end ProteinFolding.SAT.CookLevinRowRename
