import ProteinFolding.Common.CookLevinProofRuns

/-! The actual finite CNF factors of a complete padded TM2 row transition.
Projection factors connect the local windows to row controls and cells. Each
factor has machine-fixed arity, including queries crossing the stack boundary.
-/

namespace ProteinFolding.SAT.CookLevinStepCNF

open Turing TM2 CookLevinAlphabet CookLevinWindow CookLevinWindowCNF CookLevinCells
open CookLevinPaddedWindow CookLevinRows CookLevinLinks CookLevinLocal CookLevinCircuit

noncomputable def reference (tm : FinTM2) (M t : ℕ) (b : Bit tm M) : ℕ :=
  t * width tm M + (bitIndex tm M b).val

noncomputable def codeRefs {A : Type*} [Fintype A] (tm : FinTM2) (M t : ℕ)
    (tag : A → Bit tm M) : List ℕ := (codeSlots tag).map (reference tm M t)

def Reads (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r : Row tm M) : Prop :=
  ∀ b, a (reference tm M t b) = encodeRow r b

theorem codeRefs_map {A : Type*} [Fintype A] (tm : FinTM2) (M t : ℕ)
    (tag : A → Bit tm M) (a : ℕ → Bool) (r : Row tm M) (h : Reads tm M t a r) :
    (codeRefs tm M t tag).map a = (codeSlots tag).map (encodeRow r) := by
  unfold codeRefs
  rw [List.map_map]
  apply List.map_congr_left
  intro b _
  exact h b

theorem controlCode (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r : Row tm M)
    (h : Reads tm M t a r) :
    (codeRefs tm M t (controlTag tm M)).map a = finiteCode r.control := by
  rw [codeRefs_map tm M t _ a r h]
  exact (codeSlots_match_iff _ _ _).mpr (fun _ => rfl)

theorem windowCode (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r : Row tm M)
    (h : Reads tm M t a r) :
    (codeRefs tm M t (windowTag tm M)).map a = finiteCode r.window := by
  rw [codeRefs_map tm M t _ a r h]
  exact (codeSlots_match_iff _ _ _).mpr (fun _ => rfl)

theorem replacementCode (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r : Row tm M)
    (h : Reads tm M t a r) :
    (codeRefs tm M t (replacementTag tm M)).map a = finiteCode r.replacement := by
  rw [codeRefs_map tm M t _ a r h]
  exact (codeSlots_match_iff _ _ _).mpr (fun _ => rfl)

theorem cellCode (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r : Row tm M)
    (h : Reads tm M t a r) (k : tm.K) (n : Fin M) :
    (codeRefs tm M t (cellTag tm M k n)).map a = finiteCode (r.cells k n) := by
  rw [codeRefs_map tm M t _ a r h]
  exact (codeSlots_match_iff _ _ _).mpr (fun _ => rfl)

theorem queryCode (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r : Row tm M)
    (h : Reads tm M t a r) (k : tm.K) (n : Fin M) :
    (codeRefs tm M t (queryTag tm M k n)).map a = finiteCode (r.queries k n) := by
  rw [codeRefs_map tm M t _ a r h]
  exact (codeSlots_match_iff _ _ _).mpr (fun _ => rfl)

noncomputable def functionAllowed {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (bs : List Bool) : Bool := by
  classical
  exact decide (∃ v : A, bs = finiteCode v ++ finiteCode (f v))

theorem functionAllowed_codes_iff {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (u : A) (v : B) :
    functionAllowed f (finiteCode u ++ finiteCode v) = true ↔ v = f u := by
  classical
  unfold functionAllowed
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨u', he⟩
    have hp := List.append_inj he (by simp only [finiteCode_length])
    have hu : u = u' := finiteCode_injective hp.1
    subst u'
    exact finiteCode_injective hp.2
  · rintro rfl
    exact ⟨u, rfl⟩

noncomputable def functionFactor {A B : Type*} [Fintype A] [Fintype B]
    (tm : FinTM2) (M t u : ℕ) (tagA : A → Bit tm M) (tagB : B → Bit tm M)
    (f : A → B) : Constraint :=
  ⟨codeRefs tm M t tagA ++ codeRefs tm M u tagB, functionAllowed f⟩

theorem functionFactor_codes_iff {A B : Type*} [Fintype A] [Fintype B]
    (tm : FinTM2) (M t u : ℕ) (tagA : A → Bit tm M) (tagB : B → Bit tm M)
    (f : A → B) (a : ℕ → Bool) (x : A) (y : B)
    (hx : (codeRefs tm M t tagA).map a = finiteCode x)
    (hy : (codeRefs tm M u tagB).map a = finiteCode y) :
    (functionFactor tm M t u tagA tagB f).Holds a ↔ y = f x := by
  simp only [functionFactor, Constraint.Holds, List.map_append, hx, hy, functionAllowed_codes_iff]

noncomputable def toCellFactor {A : Type*} [Fintype A]
    (tm : FinTM2) (M t : ℕ) (tag : A → Bit tm M)
    (k : tm.K) (n : ℕ) (f : A → Option (Symbol tm k)) : Constraint :=
  if hn : n < M then functionFactor tm M t t tag (cellTag tm M k ⟨n, hn⟩) f
  else ⟨codeRefs tm M t tag, fun bs => functionAllowed f (bs ++ finiteCode (none : Option (Symbol tm k)))⟩

theorem toCellFactor_codes_iff {A : Type*} [Fintype A]
    (tm : FinTM2) (M t : ℕ) (tag : A → Bit tm M)
    (k : tm.K) (n : ℕ) (f : A → Option (Symbol tm k))
    (a : ℕ → Bool) (r : Row tm M) (h : Reads tm M t a r) (x : A)
    (hx : (codeRefs tm M t tag).map a = finiteCode x) :
    (toCellFactor tm M t tag k n f).Holds a ↔ rowCell r k n = f x := by
  unfold toCellFactor rowCell
  split
  · exact functionFactor_codes_iff tm M t t tag _ f a x _ hx (cellCode tm M t a r h k _)
  · simp only [Constraint.Holds, hx, functionAllowed_codes_iff]

noncomputable def controlLink (tm : FinTM2) (M t : ℕ) : Constraint :=
  functionFactor tm M t t (windowTag tm M) (controlTag tm M) (fun w => w.1)

noncomputable def executionLink (tm : FinTM2) (M t : ℕ) : Constraint :=
  ⟨codeRefs tm M t (windowTag tm M) ++ codeRefs tm M t (replacementTag tm M), paddedWindowAllowed tm⟩

noncomputable def nextControlLink (tm : FinTM2) (M t : ℕ) : Constraint :=
  functionFactor tm M t (t + 1) (replacementTag tm M) (controlTag tm M) (fun r => (r.1, r.2.1))

noncomputable def prefixLink (tm : FinTM2) (M t : ℕ) (k : tm.K) (i : Fin (machineReadBound tm)) : Constraint :=
  toCellFactor tm M t (windowTag tm M) k i.val (fun w => ((w.2 k).val)[i.val]?)

noncomputable def queryLink (tm : FinTM2) (M t : ℕ) (k : tm.K) (n : Fin M)
    (i : Fin (cellWindowWidth tm)) : Constraint :=
  toCellFactor tm M t (queryTag tm M k n) k (cellBase tm n.val + i.val) (fun q => q i)

noncomputable def selectedCellLink (tm : FinTM2) (M t : ℕ) (k : tm.K) (n : Fin M) : Constraint :=
  ⟨codeRefs tm M t (replacementTag tm M) ++ codeRefs tm M t (queryTag tm M k n) ++
    codeRefs tm M (t + 1) (cellTag tm M k n), cellAllowed tm k n.val⟩

theorem controlLink_iff (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r : Row tm M)
    (h : Reads tm M t a r) : (controlLink tm M t).Holds a ↔ r.control = r.window.1 :=
  functionFactor_codes_iff _ _ _ _ _ _ _ _ _ _ (windowCode tm M t a r h) (controlCode tm M t a r h)

theorem executionLink_iff (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r : Row tm M)
    (h : Reads tm M t a r) :
    (executionLink tm M t).Holds a ↔ r.replacement = executePaddedWindow tm r.window := by
  simp only [executionLink, Constraint.Holds, List.map_append,
    windowCode tm M t a r h, replacementCode tm M t a r h, paddedWindowAllowed_code_iff]

theorem nextControlLink_iff (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r s : Row tm M)
    (hr : Reads tm M t a r) (hs : Reads tm M (t + 1) a s) :
    (nextControlLink tm M t).Holds a ↔ s.control = (r.replacement.1, r.replacement.2.1) :=
  functionFactor_codes_iff _ _ _ _ _ _ _ _ _ _ (replacementCode tm M t a r hr) (controlCode tm M (t + 1) a s hs)

theorem prefixLink_iff (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r : Row tm M)
    (h : Reads tm M t a r) (k : tm.K) (i : Fin (machineReadBound tm)) :
    (prefixLink tm M t k i).Holds a ↔ rowCell r k i.val = ((r.window.2 k).val)[i.val]? :=
  toCellFactor_codes_iff tm M t (windowTag tm M) k i.val
    (fun w => ((w.2 k).val)[i.val]?) a r h r.window (windowCode tm M t a r h)

theorem queryLink_iff (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r : Row tm M)
    (h : Reads tm M t a r) (k : tm.K) (n : Fin M) (i : Fin (cellWindowWidth tm)) :
    (queryLink tm M t k n i).Holds a ↔ rowCell r k (cellBase tm n.val + i.val) = r.queries k n i :=
  toCellFactor_codes_iff tm M t (queryTag tm M k n) k (cellBase tm n.val + i.val)
    (fun q => q i) a r h (r.queries k n) (queryCode tm M t a r h k n)

theorem selectedCellLink_iff (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r s : Row tm M)
    (hr : Reads tm M t a r) (hs : Reads tm M (t + 1) a s) (k : tm.K) (n : Fin M) :
    (selectedCellLink tm M t k n).Holds a ↔
      s.cells k n = selectCell tm k n.val r.replacement (r.queries k n) := by
  simp only [selectedCellLink, Constraint.Holds, List.map_append,
    replacementCode tm M t a r hr, queryCode tm M t a r hr k n,
    cellCode tm M (t + 1) a s hs k n, cellAllowed_code_iff]

noncomputable def stepConstraints (tm : FinTM2) (M t : ℕ) : List Constraint := by
  letI := tm.kFin
  exact [controlLink tm M t, executionLink tm M t, nextControlLink tm M t] ++
    Finset.univ.toList.flatMap (fun k =>
      (List.finRange (machineReadBound tm)).map (prefixLink tm M t k) ++
      (List.finRange M).flatMap (fun n =>
        (List.finRange (cellWindowWidth tm)).map (queryLink tm M t k n) ++ [selectedCellLink tm M t k n]))

theorem stepConstraints_iff (tm : FinTM2) (M t : ℕ) (a : ℕ → Bool) (r s : Row tm M)
    (hr : Reads tm M t a r) (hs : Reads tm M (t + 1) a s) :
    Satisfied a (compileConstraints (stepConstraints tm M t)) ↔ Links r s := by
  letI := tm.kFin
  rw [compileConstraints_iff]
  unfold stepConstraints
  simp only [List.forall_mem_append, List.forall_mem_cons, List.forall_mem_flatMap,
    List.forall_mem_map, List.not_mem_nil, false_implies, forall_const,
    Finset.mem_toList, Finset.mem_univ, List.mem_finRange,
    controlLink_iff tm M t a r hr, executionLink_iff tm M t a r hr,
    nextControlLink_iff tm M t a r s hr hs, prefixLink_iff tm M t a r hr,
    queryLink_iff tm M t a r hr, selectedCellLink_iff tm M t a r s hr hs]
  simp only [forall_true_iff, and_true]
  constructor
  · rintro ⟨⟨hc, he, hn⟩, hcells⟩
    exact ⟨hc.symm, fun k i => (hcells k).1 i |>.symm, he, hn,
      fun k n i => ((hcells k).2 n).1 i |>.symm, fun k n => ((hcells k).2 n).2⟩
  · rintro ⟨hc, hp, he, hn, hq, ho⟩
    exact ⟨⟨hc.symm, he, hn⟩, fun k => ⟨fun i => (hp k i).symm,
      fun n => ⟨fun i => (hq k n i).symm, ho k n⟩⟩⟩

end ProteinFolding.SAT.CookLevinStepCNF
