import ProteinFolding.Common.CookLevinProofCircuit

/-!
Local truth-table constraints for Cook--Levin tableaux. Every forbidden bit
pattern becomes one clause excluding exactly that pattern. The equivalence
allows repeated variable indices, so overlapping tableau windows require no
extra promise. For a fixed local arity q, each constraint contributes at most
2^q clauses of width q. This is a semantic/size theorem, not an assumed
polynomial-time TM2 implementation of a tableau emitter.
-/

namespace ProteinFolding.SAT

namespace CookLevinLocal

open CookLevinCircuit

def bitWords : ℕ → List (List Bool)
  | 0 => [[]]
  | q + 1 => (bitWords q).map (false :: ·) ++ (bitWords q).map (true :: ·)

theorem bitWords_mem (q : ℕ) (bs : List Bool) : bs ∈ bitWords q ↔ bs.length = q := by
  induction q generalizing bs with
  | zero => simp [bitWords]
  | succ q ih =>
    cases bs with
    | nil => simp [bitWords]
    | cons b bs => cases b <;> simp [bitWords, ih]

theorem bitWords_length (q : ℕ) : (bitWords q).length = 2 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [bitWords, List.length_append, List.length_map, ih, Nat.pow_succ]; omega

/-- The clause is false precisely when each selected variable has the specified
bit. Literal polarity is the complement of the forbidden bit. -/
def blockingClause : List ℕ → List Bool → Clause
  | i :: is, b :: bs => ⟨i, !b⟩ :: blockingClause is bs
  | _, _ => []

theorem blockingClause_length (is : List ℕ) (bs : List Bool) (h : is.length = bs.length) :
    (blockingClause is bs).length = is.length := by
  induction is generalizing bs with
  | nil => rfl
  | cons i is ih =>
    cases bs with
    | nil => simp at h
    | cons b bs => simpa [blockingClause] using ih bs (by simpa using h)

theorem blockingClause_iff (a : ℕ → Bool) (is : List ℕ) (bs : List Bool)
    (h : is.length = bs.length) :
    (∃ l ∈ blockingClause is bs, l.eval a = true) ↔ is.map a ≠ bs := by
  induction is generalizing bs with
  | nil =>
    have hb : bs = [] := List.length_eq_zero_iff.mp h.symm
    subst bs
    simp [blockingClause]
  | cons i is ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      have ht : is.length = bs.length := by simpa using h
      simp only [blockingClause, List.mem_cons, or_and_right, exists_or, exists_eq_left,
        List.map_cons]
      rw [ih bs ht]
      cases b <;> cases hi : a i <;>
        simp [Literal.eval, hi]

def relationCNF (is : List ℕ) (allowed : List Bool → Bool) : CNF :=
  ((bitWords is.length).filter (fun bs => !(allowed bs))).map (blockingClause is)

theorem relationCNF_iff (a : ℕ → Bool) (is : List ℕ) (allowed : List Bool → Bool) :
    Satisfied a (relationCNF is allowed) ↔ allowed (is.map a) = true := by
  constructor
  · intro h
    cases ha : allowed (is.map a) with
    | true => rfl
    | false =>
      have hb : is.map a ∈ bitWords is.length := (bitWords_mem _ _).mpr (by simp)
      have hc : blockingClause is (is.map a) ∈ relationCNF is allowed := by
        apply List.mem_map.mpr
        exact ⟨is.map a, List.mem_filter.mpr ⟨hb, by simp [ha]⟩, rfl⟩
      have hf := (blockingClause_iff a is (is.map a) (by simp)).mp (h _ hc)
      exact False.elim (hf rfl)
  · intro h c hc
    obtain ⟨bs, hb, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hmem, hforbidden⟩ := List.mem_filter.mp hb
    have hlen : is.length = bs.length := ((bitWords_mem _ _).mp hmem).symm
    apply (blockingClause_iff a is bs hlen).mpr
    intro he
    rw [← he, h] at hforbidden
    cases hforbidden

theorem relationCNF_clause_count (is : List ℕ) (allowed : List Bool → Bool) :
    (relationCNF is allowed).length ≤ 2 ^ is.length := by
  simpa [relationCNF, bitWords_length] using
    List.length_filter_le (fun bs => !(allowed bs)) (bitWords is.length)

theorem relationCNF_clause_width (is : List ℕ) (allowed : List Bool → Bool) :
    ∀ c ∈ relationCNF is allowed, c.length = is.length := by
  intro c hc
  obtain ⟨bs, hb, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hm, _⟩ := List.mem_filter.mp hb
  exact blockingClause_length is bs ((bitWords_mem _ _).mp hm).symm

theorem flatten_length_le (φ : CNF) (q : ℕ) (h : ∀ c ∈ φ, c.length ≤ q) :
    φ.flatten.length ≤ φ.length * q := by
  induction φ with
  | nil => simp
  | cons c φ ih =>
    have hc := h c (List.mem_cons_self ..)
    have ht := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul]
    omega

theorem relationCNF_literal_count (is : List ℕ) (allowed : List Bool → Bool) :
    (relationCNF is allowed).flatten.length ≤ 2 ^ is.length * is.length := by
  have h := flatten_length_le (relationCNF is allowed) is.length
    (fun c hc => le_of_eq (relationCNF_clause_width is allowed c hc))
  exact h.trans (Nat.mul_le_mul_right is.length (relationCNF_clause_count is allowed))

theorem blockingClause_vars (is : List ℕ) (bs : List Bool) :
    ∀ l ∈ blockingClause is bs, l.var ∈ is := by
  induction is generalizing bs with
  | nil => simp [blockingClause]
  | cons i is ih =>
    cases bs with
    | nil => simp [blockingClause]
    | cons b bs =>
      intro l hl
      rcases List.mem_cons.mp hl with he | he
      · subst l; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih bs l he)

theorem relationCNF_vars (is : List ℕ) (allowed : List Bool → Bool) :
    ∀ c ∈ relationCNF is allowed, ∀ l ∈ c, l.var ∈ is := by
  intro c hc l hl
  obtain ⟨bs, _, rfl⟩ := List.mem_map.mp hc
  exact blockingClause_vars is bs l hl

theorem relationCNF_encoded_length_bound (is : List ℕ) (allowed : List Bool → Bool) (V : ℕ)
    (hV : ∀ i ∈ is, i ≤ V) :
    (cnfEncoding.encode (relationCNF is allowed)).length ≤
      (2 ^ is.length * is.length) * (V + 2) + 2 ^ is.length := by
  have h := cnfEncoding_length_bound (relationCNF is allowed) V
    (fun c hc l hl => hV l.var (relationCNF_vars is allowed c hc l hl))
  exact h.trans (Nat.add_le_add
    (Nat.mul_le_mul_right (V + 2) (relationCNF_literal_count is allowed))
    (relationCNF_clause_count is allowed))

structure Constraint where
  vars : List ℕ
  allowed : List Bool → Bool

def Constraint.Holds (a : ℕ → Bool) (c : Constraint) : Prop := c.allowed (c.vars.map a) = true

def compileConstraints (cs : List Constraint) : CNF :=
  cs.flatMap (fun c => relationCNF c.vars c.allowed)

theorem compileConstraints_iff (a : ℕ → Bool) (cs : List Constraint) :
    Satisfied a (compileConstraints cs) ↔ ∀ c ∈ cs, c.Holds a := by
  induction cs with
  | nil => simp [compileConstraints, Satisfied]
  | cons c cs ih =>
    change Satisfied a (relationCNF c.vars c.allowed ++ compileConstraints cs) ↔ _
    rw [satisfied_append, relationCNF_iff, ih]
    simp [Constraint.Holds]

theorem compileConstraints_clause_bound (cs : List Constraint) (q : ℕ)
    (hq : ∀ c ∈ cs, c.vars.length ≤ q) :
    (compileConstraints cs).length ≤ cs.length * 2 ^ q := by
  induction cs with
  | nil => simp [compileConstraints]
  | cons c cs ih =>
    have hc := relationCNF_clause_count c.vars c.allowed
    have hp : 2 ^ c.vars.length ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) (hq c (List.mem_cons_self ..))
    have ht := ih (fun d hd => hq d (List.mem_cons_of_mem _ hd))
    change (cs.flatMap (fun c => relationCNF c.vars c.allowed)).length ≤ _ at ht
    simp only [compileConstraints, List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul]
    omega

theorem compileConstraints_clause_width (cs : List Constraint) (q : ℕ)
    (hq : ∀ c ∈ cs, c.vars.length ≤ q) :
    ∀ clause ∈ compileConstraints cs, clause.length ≤ q := by
  intro clause hc
  obtain ⟨c, hmem, hc⟩ := List.mem_flatMap.mp hc
  rw [relationCNF_clause_width c.vars c.allowed clause hc]
  exact hq c hmem

theorem compileConstraints_literal_bound (cs : List Constraint) (q : ℕ)
    (hq : ∀ c ∈ cs, c.vars.length ≤ q) :
    (compileConstraints cs).flatten.length ≤ (cs.length * 2 ^ q) * q := by
  exact (flatten_length_le (compileConstraints cs) q (compileConstraints_clause_width cs q hq)).trans
    (Nat.mul_le_mul_right q (compileConstraints_clause_bound cs q hq))

theorem compileConstraints_vars (cs : List Constraint) :
    ∀ clause ∈ compileConstraints cs, ∀ l ∈ clause, ∃ c ∈ cs, l.var ∈ c.vars := by
  intro clause hc l hl
  obtain ⟨c, hmem, hc⟩ := List.mem_flatMap.mp hc
  exact ⟨c, hmem, relationCNF_vars c.vars c.allowed clause hc l hl⟩

-- Repeating the same index is allowed; an impossible local pattern is rejected.
example : ¬ Satisfiable (relationCNF [0, 0] (fun bs => bs == [false, true])) := by
  rintro ⟨a, ha⟩
  have h := (relationCNF_iff a [0, 0] (fun bs => bs == [false, true])).mp ha
  cases hv : a 0 <;> simp [hv] at h

example : relationCNF [0, 1, 0] (fun _ => true) = [] := by decide

end CookLevinLocal

end ProteinFolding.SAT
