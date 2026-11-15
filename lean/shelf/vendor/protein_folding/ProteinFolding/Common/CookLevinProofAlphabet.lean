import ProteinFolding.Common.CookLevinProofLocality
import Mathlib.Data.Set.Finite.List

/-! A finite alphabet for every reachable stack of an actual mathlib FinTM2.
Internal stack types need not be finite in FinTM2. Only finitely many symbols
can be pushed: the program syntax and the internal-state type are finite.
Together with the finite input alphabet these give a finite, invariant support.
-/

namespace ProteinFolding.SAT.CookLevinAlphabet

open Turing TM2

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

open scoped Classical in
noncomputable def pushedSymbols [DecidableEq K] [Fintype σ] : Stmt Γ Λ σ → Finset (Σ k, Γ k)
  | .push k f q => (Finset.univ.image (fun v => (⟨k, f v⟩ : Σ j, Γ j))) ∪ pushedSymbols q
  | .peek _ _ q | .pop _ _ q | .load _ q => pushedSymbols q
  | .branch _ q r => pushedSymbols q ∪ pushedSymbols r
  | .goto _ | .halt => ∅

def StacksIn (A : Finset (Σ k, Γ k)) (S : ∀ k, List (Γ k)) : Prop :=
  ∀ k x, x ∈ S k → (⟨k, x⟩ : Σ j, Γ j) ∈ A

theorem stacksIn_update [DecidableEq K] (A : Finset (Σ k, Γ k))
    (S : ∀ k, List (Γ k)) (k : K) (xs : List (Γ k))
    (hS : StacksIn A S) (hxs : ∀ x ∈ xs, (⟨k, x⟩ : Σ j, Γ j) ∈ A) :
    StacksIn A (Function.update S k xs) := by
  intro j x hx
  by_cases hj : j = k
  · subst j
    exact hxs x (by simpa using hx)
  · exact hS j x (by simpa [Function.update, hj] using hx)

theorem stepAux_stacksIn [DecidableEq K] [Fintype σ]
    (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (A : Finset (Σ k, Γ k))
    (hS : StacksIn A S) (hq : pushedSymbols q ⊆ A) :
    StacksIn A (stepAux q v S).stk := by
  classical
  induction q generalizing v S with
  | push k f q ih =>
    apply ih v (Function.update S k (f v :: S k))
    · apply stacksIn_update A S k _ hS
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hq (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩))
      · exact hS k x hx
    · exact fun z hz => hq (Finset.mem_union_right _ hz)
  | peek k f q ih => exact ih _ S hS hq
  | pop k f q ih =>
    apply ih _ (Function.update S k (S k).tail)
    · exact stacksIn_update A S k _ hS (fun x hx => hS k x (List.mem_of_mem_tail hx))
    · exact hq
  | load f q ih => exact ih _ S hS hq
  | branch f q r ihq ihr =>
    simp only [stepAux]
    cases hf : f v
    · exact ihr v S hS (fun z hz => hq (Finset.mem_union_right _ hz))
    · exact ihq v S hS (fun z hz => hq (Finset.mem_union_left _ hz))
  | goto f => exact hS
  | halt => exact hS

noncomputable def machineSymbols (tm : FinTM2) : Finset (Σ k, tm.Γ k) := by
  classical
  letI := tm.ΛFin
  letI := tm.σFin
  letI := tm.Γk₀Fin
  exact (Finset.univ.image (fun x => (⟨tm.k₀, x⟩ : Σ k, tm.Γ k))) ∪
    Finset.univ.biUnion (fun l => pushedSymbols (tm.m l))

theorem pushedSymbols_subset_machineSymbols (tm : FinTM2) (l : tm.Λ) :
    letI := tm.σFin
    pushedSymbols (tm.m l) ⊆ machineSymbols tm := by
  classical
  letI := tm.ΛFin
  letI := tm.σFin
  letI := tm.Γk₀Fin
  intro z hz
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, hz⟩)

theorem initList_stacksIn (tm : FinTM2) (input : List (tm.Γ tm.k₀)) :
    StacksIn (machineSymbols tm) (initList tm input).stk := by
  classical
  letI := tm.ΛFin
  letI := tm.σFin
  letI := tm.Γk₀Fin
  intro k x hx
  by_cases hk : k = tm.k₀
  · subst k
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  · simp [initList, hk] at hx

theorem step_stacksIn (tm : FinTM2) (a b : tm.Cfg)
    (ha : StacksIn (machineSymbols tm) a.stk) (h : tm.step a = some b) :
    StacksIn (machineSymbols tm) b.stk := by
  letI := tm.σFin
  obtain ⟨label, v, S⟩ := a
  cases label with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
    have hb : stepAux (tm.m l) v S = b := by simpa [FinTM2.step, TM2.step] using h
    rw [← hb]
    exact stepAux_stacksIn _ _ _ _ ha (pushedSymbols_subset_machineSymbols tm l)

theorem iterate_stacksIn (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (n : ℕ) (c : tm.Cfg)
    (h : (fun x : Option tm.Cfg => x.bind tm.step)^[n] (some (initList tm input)) = some c) :
    StacksIn (machineSymbols tm) c.stk := by
  induction n generalizing c with
  | zero =>
    have he : initList tm input = c := by simpa using h
    rw [← he]
    exact initList_stacksIn tm input
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    change ((fun x : Option tm.Cfg => x.bind tm.step)^[n]
      (some (initList tm input))).bind tm.step = some c at h
    cases hc : (fun x : Option tm.Cfg => x.bind tm.step)^[n] (some (initList tm input)) with
    | none => rw [hc] at h; contradiction
    | some d =>
      rw [hc] at h
      exact step_stacksIn tm d c (ih d hc) h

def Symbol (tm : FinTM2) (k : tm.K) := {x : tm.Γ k // (⟨k, x⟩ : Σ j, tm.Γ j) ∈ machineSymbols tm}

noncomputable instance symbolFintype (tm : FinTM2) (k : tm.K) : Fintype (Symbol tm k) := by
  classical
  apply Fintype.ofInjective (fun x : Symbol tm k =>
    (⟨⟨k, x.val⟩, x.property⟩ : {z // z ∈ machineSymbols tm}))
  intro x y h
  apply Subtype.ext
  exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2

noncomputable def encodeStack (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k))
    (h : ∀ x ∈ xs, (⟨k, x⟩ : Σ j, tm.Γ j) ∈ machineSymbols tm) : List (Symbol tm k) :=
  xs.pmap (fun x hx => ⟨x, hx⟩) h

theorem encodeStack_decode (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k))
    (h : ∀ x ∈ xs, (⟨k, x⟩ : Σ j, tm.Γ j) ∈ machineSymbols tm) :
    (encodeStack tm k xs h).map Subtype.val = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [encodeStack, List.pmap_cons, List.map_cons]
    congr 1
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem encodeStack_length (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k))
    (h : ∀ x ∈ xs, (⟨k, x⟩ : Σ j, tm.Γ j) ∈ machineSymbols tm) :
    (encodeStack tm k xs h).length = xs.length := by
  rw [← List.length_map (f := Subtype.val), encodeStack_decode]

end ProteinFolding.SAT.CookLevinAlphabet
