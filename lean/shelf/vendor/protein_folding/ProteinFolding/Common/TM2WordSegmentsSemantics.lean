import ProteinFolding.Common.TM2WordSegments
import ProteinFolding.Common.CookLevin

/-! Indexed splitting of terminator-delimited encodings. These identities
connect the actual marker scanner with typed list occurrences. -/

namespace ProteinFolding.TM2WordSegments

theorem splitMarkers_zero {A : Type} (p : A → Bool) (w : List A) :
    splitMarkers p w 0 = ([], w) := by cases w <;> rfl

theorem splitMarkers_segment {A : Type} (p : A → Bool) (t : A) (ht : p t = true)
    (u r : List A) (hu : ∀ a ∈ u, p a = false) (n : ℕ) :
    splitMarkers p (u ++ t :: r) (n + 1) =
      (u ++ t :: (splitMarkers p r n).1, (splitMarkers p r n).2) := by
  induction u with
  | nil => simp [splitMarkers, ht]
  | cons a u ih =>
    have ha := hu a (by simp)
    have hu' : ∀ b ∈ u, p b = false := fun b hb => hu b (List.mem_cons_of_mem _ hb)
    simp [splitMarkers, ha, ih hu']

theorem splitMarkers_terminated {A B : Type} (p : A → Bool) (t : A) (ht : p t = true)
    (enc : B → List A) (henc : ∀ b a, a ∈ enc b → p a = false) (xs : List B) (n : ℕ) :
    splitMarkers p (SAT.encTerminated t enc xs) n =
      (SAT.encTerminated t enc (xs.take n), SAT.encTerminated t enc (xs.drop n)) := by
  induction xs generalizing n with
  | nil => simp [SAT.encTerminated, splitMarkers]
  | cons b xs ih =>
    cases n with
    | zero => simp only [splitMarkers_zero, List.take_zero, List.drop_zero]; rfl
    | succ n =>
      change splitMarkers p ((enc b ++ [t]) ++ SAT.encTerminated t enc xs) (n + 1) = _
      rw [show (enc b ++ [t]) ++ SAT.encTerminated t enc xs =
          enc b ++ t :: SAT.encTerminated t enc xs by simp,
        splitMarkers_segment p t ht (enc b) _ (henc b) n, ih]
      simp [SAT.encTerminated]

theorem takeWhile_segment {A : Type} (p : A → Bool) (t : A) (ht : p t = false)
    (u r : List A) (hu : ∀ a ∈ u, p a = true) :
    (u ++ t :: r).takeWhile p = u := by
  induction u with
  | nil => simp [ht]
  | cons a u ih =>
    have ha := hu a (by simp)
    have hu' : ∀ b ∈ u, p b = true := fun b hb => hu b (List.mem_cons_of_mem _ hb)
    simp [ha, ih hu']

theorem splitMarkers_prefix_before {A : Type} (p : A → Bool) (u v : List A) (n : ℕ)
    (hn : n ≤ u.countP p) :
    (splitMarkers p (u ++ v) n).1 = (splitMarkers p u n).1 := by
  induction u generalizing n with
  | nil =>
    have hz : n = 0 := by simpa using hn
    subst n
    simp [splitMarkers_zero]
  | cons a u ih =>
    cases n with
    | zero => simp [splitMarkers_zero]
    | succ n =>
      cases hp : p a
      · have hn' : n + 1 ≤ u.countP p := by simpa [List.countP_cons, hp] using hn
        simpa [splitMarkers, hp] using congrArg (a :: ·) (ih (n + 1) hn')
      · have hn' : n ≤ u.countP p := by simpa [List.countP_cons, hp] using hn
        simpa [splitMarkers, hp] using congrArg (a :: ·) (ih n hn')

theorem splitMarkers_append_after {A : Type} (p : A → Bool) (u v : List A) (n : ℕ) :
    splitMarkers p (u ++ v) (u.countP p + n + 1) =
      (u ++ (splitMarkers p v (n + 1)).1, (splitMarkers p v (n + 1)).2) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    cases hp : p a
    · simpa [List.countP_cons, splitMarkers, hp] using
        congrArg (fun r : List A × List A => (a :: r.1, r.2)) ih
    · simpa [List.countP_cons, splitMarkers, hp, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg (fun r : List A × List A => (a :: r.1, r.2)) ih

theorem splitMarkers_prefix_count_zero {A : Type} (p q : A → Bool) (u : List A) (n : ℕ)
    (hu : u.countP q = 0) : (splitMarkers p u n).1.countP q = 0 := by
  have h := congrArg (List.countP q) (splitMarkers_append p u n)
  simp only [List.countP_append, hu] at h
  omega

end ProteinFolding.TM2WordSegments
