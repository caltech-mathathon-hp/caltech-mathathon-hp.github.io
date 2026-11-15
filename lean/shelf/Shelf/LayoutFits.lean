import Shelf.LayoutPlain

/-!
# The fold spells the string

Parts (d) and (e) of Theorem 16: along the fold, the sites in the cube are
exactly the positions of the letters `H`.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue Layout

namespace LayoutFits

/-- `Forall₂` of two appends, piece by piece. -/
theorem app {R : α → β → Prop} {a a' : List α} {b b' : List β}
    (h : List.Forall₂ R a b) (h' : List.Forall₂ R a' b') : List.Forall₂ R (a ++ a') (b ++ b') :=
  List.rel_append h h'

/-- `Forall₂` of two `flatMap`s over the same list, entry by entry. -/
theorem flatMap {R : α → β → Prop} {l : List γ} {f : γ → List α} {g : γ → List β}
    (h : ∀ i ∈ l, List.Forall₂ R (f i) (g i)) :
    List.Forall₂ R (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons x l ih =>
    simp only [List.flatMap_cons]
    exact app (h x (by simp)) (ih fun i hi => h i (by simp [hi]))

/-- Sites that are all outside the cube carry a run of `r` letters `P`, if there are `r`. -/
theorem fits_runP {n r : ℕ} {ps : List Site} (h : ∀ p ∈ ps, p ∉ Q n) (hr : ps.length = r) :
    List.Forall₂ (Fits n) ps (List.replicate r P) := by
  subst hr; exact fits_replicate_P h

/-- The tokens carry `T(r)`, if there are `r` of them. -/
theorem fits_tok {n r : ℕ} {ts : List Token} (hv : ∀ t ∈ ts, t.Valid n) (hr : ts.length = r) :
    List.Forall₂ (Fits n) (tokSites ts) (tokWord r) := by
  subst hr; exact tokSites_fits hv

theorem plain_out {J : Packing.Instance} {p : Site} (h : p ∈ plain J) : p ∉ Q (side J) :=
  plain_not_mem_Q J p h

theorem mid_out_Q {J : Packing.Instance} {P : Parts J} (hP : P.Good) {i} {s : Site}
    (hs : s ∈ P.mid i) : s ∉ Q (side J) :=
  fun hq => hP.mid_out i s hs (inBox_of_mem_Q hq)

end LayoutFits

open LayoutFits in
/-- Parts (d) and (e) of Theorem 16: along the fold, a site carries an `H` exactly when it
is in the cube. We match the ten pieces of `layout` with the ten pieces of `layoutWord`. -/
theorem layout_fits {J : Packing.Instance} (_hJ : Normalised J) {P : Parts J} (hP : P.Good) :
    List.Forall₂ (Fits (side J)) (layout P) (layoutWord J) := by
  unfold layout layoutWord
  refine app (app (app (app (app (app (app (app (app ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · rw [← hP.core_length]
    exact fits_replicate_H fun p hp => (hP.core_mem p hp).1
  · exact fits_runP (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact plain_out (mem_plain.2 (Or.inl rfl)))
      rfl
  · exact fits_tok hP.a_valid hP.a_length
  · refine fits_runP ?_ ?_
    · intro p hp
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with (rfl | hp) | rfl | rfl
      · exact plain_out (mem_plain.2 (Or.inr (Or.inl rfl)))
      · exact mid_out_Q hP hp
      · exact plain_out (mem_plain.2 (Or.inr (Or.inr (Or.inl rfl))))
      · exact plain_out (mem_plain.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · have := hP.mid_zero_length
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  · exact fits_tok (f₁Tokens_valid J) (altRun_length _ _ _ _ _)
  · exact fits_runP (fun p hp => plain_out (mem_plain.2 (by simp [hp]))) (tether₁_length J)
  · exact sepPart_fits J
  · exact fits_runP (fun p hp => plain_out (mem_plain.2 (by simp [hp]))) (tether₂_length J)
  · exact fits_tok (f₂Tokens_valid J) (altRun_length _ _ _ _ _)
  · refine flatMap fun i _ => app ?_ ?_
    · refine fits_runP (fun p hp => mid_out_Q hP hp) ?_
      have := hP.mid_succ_length i
      omega
    · exact fits_tok (itemTokens_valid hP.placed i) (altRun_length _ _ _ _ _)

end ProteinFolding.Shelf
