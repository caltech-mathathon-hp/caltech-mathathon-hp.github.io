import ProteinFolding.Cubic.Proofs.PackingGeometryExterior
import ProteinFolding.Cubic.Proofs.PackingGeometryPaths

/-! Lifting an H path to the literal E_t=(P-H-P)^t word from compatible
exterior attachments. Local attachment distinctness suffices: an exterior cube
site has only one neighbour inside the cube, so P sites belonging to distinct
H sites cannot collide. Global injectivity is therefore proved, not assumed.
Choosing the attachments greedily is a separate finite-label construction. -/

namespace ProteinFolding.CubicPackingLift

open CubicPacking CubicPackingGeometry CubicCertificates

def decoration {t : ℕ} (base : Fold cubicLattice t) (before after : Fin t → Site)
    (k : Fin t) : Fin 3 → Site
  | 0 => before k
  | 1 => base.pos k
  | 2 => after k

theorem decoration_outside {t : ℕ} (base : Fold cubicLattice t) (before after : Fin t → Site)
    (a : Site) (n : ℕ) (hbefore : ∀ k, before k ∉ cube a n) (hafter : ∀ k, after k ∉ cube a n)
    (k : Fin t) (r : Fin 3) (hr : r ≠ 1) : decoration base before after k r ∉ cube a n := by
  fin_cases r
  · exact hbefore k
  · exact False.elim (hr rfl)
  · exact hafter k

theorem decoration_adj_owner {t : ℕ} (base : Fold cubicLattice t) (before after : Fin t → Site)
    (hbefore : ∀ k, cubicLattice.Adj (before k) (base.pos k))
    (hafter : ∀ k, cubicLattice.Adj (base.pos k) (after k))
    (k : Fin t) (r : Fin 3) (hr : r ≠ 1) :
    cubicLattice.Adj (decoration base before after k r) (base.pos k) := by
  fin_cases r
  · exact hbefore k
  · exact False.elim (hr rfl)
  · exact (hafter k).symm

theorem decoration_owner_eq {t : ℕ} (base : Fold cubicLattice t) (before after : Fin t → Site)
    (a : Site) (n : ℕ) (hinside : ∀ k, base.pos k ∈ cube a n)
    (hbefore : ∀ k, before k ∉ cube a n) (hafter : ∀ k, after k ∉ cube a n)
    (hbeforeAdj : ∀ k, cubicLattice.Adj (before k) (base.pos k))
    (hafterAdj : ∀ k, cubicLattice.Adj (base.pos k) (after k))
    (k l : Fin t) (r s : Fin 3)
    (he : decoration base before after k r = decoration base before after l s) : base.pos k = base.pos l := by
  by_cases hr : r = 1
  · subst r
    by_cases hs : s = 1
    · subst s; exact he
    · have hout := decoration_outside base before after a n hbefore hafter l s hs
      have hin : decoration base before after l s ∈ cube a n := by rw [← he]; exact hinside k
      exact False.elim (hout hin)
  · by_cases hs : s = 1
    · subst s
      have hout := decoration_outside base before after a n hbefore hafter k r hr
      have hin : decoration base before after k r ∈ cube a n := by rw [he]; exact hinside l
      exact False.elim (hout hin)
    · exact cube_exterior_neighbour_unique a n (decoration base before after k r)
        (base.pos k) (base.pos l)
        (decoration_outside base before after a n hbefore hafter k r hr)
        (hinside k) (hinside l)
        (decoration_adj_owner base before after hbeforeAdj hafterAdj k r hr)
        (by rw [he]; exact decoration_adj_owner base before after hbeforeAdj hafterAdj l s hs)

theorem decoration_injective {t : ℕ} (base : Fold cubicLattice t) (before after : Fin t → Site)
    (a : Site) (n : ℕ) (hinside : ∀ k, base.pos k ∈ cube a n)
    (hbefore : ∀ k, before k ∉ cube a n) (hafter : ∀ k, after k ∉ cube a n)
    (hbeforeAdj : ∀ k, cubicLattice.Adj (before k) (base.pos k))
    (hafterAdj : ∀ k, cubicLattice.Adj (base.pos k) (after k))
    (hseparate : ∀ k, before k ≠ after k) :
    Function.Injective (fun p : Fin t × Fin 3 => decoration base before after p.1 p.2) := by
  rintro ⟨k, r⟩ ⟨l, s⟩ he
  have hk := base.injective_pos
    (decoration_owner_eq base before after a n hinside hbefore hafter hbeforeAdj hafterAdj k l r s he)
  cases hk
  have hb : before k ≠ base.pos k := by intro heq; apply hbefore k; rw [heq]; exact hinside k
  have ha : base.pos k ≠ after k := by intro heq; apply hafter k; rw [← heq]; exact hinside k
  have hba := hseparate k
  have hab : after k ≠ before k := Ne.symm hba
  have hrs : r = s := by fin_cases r <;> fin_cases s <;> simp_all [decoration]
  exact Prod.ext rfl hrs

def edgeBaseIndex (t : ℕ) (i : Fin (edgeWord t).length) : Fin t :=
  ⟨i.val / 3, by have hi := i.isLt; have hlen := edgeWord_length t; omega⟩

def edgeRole {t : ℕ} (i : Fin (edgeWord t).length) : Fin 3 := ⟨i.val % 3, by omega⟩

def edgeLiftPos (t : ℕ) (base : Fold cubicLattice t) (before after : Fin t → Site)
    (i : Fin (edgeWord t).length) : Site := decoration base before after (edgeBaseIndex t i) (edgeRole i)

theorem edgeLiftPos_injective (t : ℕ) (base : Fold cubicLattice t) (before after : Fin t → Site)
    (a : Site) (n : ℕ) (hinside : ∀ k, base.pos k ∈ cube a n)
    (hbefore : ∀ k, before k ∉ cube a n) (hafter : ∀ k, after k ∉ cube a n)
    (hbeforeAdj : ∀ k, cubicLattice.Adj (before k) (base.pos k))
    (hafterAdj : ∀ k, cubicLattice.Adj (base.pos k) (after k))
    (hseparate : ∀ k, before k ≠ after k) : Function.Injective (edgeLiftPos t base before after) := by
  intro i j he
  have hc : (edgeBaseIndex t i, edgeRole i) = (edgeBaseIndex t j, edgeRole j) := by
    apply decoration_injective base before after a n hinside hbefore hafter hbeforeAdj hafterAdj hseparate
    exact he
  have hq : i.val / 3 = j.val / 3 := congrArg (fun p : Fin t × Fin 3 => p.1.val) hc
  have hr : i.val % 3 = j.val % 3 := congrArg (fun p : Fin t × Fin 3 => p.2.val) hc
  apply Fin.ext
  omega

theorem edgeLiftPos_adjacent (t : ℕ) (base : Fold cubicLattice t) (before after : Fin t → Site)
    (hbefore : ∀ k, cubicLattice.Adj (before k) (base.pos k))
    (hafter : ∀ k, cubicLattice.Adj (base.pos k) (after k))
    (hlink : ∀ k l : Fin t, k.val + 1 = l.val → cubicLattice.Adj (after k) (before l))
    (i j : Fin (edgeWord t).length) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (edgeLiftPos t base before after i) (edgeLiftPos t base before after j) := by
  have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
  rcases hm with hm | hm | hm
  · have hj : j.val % 3 = 1 := by omega
    have hb : edgeBaseIndex t j = edgeBaseIndex t i := by apply Fin.ext; dsimp [edgeBaseIndex]; omega
    have hr : edgeRole i = 0 := Fin.ext hm
    have hs : edgeRole j = 1 := Fin.ext hj
    simpa only [edgeLiftPos, hr, hs, hb, decoration] using hbefore (edgeBaseIndex t i)
  · have hj : j.val % 3 = 2 := by omega
    have hb : edgeBaseIndex t j = edgeBaseIndex t i := by apply Fin.ext; dsimp [edgeBaseIndex]; omega
    have hr : edgeRole i = 1 := Fin.ext hm
    have hs : edgeRole j = 2 := Fin.ext hj
    simpa only [edgeLiftPos, hr, hs, hb, decoration] using hafter (edgeBaseIndex t i)
  · have hj : j.val % 3 = 0 := by omega
    have hb : (edgeBaseIndex t i).val + 1 = (edgeBaseIndex t j).val := by dsimp [edgeBaseIndex]; omega
    have hr : edgeRole i = 2 := Fin.ext hm
    have hs : edgeRole j = 0 := Fin.ext hj
    simpa only [edgeLiftPos, hr, hs, decoration] using hlink _ _ hb

/-- The full literal E_t fold from local exterior attachments. Only the
neighbouring attachments at a single H must be explicitly separated. -/
def edgeLift (t : ℕ) (base : Fold cubicLattice t) (before after : Fin t → Site)
    (a : Site) (n : ℕ) (hinside : ∀ k, base.pos k ∈ cube a n)
    (hbefore : ∀ k, before k ∉ cube a n) (hafter : ∀ k, after k ∉ cube a n)
    (hbeforeAdj : ∀ k, cubicLattice.Adj (before k) (base.pos k))
    (hafterAdj : ∀ k, cubicLattice.Adj (base.pos k) (after k))
    (hseparate : ∀ k, before k ≠ after k)
    (hlink : ∀ k l : Fin t, k.val + 1 = l.val → cubicLattice.Adj (after k) (before l)) :
    Fold cubicLattice (edgeWord t).length where
  pos := edgeLiftPos t base before after
  injective_pos := edgeLiftPos_injective t base before after a n hinside hbefore hafter hbeforeAdj hafterAdj hseparate
  consecutive := fun i j hij => edgeLiftPos_adjacent t base before after hbeforeAdj hafterAdj hlink i j hij

theorem edgeWord_residue_role (t : ℕ) (i : Fin (edgeWord t).length) :
    (edgeWord t).get i = if i.val % 3 = 1 then .H else .P := by
  have hi := i.isLt
  have hlen := edgeWord_length t
  have hblock : i.val / 3 < t := by omega
  have hrem : i.val % 3 < ([.P, .H, .P] : Sequence).length := by change i.val % 3 < 3; omega
  have he := repeatWord_getElem? [.P, .H, .P] t (i.val / 3) (i.val % 3) hblock hrem
  change (edgeWord t)[3 * (i.val / 3) + i.val % 3]? = ([.P, .H, .P] : Sequence)[i.val % 3]? at he
  rw [Nat.div_add_mod, List.getElem?_eq_getElem i.isLt] at he
  have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;> simpa [hm, List.get_eq_getElem] using he

def edgeHIndex (t : ℕ) (k : Fin t) : Fin (edgeWord t).length :=
  ⟨3 * k.val + 1, by have hk := k.isLt; have hlen := edgeWord_length t; omega⟩

theorem edgeLiftPos_HIndex (t : ℕ) (base : Fold cubicLattice t) (before after : Fin t → Site) (k : Fin t) :
    edgeLiftPos t base before after (edgeHIndex t k) = base.pos k := by
  have hb : edgeBaseIndex t (edgeHIndex t k) = k := by apply Fin.ext; dsimp [edgeBaseIndex, edgeHIndex]; omega
  have hr : edgeRole (edgeHIndex t k) = 1 := by apply Fin.ext; dsimp [edgeRole, edgeHIndex]; omega
  simp only [edgeLiftPos, hb, hr, decoration]

theorem edgeWord_H_iff (t : ℕ) (i : Fin (edgeWord t).length) :
    (edgeWord t).get i = .H ↔ i.val % 3 = 1 := by
  rw [edgeWord_residue_role]
  split_ifs <;> simp_all

theorem edgeLift_H_occupation (t : ℕ) (base : Fold cubicLattice t) (before after : Fin t → Site)
    (lifted : Fold cubicLattice (edgeWord t).length)
    (hpos : ∀ i, lifted.pos i = edgeLiftPos t base before after i) :
    hydrophobicSites (edgeWord t) lifted = Set.range base.pos := by
  ext p
  constructor
  · rintro ⟨i, hi, hip⟩
    have hm := (edgeWord_H_iff t i).mp hi
    have hr : edgeRole i = 1 := Fin.ext hm
    refine ⟨edgeBaseIndex t i, ?_⟩
    rw [hpos i] at hip
    simpa only [edgeLiftPos, hr, decoration] using hip
  · rintro ⟨k, hk⟩
    refine ⟨edgeHIndex t k, (edgeWord_H_iff t _).mpr ?_, ?_⟩
    · dsimp [edgeHIndex]
      omega
    · rw [hpos, edgeLiftPos_HIndex]
      exact hk

theorem edgeLiftPos_P_outside (t : ℕ) (base : Fold cubicLattice t) (before after : Fin t → Site)
    (a : Site) (n : ℕ) (hbefore : ∀ k, before k ∉ cube a n) (hafter : ∀ k, after k ∉ cube a n)
    (i : Fin (edgeWord t).length) (hi : (edgeWord t).get i = .P) :
    edgeLiftPos t base before after i ∉ cube a n := by
  have hr : edgeRole i ≠ 1 := by
    intro he
    have hm : i.val % 3 = 1 := congrArg Fin.val he
    have hh := (edgeWord_H_iff t i).mpr hm
    rw [hi] at hh
    contradiction
  exact decoration_outside base before after a n hbefore hafter _ _ hr

def edgeFirstIndex (t : ℕ) (ht : 0 < t) : Fin (edgeWord t).length :=
  ⟨0, by have hlen := edgeWord_length t; omega⟩

def edgeLastIndex (t : ℕ) (ht : 0 < t) : Fin (edgeWord t).length :=
  ⟨(edgeWord t).length - 1, by have hlen := edgeWord_length t; omega⟩

theorem edgeLiftPos_first (t : ℕ) (ht : 0 < t) (base : Fold cubicLattice t) (before after : Fin t → Site) :
    edgeLiftPos t base before after (edgeFirstIndex t ht) = before ⟨0, ht⟩ := by
  have hb : edgeBaseIndex t (edgeFirstIndex t ht) = ⟨0, ht⟩ := by
    apply Fin.ext
    simp [edgeBaseIndex, edgeFirstIndex]
  have hr : edgeRole (edgeFirstIndex t ht) = 0 := by apply Fin.ext; rfl
  simp only [edgeLiftPos, hb, hr, decoration]

theorem edgeLiftPos_last (t : ℕ) (ht : 0 < t) (base : Fold cubicLattice t) (before after : Fin t → Site) :
    edgeLiftPos t base before after (edgeLastIndex t ht) = after ⟨t - 1, by omega⟩ := by
  have hlen := edgeWord_length t
  have hb : edgeBaseIndex t (edgeLastIndex t ht) = ⟨t - 1, by omega⟩ := by
    apply Fin.ext
    change ((edgeWord t).length - 1) / 3 = t - 1
    omega
  have hr : edgeRole (edgeLastIndex t ht) = 2 := by
    apply Fin.ext
    change ((edgeWord t).length - 1) % 3 = 2
    omega
  simp only [edgeLiftPos, hb, hr, decoration]

end ProteinFolding.CubicPackingLift
