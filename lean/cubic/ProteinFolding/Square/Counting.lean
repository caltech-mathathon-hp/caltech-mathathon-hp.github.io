import ProteinFolding.Square.LossRepresentation

/-! Double counting the four lattice edges incident with every H residue. -/

namespace ProteinFolding.Square

def Consecutive {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

instance decidableConsecutive {n : ℕ} (i j : Fin n) : Decidable (Consecutive i j) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem consecutive_symm {n : ℕ} (i j : Fin n) : Consecutive i j ↔ Consecutive j i :=
  or_comm

theorem consecutive_adj (S : Sequence) (f : Fold squareLattice S.length)
    {i j : Fin S.length} (h : Consecutive i j) : squareLattice.Adj (f.pos i) (f.pos j) := by
  rcases h with h | h
  · exact f.consecutive i j h
  · exact squareLattice.symm (f.consecutive j i h)

def backboneDarts (S : Sequence) : Finset (Fin S.length × Fin S.length) :=
  (hydrophobicIndices S ×ˢ Finset.univ).filter fun ij => Consecutive ij.1 ij.2

def contactDarts (S : Sequence) (f : Fold squareLattice S.length) :
    Finset (Fin S.length × Fin S.length) :=
  (hydrophobicIndices S ×ˢ hydrophobicIndices S).filter fun ij =>
    squareLattice.Adj (f.pos ij.1) (f.pos ij.2) ∧ ¬ Consecutive ij.1 ij.2

def interactionDarts (S : Sequence) (f : Fold squareLattice S.length) :
    Finset (Fin S.length × Fin S.length) :=
  (hydrophobicIndices S ×ˢ Finset.univ).filter fun ij =>
    squareLattice.Adj (f.pos ij.1) (f.pos ij.2) ∧
      (S.get ij.2 = Residue.H ∨ Consecutive ij.1 ij.2)

noncomputable def edgeDirection {p q : Site} (h : squareLattice.Adj p q) : Fin 4 :=
  Classical.choose (adj_step h)

theorem step_edgeDirection {p q : Site} (h : squareLattice.Adj p q) :
    step p (edgeDirection h) = q := Classical.choose_spec (adj_step h)

theorem interactionDarts_card (S : Sequence) (f : Fold squareLattice S.length) :
    (interactionDarts S f).card =
      ((hydrophobicIndices S ×ˢ (Finset.univ : Finset (Fin 4))) \ lossEdges S f).card := by
  classical
  have hm (a : Fin S.length × Fin S.length) : a ∈ interactionDarts S f ↔
      S.get a.1 = Residue.H ∧ squareLattice.Adj (f.pos a.1) (f.pos a.2) ∧
        (S.get a.2 = Residue.H ∨ Consecutive a.1 a.2) := by
    simp [interactionDarts, hydrophobicIndices]
  let g := fun a (ha : a ∈ interactionDarts S f) =>
    (a.1, edgeDirection (hm a |>.mp ha).2.1)
  have hg a ha : step (f.pos a.1) (g a ha).2 = f.pos a.2 :=
    step_edgeDirection ((hm a).mp ha).2.1
  apply Finset.card_bij g
  · intro a ha
    obtain ⟨hh, _, hj⟩ := (hm a).1 ha
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩,
        Finset.mem_univ _⟩
    · intro hn
      obtain ⟨_, hH, hB⟩ := (mem_lossEdges S f _).1 hn
      rcases hj with hj | hj
      · exact hH a.2 hj (hg a ha).symm
      · exact hB a.2 hj (hg a ha).symm
  · intro a ha b hb he
    have hi := congrArg (fun z : Fin S.length × Fin 4 => z.1) he
    change a.1 = b.1 at hi
    have hd := congrArg Prod.snd he
    apply Prod.ext hi
    apply f.injective_pos
    rw [← hg a ha, ← hg b hb, hi, hd]
  · intro b hb
    obtain ⟨hH, hn⟩ := Finset.mem_sdiff.mp hb
    have hh : S.get b.1 = Residue.H := by simpa [hydrophobicIndices] using hH
    have hex : ∃ j, f.pos j = step (f.pos b.1) b.2 ∧
        (S.get j = Residue.H ∨ Consecutive b.1 j) := by
      by_contra h
      apply hn
      apply (mem_lossEdges S f b).2
      refine ⟨hh, ?_, ?_⟩
      · intro j hj he
        exact h ⟨j, he, Or.inl hj⟩
      · intro j hj he
        exact h ⟨j, he, Or.inr hj⟩
    obtain ⟨j, hj, hc⟩ := hex
    have ha : (b.1, j) ∈ interactionDarts S f :=
      (hm _).2 ⟨hh, hj ▸ step_adj _ _, hc⟩
    refine ⟨(b.1, j), ha, Prod.ext rfl ?_⟩
    apply step_inj (f.pos b.1)
    exact (hg _ ha).trans hj

theorem interactionDarts_partition (S : Sequence) (f : Fold squareLattice S.length) :
    (interactionDarts S f).card = (backboneDarts S).card + (contactDarts S f).card := by
  classical
  have h₁ : (interactionDarts S f).filter (fun a => Consecutive a.1 a.2) = backboneDarts S := by
    ext a
    simp only [interactionDarts, backboneDarts, hydrophobicIndices,
      Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true]
    constructor
    · rintro ⟨⟨hh, _⟩, hc⟩; exact ⟨hh, hc⟩
    · rintro ⟨hh, hc⟩; exact ⟨⟨hh, consecutive_adj S f hc, Or.inr hc⟩, hc⟩
  have h₂ : (interactionDarts S f).filter (fun a => ¬ Consecutive a.1 a.2) = contactDarts S f := by
    ext a
    simp [interactionDarts, contactDarts, hydrophobicIndices]
    tauto
  rw [← h₁, ← h₂]
  exact (Finset.filter_card_add_filter_neg_card_eq_card _).symm

theorem four_mul_hydrophobicCount (S : Sequence) (f : Fold squareLattice S.length) :
    lossCount S f + (backboneDarts S).card + (contactDarts S f).card =
      4 * hydrophobicCount S := by
  have hs : lossEdges S f ⊆ hydrophobicIndices S ×ˢ (Finset.univ : Finset (Fin 4)) :=
    Finset.filter_subset _ _
  have hc := Finset.card_sdiff_add_card_eq_card hs
  rw [← interactionDarts_card, interactionDarts_partition] at hc
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hc
  change _ + lossCount S f = hydrophobicCount S * 4 at hc
  omega

theorem contactDarts_card (S : Sequence) (f : Fold squareLattice S.length) :
    (contactDarts S f).card = 2 * score S f := by
  classical
  have hlo : (contactDarts S f).filter (fun a => a.1 < a.2) = hhContacts S f := by
    ext a
    simp only [contactDarts, hydrophobicIndices, hhContacts, hhBonds,
      Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    simp only [Consecutive, not_or]
    constructor
    · rintro ⟨⟨⟨h₁, h₂⟩, ha, hn, _⟩, hlt⟩
      exact ⟨⟨hlt, h₁, h₂, ha⟩, hn⟩
    · rintro ⟨⟨hlt, h₁, h₂, ha⟩, hn⟩
      exact ⟨⟨⟨h₁, h₂⟩, ha, hn, by omega⟩, hlt⟩
  have hhi : ((contactDarts S f).filter (fun a => ¬ a.1 < a.2)).card = score S f := by
    change _ = (hhContacts S f).card
    apply Finset.card_bij (fun a _ => (a.2, a.1))
    · intro a ha
      simp only [Finset.mem_filter, contactDarts, hydrophobicIndices, Finset.mem_product,
        Finset.mem_univ, true_and] at ha
      obtain ⟨⟨⟨h₁, h₂⟩, hadj, hnc⟩, hn⟩ := ha
      have hne : a.1 ≠ a.2 := by
        intro he; exact squareLattice.loopless _ (he ▸ hadj)
      have hlt : a.2 < a.1 := by omega
      simp only [hhContacts, hhBonds, Finset.mem_filter, Finset.mem_product,
        Finset.mem_univ, true_and]
      exact ⟨⟨hlt, h₂, h₁, squareLattice.symm hadj⟩, fun h => hnc (Or.inr h)⟩
    · intro a _ b _ he
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    · intro a ha
      have hlo' : a ∈ (contactDarts S f).filter (fun a => a.1 < a.2) := hlo ▸ ha
      simp only [Finset.mem_filter, contactDarts, hydrophobicIndices, Finset.mem_product,
        Finset.mem_univ, true_and] at hlo'
      obtain ⟨⟨⟨h₁, h₂⟩, hadj, hnc⟩, hlt⟩ := hlo'
      refine ⟨(a.2, a.1), ?_, rfl⟩
      simp only [Finset.mem_filter, contactDarts, hydrophobicIndices, Finset.mem_product,
        Finset.mem_univ, true_and]
      exact ⟨⟨⟨h₂, h₁⟩, squareLattice.symm hadj,
        fun h => hnc ((consecutive_symm _ _).1 h)⟩, by omega⟩
  have hc := Finset.filter_card_add_filter_neg_card_eq_card
    (s := contactDarts S f) (fun a => a.1 < a.2)
  rw [hlo, hhi] at hc
  change score S f + score S f = _ at hc
  omega

/-- Count H chain ends with multiplicity: a singleton H has two ends. -/
def hydrophobicEnds (S : Sequence) : ℕ :=
  ((hydrophobicIndices S).filter fun i => i.val = 0).card +
    ((hydrophobicIndices S).filter fun i => i.val + 1 = S.length).card

theorem backbone_forward_card (S : Sequence) :
    ((backboneDarts S).filter (fun a => a.1.val + 1 = a.2.val)).card =
      ((hydrophobicIndices S).filter (fun i => i.val + 1 < S.length)).card := by
  apply Finset.card_bij (fun a _ => a.1)
  · intro a ha
    simp only [Finset.mem_filter, backboneDarts, Finset.mem_product, Finset.mem_univ,
      and_true] at ha ⊢
    exact ⟨ha.1.1, by have := a.2.isLt; omega⟩
  · intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    exact Prod.ext he (Fin.ext (by simp [← ha', ← hb', he]))
  · intro i hi
    obtain ⟨hh, ht⟩ := Finset.mem_filter.mp hi
    refine ⟨(i, ⟨i.val + 1, ht⟩), ?_, rfl⟩
    simp [backboneDarts, hh, Consecutive]

theorem backbone_backward_card (S : Sequence) :
    ((backboneDarts S).filter (fun a => ¬ a.1.val + 1 = a.2.val)).card =
      ((hydrophobicIndices S).filter (fun i => 0 < i.val)).card := by
  apply Finset.card_bij (fun a _ => a.1)
  · intro a ha
    simp only [Finset.mem_filter, backboneDarts, Finset.mem_product, Finset.mem_univ,
      and_true] at ha ⊢
    obtain ⟨⟨hh, hc⟩, hn⟩ := ha
    exact ⟨hh, by unfold Consecutive at hc; omega⟩
  · intro a ha b hb he
    simp only [Finset.mem_filter, backboneDarts, Finset.mem_product, Finset.mem_univ,
      and_true, Consecutive] at ha hb
    apply Prod.ext he
    apply Fin.ext
    have hv := congrArg Fin.val he
    omega
  · intro i hi
    obtain ⟨hh, ht⟩ := Finset.mem_filter.mp hi
    have hj : i.val - 1 < S.length := by have := i.isLt; omega
    refine ⟨(i, ⟨i.val - 1, hj⟩), ?_, rfl⟩
    simp only [Finset.mem_filter, backboneDarts, Finset.mem_product, Finset.mem_univ,
      and_true, Consecutive]
    exact ⟨⟨hh, Or.inr (by omega)⟩, by omega⟩

theorem backboneDarts_card (S : Sequence) :
    (backboneDarts S).card + hydrophobicEnds S = 2 * hydrophobicCount S := by
  have hc := Finset.filter_card_add_filter_neg_card_eq_card
    (s := backboneDarts S) (fun a => a.1.val + 1 = a.2.val)
  rw [backbone_forward_card, backbone_backward_card] at hc
  have hf := Finset.filter_card_add_filter_neg_card_eq_card
    (s := hydrophobicIndices S) (fun i => 0 < i.val)
  have hl := Finset.filter_card_add_filter_neg_card_eq_card
    (s := hydrophobicIndices S) (fun i => i.val + 1 < S.length)
  have hf' : (hydrophobicIndices S).filter (fun i => ¬ 0 < i.val) =
      (hydrophobicIndices S).filter (fun i => i.val = 0) := by
    congr 1; funext i; exact propext (by omega)
  have hl' : (hydrophobicIndices S).filter (fun i => ¬ i.val + 1 < S.length) =
      (hydrophobicIndices S).filter (fun i => i.val + 1 = S.length) := by
    congr 1; funext i; apply propext; have := i.isLt; omega
  rw [hf'] at hf
  rw [hl'] at hl
  unfold hydrophobicEnds hydrophobicCount
  omega

/-- General identity, valid also for empty words and H endpoints. -/
theorem score_loss_identity (S : Sequence) (f : Fold squareLattice S.length) :
    2 * score S f + lossCount S f = 2 * hydrophobicCount S + hydrophobicEnds S := by
  have h := four_mul_hydrophobicCount S f
  rw [contactDarts_card] at h
  have hb := backboneDarts_card S
  omega

/-- The paper's endpoint convention; vacuous for an empty word. -/
def PEndpoints (S : Sequence) : Prop :=
  ∀ i : Fin S.length, i.val = 0 ∨ i.val + 1 = S.length → S.get i = Residue.P

theorem hydrophobicEnds_eq_zero {S : Sequence} (h : PEndpoints S) : hydrophobicEnds S = 0 := by
  have hf : (hydrophobicIndices S).filter (fun i => i.val = 0) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi he
    have hh : S.get i = Residue.H := (Finset.mem_filter.mp hi).2
    have hp := h i (Or.inl he)
    rw [hh] at hp
    cases hp
  have hl : (hydrophobicIndices S).filter (fun i => i.val + 1 = S.length) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi he
    have hh : S.get i = Residue.H := (Finset.mem_filter.mp hi).2
    have hp := h i (Or.inr he)
    rw [hh] at hp
    cases hp
  simp [hydrophobicEnds, hf, hl]

theorem score_loss_identity_of_PEndpoints {S : Sequence} (h : PEndpoints S)
    (f : Fold squareLattice S.length) :
    2 * score S f + lossCount S f = 2 * hydrophobicCount S := by
  simpa [hydrophobicEnds_eq_zero h] using score_loss_identity S f

/-- Signed thresholds avoid truncated subtraction and cover negative bounds too. -/
theorem loss_le_iff_score_ge {S : Sequence} (h : PEndpoints S)
    (f : Fold squareLattice S.length) (E : ℤ) :
    (lossCount S f : ℤ) ≤ E ↔ (hydrophobicCount S : ℤ) - E / 2 ≤ (score S f : ℤ) := by
  have hid := score_loss_identity_of_PEndpoints h f
  omega

/-- Endpoint-corrected translation for arbitrary words, including a singleton H. -/
theorem loss_le_iff_score_ge_general (S : Sequence)
    (f : Fold squareLattice S.length) (E : ℤ) :
    (lossCount S f : ℤ) ≤ E ↔
      (hydrophobicCount S : ℤ) - (E - (hydrophobicEnds S : ℤ)) / 2 ≤ (score S f : ℤ) := by
  have hid := score_loss_identity S f
  omega

theorem hpLossFold_iff_hpStringFold_general (S : Sequence) (E : ℤ) :
    HPLossFold S E ↔ HPStringFold S
      ((hydrophobicCount S : ℤ) - (E - (hydrophobicEnds S : ℤ)) / 2) := by
  unfold HPLossFold HPStringFold
  exact exists_congr (fun f => loss_le_iff_score_ge_general S f E)

theorem hpLossFold_iff_hpStringFold {S : Sequence} (h : PEndpoints S) (E : ℤ) :
    HPLossFold S E ↔ HPStringFold S ((hydrophobicCount S : ℤ) - E / 2) := by
  unfold HPLossFold HPStringFold
  exact exists_congr (fun f => loss_le_iff_score_ge h f E)

end ProteinFolding.Square
