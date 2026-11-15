import ProteinFolding.Tetrahedral.NearFieldCappedUnitData

/-! The terminal word and a list of capped units select the actual columns
for every routed exit/entry pair. Borrowed caps retain their given adjacency. -/

namespace ProteinFolding.Tetrahedral.NearField

def cappedRoutingUnits {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m) :
    Fin (n + 1) → PositionedWord := Fin.cases terminal (fun j => (bs j).piece)

@[simp] theorem cappedRoutingUnits_zero {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m) :
    cappedRoutingUnits terminal bs 0 = terminal := rfl

@[simp] theorem cappedRoutingUnits_succ {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m)
    (j : Fin n) : cappedRoutingUnits terminal bs j.succ = (bs j).piece := rfl

def cappedUnitColumnCatalogue {m n : ℕ} (bs : Fin n → CappedUnit m) (terminalColumn : DanglingColumn m) :
    Option (Fin n × Bool) → DanglingColumn m
  | none => terminalColumn
  | some a => (bs a.1).column a.2

def routedPreviousUnit {n : ℕ} (r : Fin n) (_hr : r.val ≠ 0) : Fin n :=
  ⟨r.val - 1, by have h := r.isLt; omega⟩

def routedUnitColumnLabel {n : ℕ} (a : Fin n × Bool) : Option (Fin n × Bool) :=
  if a.2 then some (a.1, true)
  else if h : a.1.val = 0 then none else some (routedPreviousUnit a.1 h, false)

theorem routedUnitColumnLabel_true {n : ℕ} (r : Fin n) :
    routedUnitColumnLabel (r, true) = some (r, true) := rfl

theorem routedUnitColumnLabel_false_zero {n : ℕ} (r : Fin n) (hr : r.val = 0) :
    routedUnitColumnLabel (r, false) = none := by simp [routedUnitColumnLabel, hr]

theorem routedUnitColumnLabel_false_nonzero {n : ℕ} (r : Fin n) (hr : r.val ≠ 0) :
    routedUnitColumnLabel (r, false) = some (routedPreviousUnit r hr, false) := by
  simp [routedUnitColumnLabel, hr]

theorem routedUnitColumnLabel_injective (n : ℕ) : Function.Injective (@routedUnitColumnLabel n) := by
  rintro ⟨r, b⟩ ⟨s, c⟩ heq
  cases b <;> cases c
  · by_cases hr : r.val = 0
    · by_cases hs : s.val = 0
      · have hval : r.val = s.val := by omega
        have hrs : r = s := Fin.ext hval
        exact Prod.ext hrs rfl
      · rw [routedUnitColumnLabel_false_zero r hr, routedUnitColumnLabel_false_nonzero s hs] at heq
        cases heq
    · by_cases hs : s.val = 0
      · rw [routedUnitColumnLabel_false_nonzero r hr, routedUnitColumnLabel_false_zero s hs] at heq
        cases heq
      · rw [routedUnitColumnLabel_false_nonzero r hr, routedUnitColumnLabel_false_nonzero s hs] at heq
        have hv := congrArg (fun a : Fin n × Bool => a.1.val) (Option.some.inj heq)
        change r.val - 1 = s.val - 1 at hv
        have hval : r.val = s.val := by omega
        have hrs : r = s := Fin.ext hval
        exact Prod.ext hrs rfl
  · by_cases hr : r.val = 0
    · rw [routedUnitColumnLabel_false_zero r hr, routedUnitColumnLabel_true] at heq
      cases heq
    · rw [routedUnitColumnLabel_false_nonzero r hr, routedUnitColumnLabel_true] at heq
      have hb := congrArg Prod.snd (Option.some.inj heq)
      cases hb
  · by_cases hs : s.val = 0
    · rw [routedUnitColumnLabel_true, routedUnitColumnLabel_false_zero s hs] at heq
      cases heq
    · rw [routedUnitColumnLabel_true, routedUnitColumnLabel_false_nonzero s hs] at heq
      have hb := congrArg Prod.snd (Option.some.inj heq)
      cases hb
  · rw [routedUnitColumnLabel_true, routedUnitColumnLabel_true] at heq
    exact Option.some.inj heq

theorem routedUnitColumnLabel_ne_final {n : ℕ} (a : Fin n × Bool) (k : Fin n)
    (hk : k.val + 1 = n) : routedUnitColumnLabel a ≠ some (k, false) := by
  rcases a with ⟨r, b⟩
  cases b
  · by_cases hr : r.val = 0
    · rw [routedUnitColumnLabel_false_zero r hr]
      intro heq
      cases heq
    · rw [routedUnitColumnLabel_false_nonzero r hr]
      intro heq
      have hv := congrArg (fun a : Fin n × Bool => a.1.val) (Option.some.inj heq)
      change r.val - 1 = k.val at hv
      have h := r.isLt
      omega
  · rw [routedUnitColumnLabel_true]
    intro heq
    have hb := congrArg Prod.snd (Option.some.inj heq)
    cases hb

def selectedRoutedUnitColumn {m n : ℕ} (bs : Fin n → CappedUnit m) (terminalColumn : DanglingColumn m)
    (a : Fin n × Bool) : DanglingColumn m :=
  cappedUnitColumnCatalogue bs terminalColumn (routedUnitColumnLabel a)

theorem selectedRoutedUnitColumn_true {m n : ℕ} (bs : Fin n → CappedUnit m) (C : DanglingColumn m)
    (r : Fin n) : selectedRoutedUnitColumn bs C (r, true) = (bs r).entry := rfl

theorem selectedRoutedUnitColumn_false_zero {m n : ℕ} (bs : Fin n → CappedUnit m) (C : DanglingColumn m)
    (r : Fin n) (hr : r.val = 0) : selectedRoutedUnitColumn bs C (r, false) = C := by
  unfold selectedRoutedUnitColumn
  rw [routedUnitColumnLabel_false_zero r hr]
  rfl

theorem selectedRoutedUnitColumn_false_nonzero {m n : ℕ} (bs : Fin n → CappedUnit m) (C : DanglingColumn m)
    (r : Fin n) (hr : r.val ≠ 0) : selectedRoutedUnitColumn bs C (r, false) = (bs (routedPreviousUnit r hr)).exit := by
  unfold selectedRoutedUnitColumn
  rw [routedUnitColumnLabel_false_nonzero r hr]
  rfl

theorem cappedRoutingUnits_length_ge_two {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m)
    (ht : 2 ≤ terminal.word.length) : ∀ i, 2 ≤ (cappedRoutingUnits terminal bs i).word.length := by
  intro i
  exact @Fin.cases n (fun j : Fin (n + 1) => 2 ≤ (cappedRoutingUnits terminal bs j).word.length)
    ht (fun j => (bs j).length_ge_two) i

theorem cappedRoutingUnits_last_dangling {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m)
    (C : DanglingColumn m) (hterminal : terminal.last = C.seed) :
    ∀ i, IsDangling m (cappedRoutingUnits terminal bs i).last := by
  intro i
  refine @Fin.cases n (fun j : Fin (n + 1) => IsDangling m (cappedRoutingUnits terminal bs j).last)
    ?_ (fun j => (bs j).last_dangling) i
  change IsDangling m terminal.last
  rw [hterminal]
  exact C.seed_dangling

theorem cappedRoutingUnits_first_dangling {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m) :
    ∀ i, 0 < i.val → IsDangling m (cappedRoutingUnits terminal bs i).first := by
  intro i
  refine @Fin.cases n (fun j : Fin (n + 1) =>
    0 < j.val → IsDangling m (cappedRoutingUnits terminal bs j).first) ?_ (fun j => ?_) i
  · intro hi
    change 0 < 0 at hi
    omega
  · intro _
    exact (bs j).first_dangling

theorem selectedRoutedUnitColumn_adjacent {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m)
    (C : DanglingColumn m) (hterminal : terminal.last = C.seed) (a : Fin n × Bool) :
    tetrahedralLattice.Adj (routedCapSite (cappedRoutingUnits terminal bs) a)
      ((selectedRoutedUnitColumn bs C a).point 1) := by
  rcases a with ⟨r, b⟩
  cases b
  · change tetrahedralLattice.Adj (cappedRoutingUnits terminal bs r.castSucc).last _
    by_cases hr : r.val = 0
    · rw [selectedRoutedUnitColumn_false_zero bs C r hr]
      have hi : r.castSucc = (0 : Fin (n + 1)) := Fin.ext hr
      rw [hi, cappedRoutingUnits_zero, hterminal]
      exact C.point_adj 0
    · rw [selectedRoutedUnitColumn_false_nonzero bs C r hr]
      have hi : r.castSucc = (routedPreviousUnit r hr).succ := by
        apply Fin.ext
        change r.val = (r.val - 1) + 1
        omega
      rw [hi, cappedRoutingUnits_succ]
      exact (bs (routedPreviousUnit r hr)).last_adjacent
  · rw [selectedRoutedUnitColumn_true]
    exact (bs r).first_adjacent

theorem selectedRoutedUnitColumn_seed_injective {m n : ℕ} (bs : Fin n → CappedUnit m) (C : DanglingColumn m)
    (hcat : Function.Injective (fun a => (cappedUnitColumnCatalogue bs C a).seed)) :
    Function.Injective (fun a => (selectedRoutedUnitColumn bs C a).seed) :=
  hcat.comp (routedUnitColumnLabel_injective n)

def selectedUnitWireColumn {m n : ℕ} (bs : Fin n → CappedUnit m) (C : DanglingColumn m)
    (e : FarField.Pairing (2 * n) n) (a : Fin (2 * n)) : DanglingColumn m :=
  selectedRoutedUnitColumn bs C (e a)

theorem selectedUnitWireColumn_seed_injective {m n : ℕ} (bs : Fin n → CappedUnit m) (C : DanglingColumn m)
    (e : FarField.Pairing (2 * n) n)
    (hcat : Function.Injective (fun a => (cappedUnitColumnCatalogue bs C a).seed)) :
    Function.Injective (fun a => (selectedUnitWireColumn bs C e a).seed) :=
  (selectedRoutedUnitColumn_seed_injective bs C hcat).comp e.injective

theorem selectedUnitWireColumn_second {m n : ℕ} (bs : Fin n → CappedUnit m) (C : DanglingColumn m)
    (e : FarField.Pairing (2 * n) n) (r : Fin n) :
    selectedUnitWireColumn bs C e (e.second r) = (bs r).entry := by
  simpa only [selectedUnitWireColumn, FarField.Pairing.second, Equiv.apply_symm_apply] using
    selectedRoutedUnitColumn_true bs C r

theorem selectedUnitWireColumn_first_zero {m n : ℕ} (bs : Fin n → CappedUnit m) (C : DanglingColumn m)
    (e : FarField.Pairing (2 * n) n) (r : Fin n) (hr : r.val = 0) :
    selectedUnitWireColumn bs C e (e.first r) = C := by
  simpa only [selectedUnitWireColumn, FarField.Pairing.first, Equiv.apply_symm_apply] using
    selectedRoutedUnitColumn_false_zero bs C r hr

theorem selectedUnitWireColumn_first_nonzero {m n : ℕ} (bs : Fin n → CappedUnit m) (C : DanglingColumn m)
    (e : FarField.Pairing (2 * n) n) (r : Fin n) (hr : r.val ≠ 0) :
    selectedUnitWireColumn bs C e (e.first r) = (bs (routedPreviousUnit r hr)).exit := by
  simpa only [selectedUnitWireColumn, FarField.Pairing.first, Equiv.apply_symm_apply] using
    selectedRoutedUnitColumn_false_nonzero bs C r hr

theorem selectedUnitWireColumn_adjacent {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m)
    (C : DanglingColumn m) (hterminal : terminal.last = C.seed) (e : FarField.Pairing (2 * n) n)
    (a : Fin (2 * n)) :
    tetrahedralLattice.Adj (wireCapSite (cappedRoutingUnits terminal bs) e a)
      ((selectedUnitWireColumn bs C e a).point 1) :=
  selectedRoutedUnitColumn_adjacent terminal bs C hterminal (e a)

theorem cappedRoutingUnits_wireCapSite_dangling {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m)
    (C : DanglingColumn m) (hterminal : terminal.last = C.seed) (e : FarField.Pairing (2 * n) n)
    (a : Fin (2 * n)) : IsDangling m (wireCapSite (cappedRoutingUnits terminal bs) e a) :=
  routedCapSite_dangling m (cappedRoutingUnits terminal bs)
    (cappedRoutingUnits_last_dangling terminal bs C hterminal)
    (cappedRoutingUnits_first_dangling terminal bs) (e a)

theorem cappedRoutingUnits_wireCapSite_injective {m n : ℕ} (terminal : PositionedWord) (bs : Fin n → CappedUnit m)
    (ht : 2 ≤ terminal.word.length) (e : FarField.Pairing (2 * n) n)
    (hpair : ∀ i j, i ≠ j → WordsDisjoint (cappedRoutingUnits terminal bs i) (cappedRoutingUnits terminal bs j)) :
    Function.Injective (wireCapSite (cappedRoutingUnits terminal bs) e) :=
  wireCapSite_injective (cappedRoutingUnits terminal bs) e hpair (cappedRoutingUnits_length_ge_two terminal bs ht)

theorem selectedUnitWireColumn_property {m n : ℕ} (bs : Fin n → CappedUnit m) (C : DanglingColumn m)
    (e : FarField.Pairing (2 * n) n) (P : DanglingColumn m → Prop)
    (hP : ∀ a, P (cappedUnitColumnCatalogue bs C a)) (a : Fin (2 * n)) :
    P (selectedUnitWireColumn bs C e a) := hP (routedUnitColumnLabel (e a))

end ProteinFolding.Tetrahedral.NearField
