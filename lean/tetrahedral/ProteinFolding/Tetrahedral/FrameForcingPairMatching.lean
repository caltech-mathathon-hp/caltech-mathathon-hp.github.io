import ProteinFolding.Tetrahedral.FrameForcingMatching
import ProteinFolding.Tetrahedral.Geometry

/-! Transport an actual family of disjoint HH pairs filling an isolated
finite path to PathMatching, so its unique alternating pairing applies. -/

namespace ProteinFolding.Tetrahedral.FinitePairFamily

variable {ι : Type*} [Fintype ι]

abbrev PairsIn (F : FinitePairFamily ι Site) (W : Finset Site) := {p : ι × Bool // F.point p ∈ W}

def flipIn (F : FinitePairFamily ι Site) (W : Finset Site)
    (hclosed : ∀ i, F.point (i, false) ∈ W ↔ F.point (i, true) ∈ W) : F.PairsIn W → F.PairsIn W :=
  fun p => ⟨(p.val.1, !p.val.2), by
    obtain ⟨⟨i, b⟩, hp⟩ := p
    cases b with
    | false => exact (hclosed i).mp hp
    | true => exact (hclosed i).mpr hp⟩

omit [Fintype ι] in
theorem flipIn_involutive (F : FinitePairFamily ι Site) (W : Finset Site)
    (hclosed : ∀ i, F.point (i, false) ∈ W ↔ F.point (i, true) ∈ W) :
    Function.Involutive (F.flipIn W hclosed) := by
  rintro ⟨⟨i, b⟩, hp⟩
  apply Subtype.ext
  cases b <;> rfl

noncomputable def pairsInEquiv (F : FinitePairFamily ι Site) (W : Finset Site) (hW : W ⊆ F.covered) :
    F.PairsIn W ≃ {x : Site // x ∈ W} :=
  Equiv.ofBijective (fun p => ⟨F.point p.val, p.property⟩) (by
    constructor
    · intro p q heq
      exact Subtype.ext (F.injective (congrArg Subtype.val heq))
    · intro x
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp (hW x.property)
      refine ⟨⟨p, by rw [hp]; exact x.property⟩, ?_⟩
      exact Subtype.ext hp)

omit [Fintype ι] in
theorem flipIn_adjacent (F : FinitePairFamily ι Site) (W : Finset Site)
    (hclosed : ∀ i, F.point (i, false) ∈ W ↔ F.point (i, true) ∈ W)
    (hadj : ∀ i, tetrahedralLattice.Adj (F.point (i, false)) (F.point (i, true)))
    (p : F.PairsIn W) : tetrahedralLattice.Adj (F.point p.val) (F.point (F.flipIn W hclosed p).val) := by
  obtain ⟨⟨i, b⟩, hp⟩ := p
  cases b with
  | false => exact hadj i
  | true => exact (hadj i).symm

noncomputable def pathMatching (F : FinitePairFamily ι Site) (W : Finset Site)
    (hW : W ⊆ F.covered)
    (hclosed : ∀ i, F.point (i, false) ∈ W ↔ F.point (i, true) ∈ W)
    (hadj : ∀ i, tetrahedralLattice.Adj (F.point (i, false)) (F.point (i, true)))
    (n : ℕ) (e : Fin n ≃ {x : Site // x ∈ W})
    (hpath : ∀ i j, tetrahedralLattice.Adj (e i).val (e j).val → i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    PathMatching n := by
  let t := e.trans (F.pairsInEquiv W hW).symm
  let mate : Fin n → Fin n := fun i => t.symm (F.flipIn W hclosed (t i))
  have hinv : Function.Involutive mate := by
    intro i
    dsimp only [mate]
    rw [t.apply_symm_apply, F.flipIn_involutive W hclosed, t.symm_apply_apply]
  have hpoint (i : Fin n) : F.point (t i).val = (e i).val := by
    have h := congrArg Subtype.val ((F.pairsInEquiv W hW).apply_symm_apply (e i))
    exact h
  refine ⟨mate, hinv, ?_⟩
  intro i
  have hmate : t (mate i) = F.flipIn W hclosed (t i) := t.apply_symm_apply _
  have hbond := F.flipIn_adjacent W hclosed hadj (t i)
  rw [← hmate, hpoint i, hpoint (mate i)] at hbond
  exact (hpath i (mate i) hbond).symm

end ProteinFolding.Tetrahedral.FinitePairFamily
