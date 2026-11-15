import ProteinFolding.Tetrahedral.FrameForcingSlotGuards

/-! Actual P3 links and a finite dimer-chain connectivity argument. A chain
that meets an isolated slot lies wholly in that slot. -/

namespace ProteinFolding.Tetrahedral

theorem OctWordPath.P3_link {m : ℕ} {word : Sequence} (P : OctWordPath m word)
    (i : ℕ) (hbound : i + 4 < word.length)
    (hH₀ : word[i]? = some .H) (hH₄ : word[i + 4]? = some .H)
    (hP : ∀ r, 0 < r → r < 4 → word[i + r]? = some .P) :
    ExteriorP3Link m (P.site i) (P.site (i + 4)) := by
  refine ⟨P.H_mem i (by omega) hH₀, P.H_mem (i + 4) hbound hH₄,
    P.site (i + 1), P.site (i + 2), P.site (i + 3),
    P.adjacent i (by omega), ?_, ?_, ?_,
    P.P_out _ (by omega) (hP 1 (by decide) (by decide)),
    P.P_out _ (by omega) (hP 2 (by decide) (by decide)),
    P.P_out _ (by omega) (hP 3 (by decide) (by decide)), ?_⟩
  · simpa only [Nat.add_assoc] using P.adjacent (i + 1) (by omega)
  · simpa only [Nat.add_assoc] using P.adjacent (i + 2) (by omega)
  · simpa only [Nat.add_assoc] using P.adjacent (i + 3) (by omega)
  · have hvec : (![P.site i, P.site (i + 1), P.site (i + 2), P.site (i + 3), P.site (i + 4)] : Fin 5 → Site) =
        fun r => P.site (i + r.val) := by
      funext r
      fin_cases r <;> rfl
    rw [hvec]
    intro a b heq
    apply Fin.ext
    have hindex := P.injective (i + a.val) (by omega) (i + b.val) (by omega) heq
    omega

theorem FinitePairFamily.chain_component_all (q : ℕ)
    (F : FinitePairFamily (Fin q) Site) (V W : Finset Site)
    (hsub : F.covered ⊆ V)
    (hadj : ∀ i, tetrahedralLattice.Adj (F.point (i, false)) (F.point (i, true)))
    (hlink : ∀ i : ℕ, ∀ hi : i + 1 < q,
      OctTriangularNeighbours m (F.point (⟨i, by omega⟩, true)) (F.point (⟨i + 1, hi⟩, false)))
    (hclosedA : ∀ x ∈ W, ∀ y ∈ V, tetrahedralLattice.Adj x y → y ∈ W)
    (hclosedT : ∀ x ∈ W, ∀ y ∈ V, OctTriangularNeighbours m x y → y ∈ W)
    (hmeet : ∃ i b, F.point (i, b) ∈ W) : F.covered ⊆ W := by
  have hinV (i : Fin q) (b : Bool) : F.point (i, b) ∈ V :=
    hsub (Finset.mem_image.mpr ⟨(i, b), Finset.mem_univ _, rfl⟩)
  have hpair (i : Fin q) : F.point (i, false) ∈ W ↔ F.point (i, true) ∈ W :=
    ⟨fun h => hclosedA _ h _ (hinV i true) (hadj i),
      fun h => hclosedA _ h _ (hinV i false) (hadj i).symm⟩
  obtain ⟨start, b, hstart⟩ := hmeet
  have hq : 0 < q := by have hs := start.isLt; omega
  have hstart' : F.point (start, false) ∈ W := by
    cases b with
    | false => exact hstart
    | true => exact (hpair start).mpr hstart
  have hstep (i : ℕ) (hi : i + 1 < q) :
      F.point (⟨i, by omega⟩, false) ∈ W ↔ F.point (⟨i + 1, hi⟩, false) ∈ W := by
    constructor
    · intro h
      exact hclosedT _ ((hpair ⟨i, by omega⟩).mp h) _ (hinV _ false) (hlink i hi)
    · intro h
      exact (hpair ⟨i, by omega⟩).mpr
        (hclosedT _ h _ (hinV _ true) (triangular_neighbours_symm (hlink i hi)))
  have hzero (i : ℕ) (hi : i < q) :
      F.point (⟨i, hi⟩, false) ∈ W ↔ F.point (⟨0, hq⟩, false) ∈ W := by
    induction i with
    | zero => rfl
    | succ i ih => exact (hstep i hi).symm.trans (ih (by omega))
  have hbase : F.point (⟨0, hq⟩, false) ∈ W := (hzero start.val start.isLt).mp hstart'
  intro x hx
  obtain ⟨⟨i, b⟩, _, rfl⟩ := Finset.mem_image.mp hx
  have hfalse := (hzero i.val i.isLt).mpr hbase
  cases b with
  | false => exact hfalse
  | true => exact (hpair i).mp hfalse

theorem FinitePairFamily.chain_component_card (q : ℕ)
    (F : FinitePairFamily (Fin q) Site) (V W : Finset Site)
    (hsub : F.covered ⊆ V)
    (hadj : ∀ i, tetrahedralLattice.Adj (F.point (i, false)) (F.point (i, true)))
    (hlink : ∀ i : ℕ, ∀ hi : i + 1 < q,
      OctTriangularNeighbours m (F.point (⟨i, by omega⟩, true)) (F.point (⟨i + 1, hi⟩, false)))
    (hclosedA : ∀ x ∈ W, ∀ y ∈ V, tetrahedralLattice.Adj x y → y ∈ W)
    (hclosedT : ∀ x ∈ W, ∀ y ∈ V, OctTriangularNeighbours m x y → y ∈ W)
    (hmeet : ∃ i b, F.point (i, b) ∈ W) : 2 * q ≤ W.card := by
  have hcard := Finset.card_le_card (F.chain_component_all q V W hsub hadj hlink hclosedA hclosedT hmeet)
  simpa only [F.covered_card, Fintype.card_fin] using hcard

end ProteinFolding.Tetrahedral
