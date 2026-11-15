import ProteinFolding.Tetrahedral.FrameForcingChainWords

/-! Each literal capped dimer-chain occurrence gives a concrete subfamily
of the actual HH pairs, connected by the actual exterior P3 links. -/

namespace ProteinFolding.Tetrahedral

def factorDimerOccurrence (S pre post : Sequence) (q : ℕ)
    (heq : S = pre ++ capWord (dimerChain q) ++ post) (i : Fin q) : DimerOccurrence S := by
  let r := pre.length + 5 * i.val
  have hstart : IsDimerStart S r :=
    IsDimerStart.of_factor S pre (capWord (dimerChain q)) post heq (5 * i.val) (capped_dimer_start q i.val i.isLt)
  have hbound := (List.getElem?_eq_some_iff.mp hstart.1).choose
  exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbound, hstart⟩⟩

def factorDimerPairs (S : Sequence) (f : Fold tetrahedralLattice S.length) (pre post : Sequence) (q : ℕ)
    (heq : S = pre ++ capWord (dimerChain q) ++ post) : FinitePairFamily (Fin q) Site where
  point a := (foldDimerPairs S f).point (factorDimerOccurrence S pre post q heq a.1, a.2)
  injective := by
    rintro ⟨i, b⟩ ⟨j, c⟩ he
    have hpair := (foldDimerPairs S f).injective he
    have hb := congrArg Prod.snd hpair
    have hi := congrArg (fun a => a.1.val) hpair
    change pre.length + 5 * i.val = pre.length + 5 * j.val at hi
    have hij : i = j := by apply Fin.ext; omega
    exact Prod.ext hij hb

theorem factorDimerPairs_subset (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (pre post : Sequence) (q : ℕ) (heq : S = pre ++ capWord (dimerChain q) ++ post) :
    (factorDimerPairs S f pre post q heq).covered ⊆ (foldDimerPairs S f).covered := by
  intro x hx
  obtain ⟨⟨i, b⟩, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨(factorDimerOccurrence S pre post q heq i, b), Finset.mem_univ _, rfl⟩

theorem factorDimerPairs_point (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsupport : hSupport S f = octahedron m) (pre post : Sequence) (q : ℕ)
    (heq : S = pre ++ capWord (dimerChain q) ++ post) (i : Fin q) (b : Bool) :
    (factorDimerPairs S f pre post q heq).point (i, b) =
      (OctWordPath.ofFoldOccurrence f m hsupport pre (capWord (dimerChain q)) post heq).site
        (5 * i.val + if b then 2 else 1) := by
  have hstart := dimerOccurrence_data (factorDimerOccurrence S pre post q heq i)
  have hbound := (List.getElem?_eq_some_iff.mp hstart.2.2.2).choose
  change pre.length + 5 * i.val + 3 < S.length at hbound
  cases b <;> dsimp only [factorDimerPairs, foldDimerPairs, dimerResidueIndex,
    factorDimerOccurrence, OctWordPath.ofFoldOccurrence]
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals rw [foldSiteAt_eq f _ (by omega)]
  all_goals congr 1

theorem factorDimerPairs_link (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsupport : hSupport S f = octahedron m) (pre post : Sequence) (q : ℕ)
    (heq : S = pre ++ capWord (dimerChain q) ++ post) (i : ℕ) (hi : i + 1 < q) :
    OctTriangularNeighbours m
      ((factorDimerPairs S f pre post q heq).point (⟨i, by omega⟩, true))
      ((factorDimerPairs S f pre post q heq).point (⟨i + 1, hi⟩, false)) := by
  let P := OctWordPath.ofFoldOccurrence f m hsupport pre (capWord (dimerChain q)) post heq
  rw [factorDimerPairs_point S f m hsupport, factorDimerPairs_point S f m hsupport]
  simp only [↓reduceIte, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
  obtain ⟨hH₀, hH₄, hP⟩ := capped_dimer_P3 q i hi
  have hbound := (List.getElem?_eq_some_iff.mp hH₄).choose
  have hlink := P.P3_link (5 * i + 2) (by omega) hH₀
    (by simpa only [Nat.add_assoc] using hH₄) hP
  exact exterior_P3_link_triangular m hlink

theorem factorDimerPairs_component_card (S : Sequence) (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsupport : hSupport S f = octahedron m) (pre post : Sequence) (q : ℕ)
    (heq : S = pre ++ capWord (dimerChain q) ++ post) (V W : Finset Site)
    (hsub : (foldDimerPairs S f).covered ⊆ V)
    (hclosedA : ∀ x ∈ W, ∀ y ∈ V, tetrahedralLattice.Adj x y → y ∈ W)
    (hclosedT : ∀ x ∈ W, ∀ y ∈ V, OctTriangularNeighbours m x y → y ∈ W)
    (hmeet : ∃ i b, (factorDimerPairs S f pre post q heq).point (i, b) ∈ W) : 2 * q ≤ W.card := by
  apply (factorDimerPairs S f pre post q heq).chain_component_card q V W
    ((factorDimerPairs_subset S f pre post q heq).trans hsub)
    (fun i => foldDimerPairs_adjacent S f (factorDimerOccurrence S pre post q heq i))
    (factorDimerPairs_link S f m hsupport pre post q heq) hclosedA hclosedT hmeet

end ProteinFolding.Tetrahedral
