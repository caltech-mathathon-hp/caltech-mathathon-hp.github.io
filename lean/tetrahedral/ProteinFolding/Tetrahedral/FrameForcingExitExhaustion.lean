import ProteinFolding.Tetrahedral.FrameForcingCatalogueSlots

/-! Three-dimer exit chains are exhausted by the already identified exit
slots. No order or incidence assumption is used. -/

namespace ProteinFolding.Tetrahedral

theorem exact_slot_family_exhausts {ι κ α : Type*} [Fintype ι] [Fintype κ] [DecidableEq α]
    (C : ι → Finset α) (q : ι → ℕ) (E : κ → Finset α) (t : ℕ)
    (hCcard : ∀ i, (C i).card = 2 * q i)
    (hCdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hEcard : ∀ k, (E k).card = 2 * t)
    (hEdisjoint : ∀ k l, k ≠ l → Disjoint (E k) (E l))
    (hexact : ∀ k, ∃ i, q i = t ∧ C i = E k)
    (hcount : (Finset.univ.filter (fun i => q i = t)).card = Fintype.card κ) :
    (Finset.univ.filter (fun i => q i = t)).biUnion C = Finset.univ.biUnion E := by
  classical
  let I := Finset.univ.filter (fun i => q i = t)
  have hsub : Finset.univ.biUnion E ⊆ I.biUnion C := by
    intro x hx
    obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i, hqi, heq⟩ := hexact k
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqi⟩, heq ▸ hxk⟩
  have hIcard : (I.biUnion C).card = (2 * t) * Fintype.card κ := by
    rw [disjoint_biUnion_fixed_card I C (2 * t)]
    · exact congrArg (fun n => (2 * t) * n) hcount
    · intro i hi
      rw [hCcard i, (Finset.mem_filter.mp hi).2]
    · intro i _ j _ hij
      exact hCdisjoint i j hij
  have hEunion : (Finset.univ.biUnion E).card = (2 * t) * Fintype.card κ := by
    rw [disjoint_biUnion_fixed_card Finset.univ E (2 * t)]
    · simp
    · intro k _
      exact hEcard k
    · intro k _ l _ hkl
      exact hEdisjoint k l hkl
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hIcard, hEunion])).symm

namespace ConstructionParameters

theorem actual_catalogue_exit_sites (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (pre post : Sequence) (heq : p.reductionWord items bulkLengths gaps = pre ++ p.frameWord ++ post)
    (F : ForcedFrameFamily p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq).toFold)
      p.frameGaps1 p.frameGaps2)
    {α : Type} (c : DimerCatalogue α (p.reductionWord items bulkLengths gaps))
    (hpositive : ∀ i, 0 < c.q i)
    (hcount₁ : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 1)).card = p.bins + 1)
    (hcount₃ : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 3)).card = p.bins + 1) :
    ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 3)).biUnion (c.chainSites f) =
      Finset.univ.biUnion (fun k : Fin (p.bins + 1) =>
        edgeBlock p.side F.second (2 * p.side - (10 * k.val + 13)) 6) := by
  letI := c.finiteIndex
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply exact_slot_family_exhausts (c.chainSites f) c.q
    (fun k : Fin (p.bins + 1) => edgeBlock p.side F.second (2 * p.side - (10 * k.val + 13)) 6) 3
    (c.chainSites_card f) (c.chainSites_disjoint f)
  · intro k
    exact edgeBlock_card p.side hm F.second _ _
  · intro k l hkl
    apply p.exit_slot_disjoint F.second k.val l.val (by omega) (by omega)
    exact fun he => hkl (Fin.ext he)
  · intro k
    exact p.actual_catalogue_exit_slot_chain items bulkLengths gaps htotal hbulk f hsupport hvertices
      pre post heq F c hpositive hcount₁ k.val (by omega)
  · simpa only [Fintype.card_fin] using hcount₃

end ConstructionParameters

end ProteinFolding.Tetrahedral
