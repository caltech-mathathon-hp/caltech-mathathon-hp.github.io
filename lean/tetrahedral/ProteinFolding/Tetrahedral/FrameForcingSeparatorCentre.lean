import ProteinFolding.Tetrahedral.ReductionDimerProvenanceSeparator

/-! The central HH--P3--HH chain is the actual declared size-two chain
inside the same literal separator occurrence. -/

namespace ProteinFolding.Tetrahedral.ReductionDimerProvenance

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

def CentreOffset (p : ConstructionParameters) (k : ℕ) {S : Sequence}
    (c : DimerCatalogue ReductionChainTag S) : Prop :=
  ∃ i, c.q i = 2 ∧ c.tag i = .separator k ∧
    (c.pre i).length = p.entryTether k + 2

theorem centre_cast (p : ConstructionParameters) (k : ℕ) {S T : Sequence}
    (c : DimerCatalogue ReductionChainTag S) (h : S = T) (hc : CentreOffset p k c) :
    CentreOffset p k (c.cast h) := by cases h; exact hc

theorem separator_centre_offset (p : ConstructionParameters) (items : List ℕ)
    (k : ℕ) (hk : k ≤ p.bins) :
    CentreOffset p k (separatorBody p items k hk).catalogue := by
  dsimp only [separatorBody]
  apply centre_cast
  refine ⟨Sum.inl (Sum.inr (Sum.inr ())), rfl, rfl, ?_⟩
  have he : 2 ≤ p.entryTether k := by unfold ConstructionParameters.entryTether; omega
  simp only [DimerCatalogue.append, DimerCatalogue.prependP, DimerCatalogue.chain,
    DimerCatalogue.silent, List.length_append, List.length_replicate, List.length_nil,
    capWord, dimerChain, repeatWord, List.length_cons, Nat.add_zero]
  omega

theorem separator_centre_witness (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (gaps : ℕ → ℕ) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) (k : ℕ) (hk : k ≤ p.bins) :
    let c := (catalogue p items bulkLengths gaps hbulk).val
    ∃ (pre post : Sequence) (i : c.Index),
      p.reductionWord items bulkLengths gaps = pre ++ capWord (p.separatorWord k) ++ post ∧
      c.q i = 2 ∧ c.tag i = .separator k ∧
      (c.pre i).length = pre.length + p.entryTether k + 2 := by
  dsimp only
  obtain ⟨pre, post, hfactor, ⟨e⟩⟩ := body_inclusion p items bulkLengths gaps hbulk
    (separatorBody p items k hk) (separatorBody_mem p items bulkLengths hbulk k hk)
  obtain ⟨i, hq, ht, hp⟩ := separator_centre_offset p items k hk
  refine ⟨pre, post, e.map i, ?_, (e.q_eq i).trans hq, (e.tag_eq i).trans ht, ?_⟩
  · simpa only [separatorBody_body] using hfactor
  · rw [e.offset_eq, hp]
    omega

end ProteinFolding.Tetrahedral.ReductionDimerProvenance
