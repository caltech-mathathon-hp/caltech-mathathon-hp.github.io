import ProteinFolding.Tetrahedral.ReductionDimerProvenanceConcrete
import ProteinFolding.Tetrahedral.ReductionDimerProvenanceInclusions

namespace ProteinFolding.Tetrahedral.ReductionDimerProvenance

def separatorExitOffset (p : ConstructionParameters) (k : ℕ) : ℕ :=
  2 + p.entryTether k + 7 + p.exitTether k

def EntryExitOffsets (p : ConstructionParameters) (k : ℕ) {S : Sequence}
    (c : DimerCatalogue ReductionChainTag S) : Prop :=
  ∃ i j, c.q i = 1 ∧ c.q j = 3 ∧ c.tag i = .entry k ∧ c.tag j = .exit k ∧
    (c.pre i).length = 0 ∧ (c.pre j).length = separatorExitOffset p k

theorem entryExit_cast (p : ConstructionParameters) (k : ℕ) {S T : Sequence}
    (c : DimerCatalogue ReductionChainTag S) (h : S = T) (hc : EntryExitOffsets p k c) :
    EntryExitOffsets p k (c.cast h) := by cases h; exact hc

theorem separator_offsets (p : ConstructionParameters) (items : List ℕ) (k : ℕ) (hk : k ≤ p.bins) :
    EntryExitOffsets p k (separatorBody p items k hk).catalogue := by
  dsimp only [separatorBody]
  apply entryExit_cast
  refine ⟨Sum.inl (Sum.inl ()), Sum.inr (Sum.inr ()), rfl, rfl, rfl, rfl, rfl, ?_⟩
  have he : 2 ≤ p.entryTether k := by unfold ConstructionParameters.entryTether; omega
  have hx : 2 ≤ p.exitTether k := by unfold ConstructionParameters.exitTether; omega
  simp only [DimerCatalogue.append, DimerCatalogue.prependP, DimerCatalogue.chain,
    DimerCatalogue.silent, List.length_append, List.length_replicate, List.length_nil,
    capWord, dimerChain, repeatWord, List.length_cons, Nat.add_zero, separatorExitOffset]
  omega

theorem separatorBody_mem (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) (k : ℕ) (hk : k ≤ p.bins) :
    separatorBody p items k hk ∈ bodies p items bulkLengths hbulk := by
  have hkr : k ∈ List.range (p.bins + 1) := List.mem_range.mpr (by omega)
  have hm : separatorBody p items k hk ∈ (List.range (p.bins + 1)).attach.map
      (fun r => separatorBody p items r.val (by have h := List.mem_range.mp r.property; omega)) := by
    exact List.mem_map.mpr ⟨⟨k, hkr⟩, by simp, rfl⟩
  simp only [bodies, List.mem_append]
  tauto

theorem body_inclusion (p : ConstructionParameters) (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (v : CataloguedBody ReductionChainTag (ReductionChainTag.Admissible p items))
    (hv : v ∈ bodies p items bulkLengths hbulk) :
    ∃ pre post, p.reductionWord items bulkLengths gaps = pre ++ capWord v.body ++ post ∧
      Nonempty (DimerCatalogue.Inclusion v.catalogue (catalogue p items bulkLengths gaps hbulk).val pre.length) := by
  obtain ⟨pre, post, hfactor, ⟨e⟩⟩ := CataloguedBody.reduction_body_inclusion gaps
    (bodies p items bulkLengths hbulk) v hv
  have h : assembleReductionWord gaps ((bodies p items bulkLengths hbulk).map CataloguedBody.body) =
      p.reductionWord items bulkLengths gaps := by rw [bodies_map]; rfl
  have f : DimerCatalogue.Inclusion (CataloguedBody.reduction gaps (bodies p items bulkLengths hbulk)).val
      (catalogue p items bulkLengths gaps hbulk).val 0 := by
    exact DimerCatalogue.Inclusion.cast (b := (catalogue p items bulkLengths gaps hbulk).val) _ h
  refine ⟨pre, post, ?_, ?_⟩
  · rwa [h] at hfactor
  · simpa only [Nat.zero_add] using Nonempty.intro (e.trans f)

/-- The entry and exit anchors of each declared separator belong to the same
literal separator occurrence, with their exact global HH offsets. -/
theorem separator_witnesses (p : ConstructionParameters) (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) (k : ℕ) (hk : k ≤ p.bins) :
    let c := (catalogue p items bulkLengths gaps hbulk).val
    ∃ (pre post : Sequence) (iE iX : c.Index),
      p.reductionWord items bulkLengths gaps = pre ++ capWord (p.separatorWord k) ++ post ∧
      c.q iE = 1 ∧ c.q iX = 3 ∧ c.tag iE = .entry k ∧ c.tag iX = .exit k ∧
      (c.pre iE).length = pre.length ∧ (c.pre iX).length = pre.length + separatorExitOffset p k := by
  dsimp only
  obtain ⟨pre, post, hfactor, ⟨e⟩⟩ := body_inclusion p items bulkLengths gaps hbulk
    (separatorBody p items k hk) (separatorBody_mem p items bulkLengths hbulk k hk)
  obtain ⟨i, j, hqi, hqj, hti, htj, hpi, hpj⟩ := separator_offsets p items k hk
  refine ⟨pre, post, e.map i, e.map j, ?_, (e.q_eq i).trans hqi, (e.q_eq j).trans hqj,
    (e.tag_eq i).trans hti, (e.tag_eq j).trans htj, ?_, ?_⟩
  · simpa only [separatorBody_body] using hfactor
  · rw [e.offset_eq, hpi, Nat.add_zero]
  · rw [e.offset_eq, hpj]

end ProteinFolding.Tetrahedral.ReductionDimerProvenance
