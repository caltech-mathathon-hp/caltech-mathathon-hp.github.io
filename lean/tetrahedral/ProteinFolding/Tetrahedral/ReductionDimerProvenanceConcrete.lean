import ProteinFolding.Tetrahedral.ReductionDimerProvenanceAssembly
import ProteinFolding.Tetrahedral.ReductionWordLinkers

namespace ProteinFolding.Tetrahedral

inductive ReductionChainTag where
  | entry (k : ℕ)
  | separator (k : ℕ)
  | exit (k : ℕ)
  | leftFiller
  | item (value : ℕ)
  | rightFiller
  | ring (r : ℕ)
  deriving DecidableEq

namespace ReductionChainTag

def size (p : ConstructionParameters) : ReductionChainTag → ℕ
  | .entry _ => 1
  | .separator _ => 2
  | .exit _ => 3
  | .leftFiller => p.leftFiller
  | .item s => p.itemDimers s
  | .rightFiller => p.rightFiller
  | .ring _ => 3 * (p.side - 2)

def Valid (p : ConstructionParameters) (items : List ℕ) : ReductionChainTag → Prop
  | .entry k | .separator k | .exit k => k ≤ p.bins
  | .item s => s ∈ items
  | .ring r => r < 3
  | .leftFiller | .rightFiller => True

def Admissible (p : ConstructionParameters) (items : List ℕ) (tag : ReductionChainTag) (q : ℕ) : Prop :=
  q = tag.size p ∧ tag.Valid p items

end ReductionChainTag

namespace ReductionDimerProvenance

open ReductionChainTag

theorem cap_merge_gap (u v : Sequence) (n : ℕ) :
    capWord u ++ (List.replicate n .P ++ capWord v) =
      capWord (u ++ List.replicate (n + 2) .P ++ v) := by
  simpa only [List.append_assoc, capWord, List.cons_append] using capped_words_merge_P_run u v n

noncomputable def separatorBody (p : ConstructionParameters) (items : List ℕ) (k : ℕ) (hk : k ≤ p.bins) :
    CataloguedBody ReductionChainTag (Admissible p items) := by
  let a := DimerCatalogue.chain (ReductionChainTag.entry k) 1
  let b := (DimerCatalogue.chain (ReductionChainTag.separator k) 2).prependP (p.entryTether k - 2)
  let c := (DimerCatalogue.chain (ReductionChainTag.exit k) 3).prependP (p.exitTether k - 2)
  have hab := DimerCatalogue.count_append_PP _ _ (DimerCatalogue.capped_ends_P (dimerChain 1))
    (DimerCatalogue.P_prefix_capped_starts (p.entryTether k - 2) (dimerChain 2))
  have hab_end : ∃ v, (capWord (dimerChain 1) ++
      (List.replicate (p.entryTether k - 2) .P ++ capWord (dimerChain 2))) = v ++ [.P] := by
    obtain ⟨v, hv⟩ := DimerCatalogue.P_prefix_capped_ends (p.entryTether k - 2) (dimerChain 2)
    exact ⟨capWord (dimerChain 1) ++ v, by rw [hv, List.append_assoc]⟩
  have habc := DimerCatalogue.count_append_PP _ _ hab_end
    (DimerCatalogue.P_prefix_capped_starts (p.exitTether k - 2) (dimerChain 3))
  let cat := (a.append b hab).append c habc
  have hentry : p.entryTether k - 2 + 2 = p.entryTether k := by unfold ConstructionParameters.entryTether; omega
  have hexit : p.exitTether k - 2 + 2 = p.exitTether k := by unfold ConstructionParameters.exitTether; omega
  have heq : (capWord (dimerChain 1) ++
      (List.replicate (p.entryTether k - 2) .P ++ capWord (dimerChain 2))) ++
      (List.replicate (p.exitTether k - 2) .P ++ capWord (dimerChain 3)) = capWord (p.separatorWord k) := by
    rw [cap_merge_gap, cap_merge_gap, hentry, hexit]
    simp only [ConstructionParameters.separatorWord, List.append_assoc]
  have ha : a.Satisfies (Admissible p items) := DimerCatalogue.satisfies_chain _ _ _ ⟨rfl, hk⟩
  have hb : b.Satisfies (Admissible p items) :=
    DimerCatalogue.satisfies_prependP _ _ _ (DimerCatalogue.satisfies_chain _ _ _ ⟨rfl, hk⟩)
  have hc : c.Satisfies (Admissible p items) :=
    DimerCatalogue.satisfies_prependP _ _ _ (DimerCatalogue.satisfies_chain _ _ _ ⟨rfl, hk⟩)
  exact ⟨p.separatorWord k, cat.cast heq,
    DimerCatalogue.satisfies_cast cat heq _
      (DimerCatalogue.satisfies_append _ _ _ _ (DimerCatalogue.satisfies_append _ _ _ _ ha hb) hc)⟩

@[simp] theorem separatorBody_body (p : ConstructionParameters) (items : List ℕ) (k : ℕ) (hk : k ≤ p.bins) :
    (separatorBody p items k hk).body = p.separatorWord k := rfl

theorem map_attach_val {α β : Type} (xs : List α) (f : α → β) :
    xs.attach.map (fun x => f x.val) = xs.map f := by
  change xs.attach.map (f ∘ Subtype.val) = xs.map f
  rw [← List.map_map, List.attach_map_subtype_val]

noncomputable def bodies (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) : List (CataloguedBody ReductionChainTag (Admissible p items)) :=
  [CataloguedBody.silent [.H] dimerStartCount_capped_single_H,
    CataloguedBody.silent [.H] dimerStartCount_capped_single_H,
    CataloguedBody.silent [.H] dimerStartCount_capped_single_H,
    CataloguedBody.silent (p.framePart1 ++ p.framePart2) (by rw [← p.frameWord_eq_cap, p.frameWord_dimerStartCount])] ++
  (List.range (p.bins + 1)).attach.map (fun k => separatorBody p items k.val (by have h := List.mem_range.mp k.property; omega)) ++
  [CataloguedBody.chain .leftFiller p.leftFiller ⟨rfl, trivial⟩] ++
  items.attach.map (fun s => CataloguedBody.chain (.item s.val) (p.itemDimers s.val) ⟨rfl, s.property⟩) ++
  [CataloguedBody.chain .rightFiller p.rightFiller ⟨rfl, trivial⟩] ++
  (List.range 3).attach.map (fun r => CataloguedBody.chain (.ring r.val) (3 * (p.side - 2)) ⟨rfl, List.mem_range.mp r.property⟩) ++
  bulkLengths.attach.map (fun n => CataloguedBody.silent (List.replicate n.val .H) (dimerStartCount_capped_long_H n.val (hbulk n.val n.property)))

theorem bodies_map (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) :
    (bodies p items bulkLengths hbulk).map CataloguedBody.body = p.reductionUnitBodies items bulkLengths := by
  simp only [bodies, List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def, CataloguedBody.silent, CataloguedBody.chain, separatorBody_body]
  rw [map_attach_val (List.range (p.bins + 1)) p.separatorWord,
    map_attach_val items (fun s => dimerChain (p.itemDimers s)),
    map_attach_val bulkLengths (fun n => List.replicate n Residue.H)]
  simp [ConstructionParameters.reductionUnitBodies, List.map_const]

noncomputable def catalogue (p : ConstructionParameters) (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) :
    {c : DimerCatalogue ReductionChainTag (p.reductionWord items bulkLengths gaps) // c.Satisfies (Admissible p items)} := by
  let c := CataloguedBody.reduction gaps (bodies p items bulkLengths hbulk)
  have h : assembleReductionWord gaps ((bodies p items bulkLengths hbulk).map CataloguedBody.body) =
      p.reductionWord items bulkLengths gaps := by rw [bodies_map]; rfl
  exact ⟨c.val.cast h, DimerCatalogue.satisfies_cast _ h _ c.property⟩

theorem small_size {p : ConstructionParameters} {items : List ℕ} (hpos : ∀ s ∈ items, 0 < s)
    (tag : ReductionChainTag) (q : ℕ) (h : Admissible p items tag q) :
    (q = 1 ↔ ∃ k, k ≤ p.bins ∧ tag = .entry k) ∧
    (q = 2 ↔ ∃ k, k ≤ p.bins ∧ tag = .separator k) ∧
    (q = 3 ↔ ∃ k, k ≤ p.bins ∧ tag = .exit k) := by
  rcases h with ⟨hq, ht⟩
  cases tag with
  | entry k => simp only [size] at hq; simp only [Valid] at ht; simp [hq, ht]
  | separator k => simp only [size] at hq; simp only [Valid] at ht; simp [hq, ht]
  | exit k => simp only [size] at hq; simp only [Valid] at ht; simp [hq, ht]
  | leftFiller => have hge := p.leftFiller_ge; simp only [size] at hq; simp; omega
  | rightFiller => have hge := p.rightFiller_ge; simp only [size] at hq; simp; omega
  | item s =>
    have hge := p.itemDimers_ge s (hpos s ht)
    simp only [size] at hq
    simp
    omega
  | ring r => have hge := p.side_ge; simp only [size] at hq; simp; omega

end ReductionDimerProvenance

end ProteinFolding.Tetrahedral
