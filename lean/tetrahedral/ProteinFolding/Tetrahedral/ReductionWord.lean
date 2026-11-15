import ProteinFolding.Tetrahedral.FrameWordCounts

/-! Literal unit assembly. The bulk path lengths and the linker parity data
remain explicit inputs until their geometric constructions are formalized. -/

namespace ProteinFolding.Tetrahedral

def assembleCappedBodies (gaps : ℕ → ℕ) : ℕ → List Sequence → Sequence
  | _, [] => []
  | i, u :: us => List.replicate (gaps i) .P ++ capWord u ++ assembleCappedBodies gaps (i + 1) us

theorem assembleCappedBodies_starts_P (gaps : ℕ → ℕ) (i : ℕ) (u : Sequence)
    (us : List Sequence) : ∃ v, assembleCappedBodies gaps i (u :: us) = .P :: v := by
  cases hgap : gaps i with
  | zero =>
    exact ⟨u ++ [.P] ++ assembleCappedBodies gaps (i + 1) us,
      by simp [assembleCappedBodies, hgap, capWord]⟩
  | succ n =>
    exact ⟨List.replicate n .P ++ capWord u ++ assembleCappedBodies gaps (i + 1) us,
      by simp [assembleCappedBodies, hgap, List.replicate_succ]⟩

theorem phpStartCount_P_prefix (n : ℕ) (S : Sequence) :
    phpStartCount (List.replicate n .P ++ .P :: S) = phpStartCount (.P :: S) := by
  cases n with
  | zero => rfl
  | succ n =>
    exact (phpStartCount_replicate_P n (.P :: S)).trans (phpStartCount_PP_cons S)

theorem phpStartCount_P_prefix_cap (n : ℕ) (u v : Sequence) :
    phpStartCount (List.replicate n .P ++ capWord u ++ v) =
      phpStartCount (capWord u ++ v) := by
  rw [List.append_assoc]
  change phpStartCount (List.replicate n .P ++ .P :: ((u ++ [.P]) ++ v)) =
    phpStartCount (.P :: ((u ++ [.P]) ++ v))
  exact phpStartCount_P_prefix n _

theorem phpStartCount_assembleCappedBodies (gaps : ℕ → ℕ) (i : ℕ) (us : List Sequence) :
    phpStartCount (assembleCappedBodies gaps i us) =
      (us.map (fun u => phpStartCount (capWord u))).sum := by
  induction us generalizing i with
  | nil => simp [assembleCappedBodies]
  | cons u us ih =>
    rw [assembleCappedBodies, phpStartCount_P_prefix_cap]
    cases us with
    | nil => simp [assembleCappedBodies]
    | cons v vs =>
      obtain ⟨tail, htail⟩ := assembleCappedBodies_starts_P gaps (i + 1) v vs
      rw [htail, phpStartCount_capped_append_P, ← htail, ih]
      rfl

theorem hydrophobicCount_capWord (u : Sequence) : hydrophobicCount (capWord u) = hydrophobicCount u := by
  simp [capWord, hydrophobicCount_eq_count]

theorem hydrophobicCount_assembleCappedBodies (gaps : ℕ → ℕ) (i : ℕ) (us : List Sequence) :
    hydrophobicCount (assembleCappedBodies gaps i us) = (us.map hydrophobicCount).sum := by
  induction us generalizing i with
  | nil => simp [assembleCappedBodies, hydrophobicCount_eq_count]
  | cons u us ih =>
    simp only [assembleCappedBodies, hydrophobicCount_append, hydrophobicCount_replicate,
      hydrophobicCount_capWord, ih, List.map_cons, List.sum_cons]
    simp

/-- Initial H followed by its cap, all P-capped units, and the final cap P.
Each gaps i is the full prescribed linker P-length minus the two unit caps. -/
def assembleReductionWord (gaps : ℕ → ℕ) (us : List Sequence) : Sequence :=
  [.H, .P] ++ assembleCappedBodies gaps 0 us

theorem phpStartCount_assembleReductionWord (gaps : ℕ → ℕ) (us : List Sequence) :
    phpStartCount (assembleReductionWord gaps us) =
      (us.map (fun u => phpStartCount (capWord u))).sum := by
  unfold assembleReductionWord
  cases us with
  | nil => simp [assembleCappedBodies, phpStartCount_cons]
  | cons u us =>
    obtain ⟨tail, htail⟩ := assembleCappedBodies_starts_P gaps 0 u us
    rw [htail]
    simp only [List.cons_append, List.nil_append, phpStartCount_H_cons, phpStartCount_PP_cons]
    rw [← htail, phpStartCount_assembleCappedBodies]

theorem hydrophobicCount_assembleReductionWord (gaps : ℕ → ℕ) (us : List Sequence) :
    hydrophobicCount (assembleReductionWord gaps us) = 1 + (us.map hydrophobicCount).sum := by
  rw [assembleReductionWord, hydrophobicCount_append, hydrophobicCount_assembleCappedBodies]
  have h : hydrophobicCount [.H, .P] = 1 := by decide
  rw [h]

namespace ConstructionParameters

/-- Units after the terminal H, in the exact order of Section 6 and build3.py.
Bulk units are supplied as their actual path lengths in canonical order. -/
def reductionUnitBodies (p : ConstructionParameters) (items bulkLengths : List ℕ) : List Sequence :=
  [[.H], [.H], [.H], p.framePart1 ++ p.framePart2] ++
    ((List.range (p.bins + 1)).map p.separatorWord) ++
    [dimerChain p.leftFiller] ++
    items.map (fun s => dimerChain (p.itemDimers s)) ++
    [dimerChain p.rightFiller] ++
    List.replicate 3 (dimerChain (3 * (p.side - 2))) ++
    bulkLengths.map (fun n => List.replicate n .H)

def reductionWord (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (gaps : ℕ → ℕ) : Sequence :=
  assembleReductionWord gaps (p.reductionUnitBodies items bulkLengths)

theorem reductionUnitBodies_length (p : ConstructionParameters) (items bulkLengths : List ℕ) :
    (p.reductionUnitBodies items bulkLengths).length = p.bins + items.length + bulkLengths.length + 10 := by
  simp only [reductionUnitBodies, List.length_append, List.length_map, List.length_range,
    List.length_replicate, List.length_cons, List.length_nil]
  omega

end ConstructionParameters

end ProteinFolding.Tetrahedral
