import ProteinFolding.Cubic.Proofs.PackingGeometryPaths
import ProteinFolding.Cubic.Proofs.PackingGeometrySkeleton

/-! A compositional certificate for selected P-H-P centres in a word. Only
the H residues deliberately placed in edge words are selected. Counting these
centres, together with injectivity of a fold, proves full skeleton saturation;
there is no assumption about the placement of the other residues. -/

namespace ProteinFolding.CubicPacking

open CubicPackingGeometry

def PHPAt (S : Sequence) (i : ℕ) : Prop :=
  0 < i ∧ i + 1 < S.length ∧ S[i - 1]? = some .P ∧
    S[i]? = some .H ∧ S[i + 1]? = some .P

structure MarkedWord where
  word : Sequence
  anchors : Finset ℕ
  valid : ∀ i ∈ anchors, PHPAt word i

def MarkedWord.plain (S : Sequence) : MarkedWord := ⟨S, ∅, by simp⟩

def MarkedWord.append (u v : MarkedWord) : MarkedWord where
  word := u.word ++ v.word
  anchors := u.anchors ∪ v.anchors.image (fun i => u.word.length + i)
  valid := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨hpos, hlt, hp, hh, hn⟩ := u.valid i hi
      refine ⟨hpos, by simp only [List.length_append]; omega, ?_, ?_, ?_⟩
      · rw [List.getElem?_append_left (by omega)]; exact hp
      · rw [List.getElem?_append_left (by omega)]; exact hh
      · rw [List.getElem?_append_left hlt]; exact hn
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hpos, hlt, hp, hh, hn⟩ := v.valid j hj
      refine ⟨by omega, by simp only [List.length_append]; omega, ?_, ?_, ?_⟩
      · rw [List.getElem?_append_right (by omega)]
        have he : u.word.length + j - 1 - u.word.length = j - 1 := by omega
        rw [he]; exact hp
      · rw [List.getElem?_append_right (by omega)]
        simpa only [Nat.add_sub_cancel_left] using hh
      · rw [List.getElem?_append_right (by omega)]
        have he : u.word.length + j + 1 - u.word.length = j + 1 := by omega
        rw [he]; exact hn

theorem MarkedWord.append_card (u v : MarkedWord) :
    (u.append v).anchors.card = u.anchors.card + v.anchors.card := by
  have hd : Disjoint u.anchors (v.anchors.image (fun i => u.word.length + i)) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hj
    have hb := (u.valid _ hi).2.1
    omega
  change (u.anchors ∪ v.anchors.image (fun i => u.word.length + i)).card = _
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective]
  intro i j h
  dsimp only at h
  omega

def MarkedWord.edge (t : ℕ) : MarkedWord where
  word := edgeWord t
  anchors := (Finset.range t).image (fun i => 3 * i + 1)
  valid := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hj' := Finset.mem_range.mp hj
    refine ⟨by omega, by rw [edgeWord_length]; omega, ?_, ?_, ?_⟩
    · have he := repeatWord_getElem? [.P, .H, .P] t j 0 hj' (by decide)
      simpa only [edgeWord, List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.add_zero, Nat.add_sub_cancel, List.getElem?_cons_zero] using he
    · have he := repeatWord_getElem? [.P, .H, .P] t j 1 hj' (by decide)
      simpa only [edgeWord, List.length_cons, List.length_nil, Nat.reduceAdd,
        List.getElem?_cons_succ, List.getElem?_cons_zero] using he
    · have he := repeatWord_getElem? [.P, .H, .P] t j 2 hj' (by decide)
      have heq : 3 * j + 1 + 1 = 3 * j + 2 := by omega
      simpa only [edgeWord, List.length_cons, List.length_nil, Nat.reduceAdd, heq,
        List.getElem?_cons_succ, List.getElem?_cons_zero] using he

theorem MarkedWord.edge_card (t : ℕ) : (MarkedWord.edge t).anchors.card = t := by
  rw [MarkedWord.edge, Finset.card_image_of_injective, Finset.card_range]
  intro i j h
  dsimp only at h
  omega

def MarkedWord.repeat (u : MarkedWord) : ℕ → MarkedWord
  | 0 => .plain []
  | n + 1 => u.append (u.repeat n)

theorem MarkedWord.repeat_word (u : MarkedWord) (n : ℕ) :
    (u.repeat n).word = repeatWord u.word n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [MarkedWord.repeat, MarkedWord.append, repeatWord, ih]

theorem MarkedWord.repeat_card (u : MarkedWord) (n : ℕ) :
    (u.repeat n).anchors.card = n * u.anchors.card := by
  induction n with
  | zero => simp [MarkedWord.repeat, MarkedWord.plain]
  | succ n ih => rw [MarkedWord.repeat, MarkedWord.append_card, ih]; ring

def MarkedWord.join : List MarkedWord → MarkedWord
  | [] => .plain []
  | u :: us => u.append (MarkedWord.join us)

theorem MarkedWord.join_word (us : List MarkedWord) :
    (MarkedWord.join us).word = (us.map MarkedWord.word).flatten := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [MarkedWord.join, MarkedWord.append, List.map_cons, List.flatten_cons, ih]

theorem MarkedWord.join_card (us : List MarkedWord) :
    (MarkedWord.join us).anchors.card = (us.map (fun u => u.anchors.card)).sum := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [MarkedWord.join, MarkedWord.append_card, List.map_cons, List.sum_cons, ih]

def MarkedWord.castWord (u : MarkedWord) (S : Sequence) (h : u.word = S) : MarkedWord :=
  ⟨S, u.anchors, by intro i hi; rw [← h]; exact u.valid i hi⟩

def prefixMarked (q Q : ℕ) : MarkedWord :=
  let d := depth q Q
  MarkedWord.join [MarkedWord.edge (9 * d + 8), .plain (faceWord (d ^ 2)),
    .edge d, .plain (List.replicate 4 .P),
    (MarkedWord.join [.plain (faceWord (d ^ 2)), .plain (List.replicate (d + 9) .P)]).repeat 3,
    .plain (faceWord (d ^ 2 - 2)), .plain [.P], .plain (List.replicate (d ^ 3 + 2) .H),
    .plain (List.replicate (alpha Q + 8) .P)]

def wallUnitMarked (q Q : ℕ) : MarkedWord :=
  MarkedWord.join [.edge (alpha Q), .plain (faceWord (depth q Q)), .edge (beta Q),
    .plain (faceWord (depth q Q)), .edge (alpha Q)]

def gapMarked (q Q : ℕ) : MarkedWord :=
  MarkedWord.join [.edge 2,
    (MarkedWord.join [.plain (List.replicate (2 * alpha Q + 4) .P), .edge 2]).repeat (q - 1)]

def wallsMarked (q Q : ℕ) : MarkedWord :=
  MarkedWord.join [
    (MarkedWord.join [wallUnitMarked q Q, .plain (List.replicate (2 * alpha Q) .P)]).repeat (q - 1),
    wallUnitMarked q Q, gapMarked q Q]

def frameMarked (q Q : ℕ) (items : List ℕ) : MarkedWord :=
  MarkedWord.join [prefixMarked q Q, wallsMarked q Q, .plain (itemWords q Q items)]

theorem prefixMarked_word (q Q : ℕ) : (prefixMarked q Q).word = prefixWord q Q := by
  simp [prefixMarked, MarkedWord.join_word, MarkedWord.repeat_word,
    MarkedWord.edge, MarkedWord.plain, prefixWord, List.append_assoc]

theorem wallUnitMarked_word (q Q : ℕ) : (wallUnitMarked q Q).word = wallUnit q Q := by
  simp [wallUnitMarked, MarkedWord.join_word, MarkedWord.edge, MarkedWord.plain, wallUnit, List.append_assoc]

theorem gapMarked_word (q Q : ℕ) : (gapMarked q Q).word = gapWord q Q := by
  simp [gapMarked, MarkedWord.join_word, MarkedWord.repeat_word,
    MarkedWord.edge, MarkedWord.plain, gapWord]

theorem wallsMarked_word (q Q : ℕ) : (wallsMarked q Q).word = walls q Q := by
  simp [wallsMarked, MarkedWord.join_word, MarkedWord.repeat_word, wallUnitMarked_word,
    gapMarked_word, MarkedWord.plain, walls, List.append_assoc]

theorem frameMarked_word (q Q : ℕ) (items : List ℕ) :
    (frameMarked q Q items).word = frameWord q Q items := by
  simp [frameMarked, MarkedWord.join_word, prefixMarked_word, wallsMarked_word,
    MarkedWord.plain, frameWord, List.append_assoc]

theorem prefixMarked_card (q Q : ℕ) :
    (prefixMarked q Q).anchors.card = 10 * depth q Q + 8 := by
  simp [prefixMarked, MarkedWord.join_card, MarkedWord.repeat_card,
    MarkedWord.edge_card, MarkedWord.plain]
  omega

theorem wallsMarked_card (q Q : ℕ) (hq : 0 < q) :
    (wallsMarked q Q).anchors.card = 2 * depth q Q := by
  have hq' : q - 1 + 1 = q := by omega
  simp only [wallsMarked, wallUnitMarked, gapMarked, MarkedWord.join_card,
    MarkedWord.repeat_card, MarkedWord.edge_card, MarkedWord.plain,
    Finset.card_empty, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have he : (q - 1) * (alpha Q + beta Q + alpha Q) +
      (alpha Q + beta Q + alpha Q) = q * (alpha Q + beta Q + alpha Q) := by
    calc
      _ = (q - 1 + 1) * (alpha Q + beta Q + alpha Q) := by ring
      _ = _ := by rw [hq']
  dsimp [alpha, beta, depth]
  nlinarith

theorem frameMarked_card (q Q : ℕ) (items : List ℕ) (hq : 0 < q) :
    (frameMarked q Q items).anchors.card = 12 * depth q Q + 8 := by
  simp [frameMarked, MarkedWord.join_card, prefixMarked_card, wallsMarked_card q Q hq,
    MarkedWord.plain]
  omega

def MarkedWord.indices (u : MarkedWord) : Finset (Fin u.word.length) :=
  u.anchors.attach.image (fun i => ⟨i.val, by have h := u.valid i.val i.property; exact Nat.lt_of_succ_lt h.2.1⟩)

theorem MarkedWord.indices_card (u : MarkedWord) : u.indices.card = u.anchors.card := by
  have hinj : Function.Injective (fun i : {i // i ∈ u.anchors} =>
      (⟨i.val, Nat.lt_of_succ_lt (u.valid i.val i.property).2.1⟩ : Fin u.word.length)) := by
    intro i j h
    apply Subtype.ext
    exact congrArg Fin.val h
  rw [MarkedWord.indices, Finset.card_image_of_injective _ hinj, Finset.card_attach]

theorem MarkedWord.indices_php (u : MarkedWord) (i : Fin u.word.length) (hi : i ∈ u.indices) :
    PHPAt u.word i.val := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact u.valid j.val j.property

theorem MarkedWord.mem_indices (u : MarkedWord) (i : Fin u.word.length) :
    i ∈ u.indices ↔ i.val ∈ u.anchors := by
  constructor
  · intro h
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp h
    have hv : j.val = i.val := congrArg Fin.val he
    exact hv ▸ j.property
  · intro h
    refine Finset.mem_image.mpr ⟨⟨i.val, h⟩, by simp, ?_⟩
    apply Fin.ext
    rfl

/-- The unmarked middle fragment contributes no selected edge anchors, even
when surrounded by marked words. This supplies index disjointness for F paths. -/
theorem MarkedWord.plain_segment_not_anchor (u v : MarkedWord) (S : Sequence)
    (i : ℕ) (hi : i < S.length) :
    u.word.length + i ∉ ((u.append (.plain S)).append v).anchors := by
  intro h
  simp only [MarkedWord.append, MarkedWord.plain, Finset.image_empty, Finset.union_empty,
    List.length_append, Finset.mem_union, Finset.mem_image] at h
  rcases h with h | ⟨j, _, hj⟩
  · have hu := (u.valid _ h).2.1
    omega
  · omega

theorem get_of_optional (S : Sequence) (i : Fin S.length) (r : Residue)
    (h : S[i.val]? = some r) : S.get i = r := by
  rw [List.getElem?_eq_getElem i.isLt] at h
  exact Option.some.inj h

theorem MarkedWord.indices_on_skeleton (u : MarkedWord)
    (f : Fold cubicLattice u.word.length) (a : Site) (n : ℕ)
    (hpack : hydrophobicSites u.word f = cube a n) :
    ∀ i ∈ u.indices, EdgeSkeleton a n (f.pos i) := by
  intro i hi
  obtain ⟨hpos, hlt, hp, hh, hn⟩ := u.indices_php i hi
  let prev : Fin u.word.length := ⟨i.val - 1, by have := i.isLt; omega⟩
  let next : Fin u.word.length := ⟨i.val + 1, hlt⟩
  apply php_on_edge f a n hpack prev i next
  · dsimp [prev]; omega
  · rfl
  · exact get_of_optional u.word prev .P hp
  · exact get_of_optional u.word i .H hh
  · exact get_of_optional u.word next .P hn

def markedFrame (q Q : ℕ) (items : List ℕ) : MarkedWord :=
  (frameMarked q Q items).castWord (frameWord q Q items) (frameMarked_word q Q items)

def frameAnchors (q Q : ℕ) (items : List ℕ) : Finset (Fin (frameWord q Q items).length) :=
  (markedFrame q Q items).indices

theorem frameAnchors_card (q Q : ℕ) (items : List ℕ) (hq : 0 < q) :
    (frameAnchors q Q items).card = 12 * depth q Q + 8 := by
  rw [frameAnchors, MarkedWord.indices_card]
  exact frameMarked_card q Q items hq

/-- All cube edges are filled by the selected H residues of the actual frame
word. This supplies the global saturation premise for face confinement. -/
theorem frame_skeleton_saturated (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (f : Fold cubicLattice (frameWord q Q items).length) (a : Site)
    (hpack : hydrophobicSites (frameWord q Q items) f = cube a (side q Q)) :
    (frameAnchors q Q items).image f.pos = skeletonFinset a (side q Q) := by
  apply skeleton_saturated f a (side q Q) (frameAnchors q Q items)
  · exact (markedFrame q Q items).indices_on_skeleton f a (side q Q) hpack
  · rw [frameAnchors_card q Q items hq, skeletonFinset_card a (side q Q) (by simp [side])]
    simp [side]

end ProteinFolding.CubicPacking
