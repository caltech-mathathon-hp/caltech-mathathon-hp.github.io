import Shelf.Anatomy
import Shelf.Count

/-!
# Where the pieces of the string are

Section 3 of our write-up writes the string as a product of pieces: the core, the
runs `A`, `F₁`, `F₂`, the separators with their tethers, and one block per item.
The proof of Theorem 12 only uses where the `H`'s of these pieces are and which
letters between them are `P`'s. `Anatomy` (in `Shelf/Anatomy.lean`) lists these
facts; here we check them for the string `shelfWord J`, letter by letter.

The tool is `Occ S w o`: the word `w` occurs in `S` starting at letter `o`. We
find each piece of the string as an occurrence at an explicit offset
(`offA`, `offF₁`, `offSep`, `offF₂`, `offItem`), and read the letters off.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue List

/-! ### Occurrences of a word in a string -/

/-- The word `w` occurs in `S` starting at letter `o`. -/
def Occ (S w : Sequence) (o : ℕ) : Prop :=
  ∃ pre post, S = pre ++ w ++ post ∧ pre.length = o

theorem Occ.letter {S w : Sequence} {o t : ℕ} {x : Residue} (h : Occ S w o)
    (hw : w[t]? = some x) : S[o + t]? = some x := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  have ht : t < w.length := (List.getElem?_eq_some_iff.mp hw).1
  rw [getElem?_append_left (by simp; omega), getElem?_append_right (by omega)]
  simpa using hw

theorem Occ.letter' {S w : Sequence} {o t i : ℕ} {x : Residue} (h : Occ S w o)
    (hw : w[t]? = some x) (hi : i = o + t) : S[i]? = some x :=
  hi ▸ h.letter hw

theorem Occ.rep {S : Sequence} {k o i : ℕ} {x : Residue} (h : Occ S (replicate k x) o)
    (h1 : o ≤ i) (h2 : i < o + k) : S[i]? = some x :=
  h.letter' (t := i - o) (getElem?_replicate_of_lt (by omega)) (by omega)

theorem Occ.self (w : Sequence) : Occ w w 0 := ⟨[], [], by simp, rfl⟩

theorem Occ.start (w y : Sequence) : Occ (w ++ y) w 0 := ⟨[], y, by simp, rfl⟩

theorem Occ.shift (x : Sequence) {y w : Sequence} {o : ℕ} (h : Occ y w o) :
    Occ (x ++ y) w (x.length + o) := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨x ++ pre, post, by simp, by simp⟩

theorem Occ.left {S x y : Sequence} {o : ℕ} (h : Occ S (x ++ y) o) : Occ S x o := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨pre, y ++ post, by simp, rfl⟩

theorem Occ.right {S x y : Sequence} {o : ℕ} (h : Occ S (x ++ y) o) :
    Occ S y (o + x.length) := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨pre ++ x, post, by simp, by simp⟩

theorem Occ.congr {S w : Sequence} {o o' : ℕ} (h : Occ S w o) (e : o = o') : Occ S w o' :=
  e ▸ h

/-! ### Letters of repeated blocks, dense runs and separators -/

/-- Letter `|w| q + s` of `w^r` is letter `s` of `w`. -/
theorem getElem?_flatten_replicate (w : Sequence) {r q s : ℕ} (hq : q < r)
    (hs : s < w.length) : (replicate r w).flatten[w.length * q + s]? = w[s]? := by
  induction q generalizing r with
  | zero =>
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [replicate_succ, flatten_cons, Nat.mul_zero, Nat.zero_add, getElem?_append_left hs]
  | succ q ih =>
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [replicate_succ, flatten_cons, getElem?_append_right (by rw [Nat.mul_succ]; omega)]
    have : w.length * (q + 1) + s - w.length = w.length * q + s := by
      rw [Nat.mul_succ]; omega
    rw [this, ih (by omega)]

/-- The `H`'s of `D(r)` are its letters `0, 3, …, 3 (r - 1)`. -/
theorem denseRun_H {r t : ℕ} (ht : t < r) : (denseRun r)[3 * t]? = some H := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  cases t with
  | zero => rfl
  | succ t =>
    have := getElem?_flatten_replicate [P, P, H] (r := r) (q := t) (s := 2) (by omega)
      (by simp)
    rw [show 3 * (t + 1) = (3 * t + 2) + 1 by ring]
    simpa [denseRun] using this

/-- Between consecutive `H`'s of `D(r)` there are two `P`'s. -/
theorem denseRun_P {r t : ℕ} (ht : t + 1 < r) :
    (denseRun r)[3 * t + 1]? = some P ∧ (denseRun r)[3 * t + 2]? = some P := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have h0 := getElem?_flatten_replicate [P, P, H] (r := r) (q := t) (s := 0) (by omega)
    (by simp)
  have h1 := getElem?_flatten_replicate [P, P, H] (r := r) (q := t) (s := 1) (by omega)
    (by simp)
  constructor
  · simpa [denseRun] using h0
  · simpa [denseRun] using h1

theorem length_separators (J : Packing.Instance) :
    (separators J).length = 1 + (J.capacity + 7) * J.bins := by
  simp [separators, length_flatten]; ring

/-- The separators are the letters `(B + 7) j` of `H (P^(B+6) H)^m`. -/
theorem separators_H (J : Packing.Instance) {j : ℕ} (hj : j ≤ J.bins) :
    (separators J)[(J.capacity + 7) * j]? = some H := by
  cases j with
  | zero => rfl
  | succ q =>
    have := getElem?_flatten_replicate (replicate (J.capacity + 6) P ++ [H])
      (r := J.bins) (q := q) (s := J.capacity + 6) (by omega) (by simp)
    rw [getElem?_append_right (by simp)] at this
    rw [show (J.capacity + 7) * (q + 1) = ((J.capacity + 7) * q + (J.capacity + 6)) + 1 by
      ring]
    simpa [separators] using this

/-- The inner tethers of `H (P^(B+6) H)^m` consist of `P`'s. -/
theorem separators_P (J : Packing.Instance) {j u : ℕ} (hj : j < J.bins)
    (hu : u < J.capacity + 6) :
    (separators J)[(J.capacity + 7) * j + 1 + u]? = some P := by
  have := getElem?_flatten_replicate (replicate (J.capacity + 6) P ++ [H])
    (r := J.bins) (q := j) (s := u) hj (by simp; omega)
  rw [getElem?_append_left (by simpa using hu), getElem?_replicate_of_lt hu] at this
  rw [show (J.capacity + 7) * j + 1 + u = ((J.capacity + 7) * j + u) + 1 by ring]
  simpa [separators] using this

/-- If a dense run occurs in `S` with a `P` just before it and a `P` just after it,
then all its `H`'s are isolated. -/
theorem runAt_of_occ {S : Sequence} {o r : ℕ} (h : Occ S (denseRun r) o) (h1 : 1 ≤ o)
    (hb : S[o - 1]? = some P) (ha : S[o + (denseRun r).length]? = some P) :
    RunAt S o r := by
  intro t ht
  rw [length_denseRun] at ha
  refine ⟨by omega, ?_, h.letter (denseRun_H ht), ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | htp
    · simpa using hb
    · exact h.letter' (denseRun_P (t := t - 1) (by omega)).2 (by omega)
  · by_cases hlt : t + 1 < r
    · exact h.letter' (denseRun_P hlt).1 (by omega)
    · rw [show o + 3 * t + 1 = o + (3 * r - 2) by omega]; exact ha

/-! ### The items -/

theorem items_head (lam : ℕ) (hl : 1 ≤ lam) (l : List ℕ) :
    ∃ post, (l.map fun a => replicate lam P ++ denseRun a).flatten ++ [P] = P :: post := by
  cases l with
  | nil => exact ⟨[], rfl⟩
  | cons a l =>
    obtain ⟨k, rfl⟩ : ∃ k, lam = k + 1 := ⟨lam - 1, by omega⟩
    simp [replicate_succ]

/-- In `∏ᵢ (P^λ D(aᵢ)) P`, the block `P^λ D(aᵢ) P` starts after the earlier blocks. -/
theorem occ_items (lam : ℕ) (hl : 1 ≤ lam) :
    ∀ (l : List ℕ) (i : ℕ) (hi : i < l.length),
      Occ ((l.map fun a => replicate lam P ++ denseRun a).flatten ++ [P])
        (replicate lam P ++ denseRun l[i] ++ [P])
        ((l.map fun a => lam + (denseRun a).length).take i).sum
  | [], i, hi => absurd hi (by simp)
  | a :: l, 0, _ => by
      obtain ⟨post, hp⟩ := items_head lam hl l
      refine ⟨[], post, ?_, rfl⟩
      simp only [map_cons, flatten_cons, append_assoc] at hp ⊢
      rw [hp]
      simp
  | a :: l, i + 1, hi => by
      have := (occ_items lam hl l i (by simpa using hi)).shift
        (replicate lam P ++ denseRun a)
      simp only [map_cons, flatten_cons, append_assoc, take_succ_cons, sum_cons,
        getElem_cons_succ] at this ⊢
      exact this.congr (by simp)

/-- Sums of longer prefixes are larger. -/
theorem sum_take_mono (l : List ℕ) {i j : ℕ} (h : i ≤ j) :
    (l.take i).sum ≤ (l.take j).sum := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [take_add, sum_append]
  omega

/-! ### The offsets -/

/-- First `H` of `A`. -/
def offA (J : Packing.Instance) : ℕ := coreLength (side J) + 2

/-- First `H` of `F₁`. -/
def offF₁ (J : Packing.Instance) : ℕ :=
  offA J + (denseRun (9 * side J - 10)).length + linkerLength J

/-- The separator `σ_{j+1}`. -/
def offSep (J : Packing.Instance) (j : ℕ) : ℕ :=
  offF₁ J + (denseRun (side J - 2)).length + side J + (J.capacity + 7) * j

/-- First `H` of `F₂`. -/
def offF₂ (J : Packing.Instance) : ℕ := offSep J J.bins + 1 + side J

/-- First letter of the items (the first letter of the first linker). -/
def offItems (J : Packing.Instance) : ℕ := offF₂ J + (denseRun (side J - 2)).length

/-- Where the block `P^λ D(aᵢ)` of the item `i` starts. -/
def offBlock (J : Packing.Instance) (i : ℕ) : ℕ :=
  offItems J + ((J.sizes.map fun a => linkerLength J + (denseRun a).length).take i).sum

/-- First `H` of the item `i`. -/
def offItem (J : Packing.Instance) (i : ℕ) : ℕ := offBlock J i + linkerLength J

theorem three_le_side (J : Packing.Instance) : 3 ≤ side J := by unfold side; omega

theorem linker_ge (J : Packing.Instance) : 12 ≤ linkerLength J := by
  have := three_le_side J; unfold linkerLength; omega

/-! ### Where the pieces occur -/

section Pieces

variable (J : Packing.Instance)

theorem shelfWord_eq : shelfWord J =
    replicate (coreLength (side J)) H ++ ([P, P] ++ (denseRun (9 * side J - 10) ++
    (replicate (linkerLength J) P ++ (denseRun (side J - 2) ++ (replicate (side J) P ++
    (separators J ++ (replicate (side J) P ++ (denseRun (side J - 2) ++
    (itemsWord J ++ [P]))))))))) := by
  simp [shelfWord, shelfPieces]

theorem occ_PP : Occ (shelfWord J) [P, P] (coreLength (side J)) := by
  rw [shelfWord_eq]
  exact ((Occ.start _ _).shift _).congr (by simp)

theorem occ_A : Occ (shelfWord J) (denseRun (9 * side J - 10)) (offA J) := by
  rw [shelfWord_eq]
  exact (((Occ.start _ _).shift _).shift _).congr (by simp [offA])

theorem occ_L : Occ (shelfWord J) (replicate (linkerLength J) P)
    (offA J + (denseRun (9 * side J - 10)).length) := by
  rw [shelfWord_eq]
  exact ((((Occ.start _ _).shift _).shift _).shift _).congr (by simp [offA]; omega)

theorem occ_F₁ : Occ (shelfWord J) (denseRun (side J - 2)) (offF₁ J) := by
  rw [shelfWord_eq]
  exact (((((Occ.start _ _).shift _).shift _).shift _).shift _).congr
    (by simp [offA, offF₁]; omega)

theorem occ_T₁ : Occ (shelfWord J) (replicate (side J) P)
    (offF₁ J + (denseRun (side J - 2)).length) := by
  rw [shelfWord_eq]
  exact ((((((Occ.start _ _).shift _).shift _).shift _).shift _).shift _).congr
    (by simp [offA, offF₁]; omega)

theorem occ_Sep : Occ (shelfWord J) (separators J) (offSep J 0) := by
  rw [shelfWord_eq]
  exact (((((((Occ.start _ _).shift _).shift _).shift _).shift _).shift _).shift _).congr
    (by simp [offA, offF₁, offSep]; omega)

theorem occ_T₂ : Occ (shelfWord J) (replicate (side J) P) (offSep J J.bins + 1) := by
  rw [shelfWord_eq]
  refine ((((((((Occ.start _ _).shift _).shift _).shift _).shift _).shift _).shift _).shift
    _).congr ?_
  simp only [length_replicate, length_cons, length_nil, length_separators, offSep, offF₁,
    offA]
  omega

theorem occ_F₂ : Occ (shelfWord J) (denseRun (side J - 2)) (offF₂ J) := by
  rw [shelfWord_eq]
  refine (((((((((Occ.start _ _).shift _).shift _).shift _).shift _).shift _).shift
    _).shift _).shift _).congr ?_
  simp only [length_replicate, length_cons, length_nil, length_separators, offF₂, offSep,
    offF₁, offA]
  omega

theorem occ_Items : Occ (shelfWord J) (itemsWord J ++ [P]) (offItems J) := by
  rw [shelfWord_eq]
  refine ((((((((((Occ.self (itemsWord J ++ [P])).shift _).shift
    _).shift _).shift _).shift _).shift _).shift _).shift _).shift _).congr ?_
  simp only [length_replicate, length_cons, length_nil, length_separators, offItems, offF₂,
    offSep, offF₁, offA]
  omega

theorem occ_block (i : ℕ) (hi : i < J.sizes.length) :
    Occ (shelfWord J) (replicate (linkerLength J) P ++ denseRun J.sizes[i] ++ [P])
      (offBlock J i) := by
  obtain ⟨pre, post, hS, hpre⟩ := occ_Items J
  obtain ⟨pre', post', hI, hpre'⟩ :=
    occ_items (linkerLength J) (by have := linker_ge J; omega) J.sizes i hi
  refine ⟨pre ++ pre', post' ++ post, ?_, ?_⟩
  · rw [hS, show itemsWord J ++ [P] = _ from hI]; simp
  · simp [offBlock, hpre, hpre']

end Pieces

/-! ### The anatomy -/

/-- The string of the reduction has the features that the proof of Theorem 12 uses
(Section 3 of our write-up: the positions of `A`, `F₁`, the separators, `F₂` and the items). -/
def shelfAnatomy (J : Packing.Instance) : Anatomy (shelfWord J) J where
  oA := offA J
  oF₁ := offF₁ J
  oSep := offSep J
  oF₂ := offF₂ J
  oItem i := offItem J i
  runA := by
    have hn := three_le_side J
    have hl := linker_ge J
    refine runAt_of_occ (occ_A J) (by unfold offA; omega) ?_ ?_
    · exact (occ_PP J).letter' (t := 1) rfl (by unfold offA; omega)
    · exact (occ_L J).rep (by omega) (by omega)
  runF₁ := by
    have hn := three_le_side J
    have hl := linker_ge J
    refine runAt_of_occ (occ_F₁ J) (by unfold offF₁; omega) ?_ ?_
    · exact (occ_L J).rep (by unfold offF₁; omega) (by unfold offF₁; omega)
    · exact (occ_T₁ J).rep (by omega) (by omega)
  sep := by
    intro j hj
    have hn := three_le_side J
    refine ⟨by unfold offSep offF₁; omega, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hjp
      · exact (occ_T₁ J).rep (by unfold offSep; omega) (by unfold offSep; omega)
      · obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
        refine (occ_Sep J).letter' (separators_P J (j := q) (u := J.capacity + 5)
          (by omega) (by omega)) ?_
        simp only [offSep, Nat.mul_succ]; omega
    · exact (occ_Sep J).letter' (separators_H J hj) (by simp [offSep])
    · rcases Nat.lt_or_ge j J.bins with hlt | hge
      · exact (occ_Sep J).letter' (separators_P J (u := 0) hlt (by omega))
          (by simp [offSep]; omega)
      · obtain rfl : j = J.bins := by omega
        exact (occ_T₂ J).rep (by omega) (by omega)
  runF₂ := by
    have hn := three_le_side J
    refine runAt_of_occ (occ_F₂ J) (by unfold offF₂; omega) ?_ ?_
    · exact (occ_T₂ J).rep (by unfold offF₂; omega) (by unfold offF₂; omega)
    · obtain ⟨post, hp⟩ := items_head (linkerLength J) (by have := linker_ge J; omega)
        J.sizes
      refine (occ_Items J).letter' (t := 0) ?_ (by unfold offItems; omega)
      rw [show itemsWord J ++ [P] = _ from hp]; rfl
  runItem := by
    intro i
    have hl := linker_ge J
    have hb := occ_block J i.val i.isLt
    have hd := hb.left.right
    refine runAt_of_occ (by simpa using hd) (by unfold offItem; omega) ?_ ?_
    · exact hb.left.left.rep (by unfold offItem; omega) (by unfold offItem; omega)
    · exact hb.right.letter' (t := 0) rfl (by simp [offItem]; omega)
  tetherF₁ := by
    have hn := three_le_side J
    simp only [offSep, length_denseRun]; omega
  tetherF₁_P := by
    intro t h1 h2
    have hn := three_le_side J
    simp only [offSep, length_denseRun] at h2
    exact (occ_T₁ J).rep (by rw [length_denseRun]; omega) (by rw [length_denseRun]; omega)
  tetherSep := by
    intro j _
    simp only [offSep, Nat.mul_succ]; omega
  tetherSep_P := by
    intro j hj t h1 h2
    simp only [offSep, Nat.mul_succ] at h1 h2
    refine (occ_Sep J).letter' (separators_P J (j := j) (u := t - offSep J j - 1) hj
      (by simp only [offSep]; omega)) ?_
    simp only [offSep]; omega
  tetherF₂ := by unfold offF₂; omega
  tetherF₂_P := by
    intro t h1 h2
    exact (occ_T₂ J).rep (by omega) (by unfold offF₂ at h2; omega)
  A_before_F₁ := by
    have hl := linker_ge J
    simp only [offF₁, length_denseRun]; omega
  F₂_before_items := by
    intro i
    have hl := linker_ge J
    have hn := three_le_side J
    simp only [offItem, offBlock, offItems, length_denseRun]; omega
  items_in_order := by
    intro i i' hii'
    have hl := linker_ge J
    have hlt : i.val < i'.val := hii'
    have hmono := sum_take_mono (J.sizes.map fun a => linkerLength J + (denseRun a).length)
      (show i.val + 1 ≤ i'.val by omega)
    rw [sum_take_succ _ _ (by simp)] at hmono
    simp only [getElem_map] at hmono
    have hlen := length_denseRun (J.sizes[i.val])
    simp only [offItem, offBlock, List.get_eq_getElem]
    omega

end ProteinFolding.Shelf
