import ProteinFolding.Cubic.Proofs.PackingGeometryFrameIndices
import ProteinFolding.Cubic.Proofs.PackingGeometryAnchorFamily
import ProteinFolding.Cubic.Proofs.PackingGeometryShortLinks

/-! Literal occurrences of the E blocks in the reduction word. The offsets
below are sequence indices, before any geometric interpretation of a fold. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicPacking

theorem repeatWord_append (u : Sequence) (m n : ℕ) :
    repeatWord u (m + n) = repeatWord u m ++ repeatWord u n := by
  induction m with
  | zero => simp [repeatWord]
  | succ m ih => simp [repeatWord, Nat.succ_add, ih, List.append_assoc]

theorem repeatWord_split (u : Sequence) (n j : ℕ) (hj : j < n) :
    repeatWord u n = repeatWord u j ++ u ++ repeatWord u (n - j - 1) := by
  have hn : n = j + (n - j - 1 + 1) := by omega
  rw [hn, repeatWord_append]
  have he : j + (n - j - 1 + 1) - j - 1 = n - j - 1 := by omega
  rw [he]
  simp [repeatWord, List.append_assoc]

def separatedCopies (u link : Sequence) (q : ℕ) : Sequence :=
  repeatWord (u ++ link) (q - 1) ++ u

theorem separatedCopies_occurrence (u link : Sequence) (q j : ℕ) (hj : j < q) :
    ∃ pre post : Sequence,
      separatedCopies u link q = pre ++ u ++ post ∧
      pre.length = j * (u.length + link.length) := by
  by_cases hlast : j = q - 1
  · refine ⟨repeatWord (u ++ link) j, [], ?_, ?_⟩
    · simp [separatedCopies, hlast]
    · simp [repeatWord_length]
  · have hj' : j < q - 1 := by omega
    refine ⟨repeatWord (u ++ link) j,
      link ++ repeatWord (u ++ link) (q - 1 - j - 1) ++ u, ?_, ?_⟩
    · unfold separatedCopies
      rw [repeatWord_split (u ++ link) (q - 1) j hj']
      simp only [List.append_assoc]
    · simp [repeatWord_length]

theorem repeatWord_slide (u link : Sequence) (n : ℕ) :
    repeatWord (u ++ link) n ++ u = u ++ repeatWord (link ++ u) n := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih =>
    simp only [repeatWord, List.append_assoc]
    rw [ih]

/-- A contiguous E block, certified inside the complete literal sequence. -/
structure EdgeOccurrence (S : Sequence) (t : ℕ) where
  pre : Sequence
  post : Sequence
  word_eq : S = pre ++ edgeWord t ++ post

namespace EdgeOccurrence

def prepend {S : Sequence} {t : ℕ} (o : EdgeOccurrence S t) (u : Sequence) :
    EdgeOccurrence (u ++ S) t where
  pre := u ++ o.pre
  post := o.post
  word_eq := by simpa only [List.append_assoc] using congrArg (u ++ ·) o.word_eq

def append {S : Sequence} {t : ℕ} (o : EdgeOccurrence S t) (u : Sequence) :
    EdgeOccurrence (S ++ u) t where
  pre := o.pre
  post := o.post ++ u
  word_eq := by simpa only [List.append_assoc] using congrArg (· ++ u) o.word_eq

def cast {S T : Sequence} {t : ℕ} (o : EdgeOccurrence S t) (h : T = S) :
    EdgeOccurrence T t where
  pre := o.pre
  post := o.post
  word_eq := h.trans o.word_eq

def index {S : Sequence} {t : ℕ} (o : EdgeOccurrence S t) (i : Fin t) : Fin S.length :=
  Fin.cast (congrArg List.length o.word_eq).symm (edgeIndex o.pre o.post t i 1)

theorem index_val {S : Sequence} {t : ℕ} (o : EdgeOccurrence S t) (i : Fin t) :
    (o.index i).val = o.pre.length + 3 * i.val + 1 := rfl

def path {S : Sequence} {t : ℕ} (o : EdgeOccurrence S t)
    (f : Fold cubicLattice S.length) (i : Fin t) : Site := f.pos (o.index i)

theorem path_eq {S : Sequence} {t : ℕ} (o : EdgeOccurrence S t)
    (f : Fold cubicLattice S.length) :
    o.path f = edgeHPath o.pre o.post t (foldOnWord o.word_eq f) := by
  funext i
  exact (foldOnWord_pos o.word_eq f (edgeIndex o.pre o.post t i 1)).symm

theorem path_injective {S : Sequence} {t : ℕ} (o : EdgeOccurrence S t)
    (f : Fold cubicLattice S.length) : Function.Injective (o.path f) := by
  rw [o.path_eq]
  exact edgeHPath_injective o.pre o.post t (foldOnWord o.word_eq f)

theorem path_skeleton {S : Sequence} {t : ℕ} (o : EdgeOccurrence S t)
    (f : Fold cubicLattice S.length) (a : Site) (n : ℕ)
    (hpack : hydrophobicSites S f = cube a n) (i : Fin t) :
    EdgeSkeleton a n (o.path f i) := by
  rw [o.path_eq]
  apply edgeHPath_on_skeleton o.pre o.post t (foldOnWord o.word_eq f) a n
  rw [foldOnWord_hydrophobicSites]
  exact hpack

theorem path_adjacent {S : Sequence} {t : ℕ} (o : EdgeOccurrence S t)
    (f : Fold cubicLattice S.length) (a : Site) (n : ℕ)
    (hpack : hydrophobicSites S f = cube a n) (i j : Fin t) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (o.path f i) (o.path f j) := by
  rw [o.path_eq]
  apply edgeHPath_adjacent o.pre o.post t (foldOnWord o.word_eq f) a n
    (by rw [foldOnWord_hydrophobicSites]; exact hpack) i j hij

def sites {S : Sequence} {t : ℕ} (o : EdgeOccurrence S t)
    (f : Fold cubicLattice S.length) : Finset Site := Finset.univ.image (o.path f)

theorem sites_card {S : Sequence} {t : ℕ} (o : EdgeOccurrence S t)
    (f : Fold cubicLattice S.length) : (o.sites f).card = t := by
  rw [sites, Finset.card_image_of_injective _ (o.path_injective f)]
  simp

theorem sites_eq_pathList {S : Sequence} {t : ℕ} (o : EdgeOccurrence S t)
    (f : Fold cubicLattice S.length) :
    o.sites f = (edgeHPathList o.pre o.post t (foldOnWord o.word_eq f)).toFinset := by
  rw [sites, o.path_eq]
  ext p
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset,
    edgeHPathList, List.mem_ofFn]

theorem sites_disjoint_of_before {S : Sequence} {t u : ℕ}
    (o : EdgeOccurrence S t) (p : EdgeOccurrence S u)
    (f : Fold cubicLattice S.length) (hbefore : o.pre.length + 3 * t ≤ p.pre.length) :
    Disjoint (o.sites f) (p.sites f) := by
  rw [o.sites_eq_pathList, p.sites_eq_pathList]
  exact (separated_edge_paths_disjoint f o.pre o.post p.pre p.post t u
    o.word_eq p.word_eq hbefore).symm

end EdgeOccurrence

end ProteinFolding.CubicPackingGeometry
