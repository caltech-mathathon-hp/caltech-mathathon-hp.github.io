import ProteinFolding.Tetrahedral.BulkVertexPatches
import ProteinFolding.Tetrahedral.OctahedralEdgeParametrization

/-! Uniform bounded neighbourhoods of far edge points, with no finite-size assumption. -/

namespace ProteinFolding.Tetrahedral

theorem edgeZigzag_even_inA (a b : Fin 4) (p : Site) (hp : InASublattice p.val) (n : ℕ) :
    InASublattice (edgeZigzag a b p (2 * n)).val := by
  induction n with
  | zero => simpa [edgeZigzag] using hp
  | succ n ih =>
    have hqB := step_in_B ih a
    have hidx : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [hidx]
    change InASublattice
      (edgeForwardStep a b (edgeForwardStep a b (edgeZigzag a b p (2 * n)))).val
    have hfirst : edgeForwardStep a b (edgeZigzag a b p (2 * n)) =
        step (edgeZigzag a b p (2 * n)) a := by rw [edgeForwardStep, if_pos ih]
    rw [hfirst, edgeForwardStep, if_neg ((inB_iff_not_inA _).mp hqB)]
    exact step_in_A hqB b

def bulkEdgeAnchor (m : ℕ) (F : OctEdgeFrame) (t : ℕ) : Site := octEdgeZigzag m F (2 * t)

theorem bulkEdgeAnchor_inA (m : ℕ) (F : OctEdgeFrame) (t : ℕ) :
    InASublattice (bulkEdgeAnchor m F t).val := by
  have hstart : InASublattice (octEdgeStart m F).val := by
    unfold octEdgeStart octVertexForFaces
    split_ifs <;> exact octVertexCoordinates_inA _ _ _
  exact edgeZigzag_even_inA F.a F.b (octEdgeStart m F) hstart t

def bulkEdgeDelta (m M t T : ℕ) (F : OctEdgeFrame) : Site :=
  shiftSite (bulkEdgeAnchor M F T) (bulkEdgeAnchor_inA M F T) (bulkEdgeAnchor m F t)

theorem bulkEdgeDelta_inA (m M t T : ℕ) (F : OctEdgeFrame) :
    InASublattice (bulkEdgeDelta m M t T F).val :=
  sub_A_A (bulkEdgeAnchor_inA m F t) (bulkEdgeAnchor_inA M F T)

def bulkEdgeReanchor (m M t T : ℕ) (F : OctEdgeFrame) (p : Site) : Site :=
  shiftSite (bulkEdgeDelta m M t T F) (bulkEdgeDelta_inA m M t T F) p

theorem bulkEdgeReanchor_coordinates (m M t T : ℕ) (F : OctEdgeFrame) (p : Site) (k : Fin 3) :
    (bulkEdgeReanchor m M t T F p).val k =
      p.val k - (bulkEdgeAnchor m F t).val k + (bulkEdgeAnchor M F T).val k := by
  change p.val k - ((bulkEdgeAnchor m F t).val k - (bulkEdgeAnchor M F T).val k) = _
  omega

def InBulkEdgeBox (m : ℕ) (F : OctEdgeFrame) (t D : ℕ) (p : Site) : Prop :=
  ∀ k : Fin 3, |p.val k - (bulkEdgeAnchor m F t).val k| ≤ (D : ℤ)

theorem bulkEdgeReanchor_in_box (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (hp : InBulkEdgeBox m F t D p) : InBulkEdgeBox M F T D (bulkEdgeReanchor m M t T F p) := by
  intro k
  rw [bulkEdgeReanchor_coordinates]
  have heq : p.val k - (bulkEdgeAnchor m F t).val k + (bulkEdgeAnchor M F T).val k -
      (bulkEdgeAnchor M F T).val k = p.val k - (bulkEdgeAnchor m F t).val k := by omega
  rw [heq]
  exact hp k

theorem bulkEdgeBox_face_bound (m : ℕ) (F : OctEdgeFrame) (t D : ℕ) (p : Site)
    (hp : InBulkEdgeBox m F t D p) (i : Fin 4) :
    |tetraCoordinate m p.val i - tetraCoordinate m (bulkEdgeAnchor m F t).val i| ≤ 3 * (D : ℤ) := by
  have hx := abs_le.mp (hp 0)
  have hy := abs_le.mp (hp 1)
  have hz := abs_le.mp (hp 2)
  apply abs_le.mpr
  fin_cases i <;> dsimp [tetraCoordinate] <;> constructor <;> omega

theorem bulkEdgeReanchor_tetra (m M t T : ℕ) (F : OctEdgeFrame) (p : Site) (i : Fin 4) :
    tetraCoordinate M (bulkEdgeReanchor m M t T F p).val i = tetraCoordinate m p.val i -
      tetraCoordinate m (bulkEdgeAnchor m F t).val i + tetraCoordinate M (bulkEdgeAnchor M F T).val i := by
  have hx := bulkEdgeReanchor_coordinates m M t T F p 0
  have hy := bulkEdgeReanchor_coordinates m M t T F p 1
  have hz := bulkEdgeReanchor_coordinates m M t T F p 2
  fin_cases i <;> dsimp [tetraCoordinate] <;> omega

set_option maxHeartbeats 1200000 in
theorem bulkEdgeReanchor_face_le_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) (i : Fin 4) (s c : ℤ)
    (hs : s = 1 ∨ s = -1) (hc : -2 ≤ c ∧ c ≤ 2) :
    s * tetraCoordinate M (bulkEdgeReanchor m M t T F p).val i ≤ octRadius M + c ↔
      s * tetraCoordinate m p.val i ≤ octRadius m + c := by
  have hm : 1 ≤ m := by omega
  have hM : 1 ≤ M := by omega
  have hOld := octEdgeZigzag_even hm F t
  have hNew := octEdgeZigzag_even hM F T
  change InASublattice (bulkEdgeAnchor m F t).val ∧
    tetraCoordinate m (bulkEdgeAnchor m F t).val F.k = octRadius m ∧
    tetraCoordinate m (bulkEdgeAnchor m F t).val F.j = -octRadius m ∧
    tetraCoordinate m (bulkEdgeAnchor m F t).val F.a = -octRadius m + 4 * (t : ℤ) ∧
    tetraCoordinate m (bulkEdgeAnchor m F t).val F.b = octRadius m - 4 * (t : ℤ) at hOld
  change InASublattice (bulkEdgeAnchor M F T).val ∧
    tetraCoordinate M (bulkEdgeAnchor M F T).val F.k = octRadius M ∧
    tetraCoordinate M (bulkEdgeAnchor M F T).val F.j = -octRadius M ∧
    tetraCoordinate M (bulkEdgeAnchor M F T).val F.a = -octRadius M + 4 * (T : ℤ) ∧
    tetraCoordinate M (bulkEdgeAnchor M F T).val F.b = octRadius M - 4 * (T : ℤ) at hNew
  have hbound := abs_le.mp (bulkEdgeBox_face_bound m F t D p hp i)
  have htrans := bulkEdgeReanchor_tetra m M t T F p i
  rcases F.index_cases i with rfl | rfl | rfl | rfl
  · rw [hOld.2.1] at hbound
    rw [hOld.2.1, hNew.2.1] at htrans
    rcases hs with rfl | rfl <;> dsimp [octRadius] at hbound htrans ⊢ <;> omega
  · rw [hOld.2.2.1] at hbound
    rw [hOld.2.2.1, hNew.2.2.1] at htrans
    rcases hs with rfl | rfl <;> dsimp [octRadius] at hbound htrans ⊢ <;> omega
  · rw [hOld.2.2.2.1] at hbound
    rw [hOld.2.2.2.1, hNew.2.2.2.1] at htrans
    rcases hs with rfl | rfl <;> dsimp [octRadius] at hbound htrans ⊢ <;> omega
  · rw [hOld.2.2.2.2] at hbound
    rw [hOld.2.2.2.2, hNew.2.2.2.2] at htrans
    rcases hs with rfl | rfl <;> dsimp [octRadius] at hbound htrans ⊢ <;> omega

theorem bulkEdgeReanchor_face_eq_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) (i : Fin 4) (s c : ℤ)
    (hs : s = 1 ∨ s = -1) (hc : -1 ≤ c ∧ c ≤ 2) :
    s * tetraCoordinate M (bulkEdgeReanchor m M t T F p).val i = octRadius M + c ↔
      s * tetraCoordinate m p.val i = octRadius m + c := by
  have hle := bulkEdgeReanchor_face_le_iff m M t T F D p ht htm hT hTM hp i s c hs (by omega)
  have hlt := bulkEdgeReanchor_face_le_iff m M t T F D p ht htm hT hTM hp i s (c - 1) hs (by omega)
  omega

theorem bulkEdgeReanchor_mem_octahedron_iff (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    bulkEdgeReanchor m M t T F p ∈ octahedron M ↔ p ∈ octahedron m := by
  rw [mem_octahedron, mem_octahedron]
  unfold InOctahedron
  have hle := fun i => bulkEdgeReanchor_face_le_iff m M t T F D p ht htm hT hTM hp i 1 0
    (Or.inl rfl) (by omega)
  have hge := fun i => bulkEdgeReanchor_face_le_iff m M t T F D p ht htm hT hTM hp i (-1) 1
    (Or.inr rfl) (by omega)
  constructor
  · intro h i
    have hi := h i
    have hlo := hge i
    have hup := hle i
    dsimp [octRadius] at hi hlo hup ⊢
    omega
  · intro h i
    have hi := h i
    have hlo := hge i
    have hup := hle i
    dsimp [octRadius] at hi hlo hup ⊢
    omega

end ProteinFolding.Tetrahedral
