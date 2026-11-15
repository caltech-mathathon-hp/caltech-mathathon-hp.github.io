import ProteinFolding.Tetrahedral.BulkFastLocal
import Mathlib.Data.List.Chain

/-! Finite lists certify actual cover walks and transport them between sizes. -/

namespace ProteinFolding.Tetrahedral

theorem bulkFastCoverChain_reachable (m : ℕ) (points : List Site)
    (h : points.IsChain (bulkFastCoverBond m)) (p q : Site)
    (hp : p ∈ points) (hq : q ∈ points) : (bulkCoverGraph m).Reachable p q := by
  cases points with
  | nil => simp only [List.not_mem_nil] at hp
  | cons r tail =>
    have hactual : (r :: tail).IsChain (bulkCoverGraph m).Adj :=
      h.imp (fun x y hxy => (bulkCoverBond_fast_iff m x y).mpr hxy)
    have hroot : ∀ s ∈ r :: tail, (bulkCoverGraph m).Reachable r s :=
      List.IsChain.induction (fun s => (bulkCoverGraph m).Reachable r s) (r :: tail) hactual
        (fun {_ _} hxy hs => hs.trans hxy.reachable) (fun _ => .refl _)
    exact (hroot p hp).symm.trans (hroot q hq)

theorem bulkFastCoverChain_vertex_map (m n : ℕ) (v : Fin 6) (D : ℕ) (points : List Site)
    (hm : D + 6 ≤ m) (hn : D + 6 ≤ n)
    (hbox : ∀ p ∈ points, InBulkVertexBox m v D p)
    (h : points.IsChain (bulkFastCoverBond m)) :
    (points.map (bulkReanchorSite m n v)).IsChain (bulkFastCoverBond n) := by
  apply (List.isChain_map (bulkReanchorSite m n v)).mpr
  apply h.imp_of_mem_imp
  intro p q hp hq hpq
  apply (bulkCoverBond_fast_iff n _ _).mp
  exact (bulkReanchor_coverBond_iff m n v D p q hm hn (hbox p hp) (hbox q hq)).mpr
    ((bulkCoverBond_fast_iff m p q).mpr hpq)

theorem bulkFastCoverChain_vertex_reachable (m n : ℕ) (v : Fin 6) (D : ℕ) (points : List Site)
    (hm : D + 6 ≤ m) (hn : D + 6 ≤ n)
    (hbox : ∀ p ∈ points, InBulkVertexBox m v D p)
    (h : points.IsChain (bulkFastCoverBond m)) (p q : Site)
    (hp : p ∈ points) (hq : q ∈ points) :
    (bulkCoverGraph n).Reachable (bulkReanchorSite m n v p) (bulkReanchorSite m n v q) :=
  bulkFastCoverChain_reachable n (points.map (bulkReanchorSite m n v))
    (bulkFastCoverChain_vertex_map m n v D points hm hn hbox h) _ _
    (List.mem_map.mpr ⟨p, hp, rfl⟩) (List.mem_map.mpr ⟨q, hq, rfl⟩)

end ProteinFolding.Tetrahedral
