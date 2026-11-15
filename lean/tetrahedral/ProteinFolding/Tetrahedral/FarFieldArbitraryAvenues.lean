import ProteinFolding.Tetrahedral.FarFieldQuadrants
import ProteinFolding.Tetrahedral.FarFieldAvenueClassification

namespace ProteinFolding.Tetrahedral.FarField

def InQuadrant (R : ℤ) (q : Quadrant) (p : Site) : Prop :=
  (if q.1 then Y R p < 0 else 0 < Y R p) ∧
    (if q.2 then Z p < 0 else 0 < Z p)

def quadrantUnmap (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) : Site :=
  let p' := if q.1 then flipY R hR p else p
  if q.2 then flipZ p' else p'

@[simp] theorem flipY_flipY (R : ℤ) (hR : R % 2 = 0) (p : Site) :
    flipY R hR (flipY R hR p) = p := flipY_involutive R hR p

@[simp] theorem flipZ_flipZ (p : Site) : flipZ (flipZ p) = p := flipZ_involutive p

@[simp] theorem quadrantMap_unmap (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) :
    quadrantMap R hR q (quadrantUnmap R hR q p) = p := by
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> simp [quadrantMap, quadrantUnmap]

@[simp] theorem quadrantUnmap_map (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) :
    quadrantUnmap R hR q (quadrantMap R hR q p) = p := by
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> simp [quadrantMap, quadrantUnmap]

theorem quadrantMap_positive_iff (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) :
    InQuadrant R q (quadrantMap R hR q p) ↔ PositiveQuadrant R p := by
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> simp [quadrantMap, InQuadrant, PositiveQuadrant]

@[simp] theorem quadrantUnmap_rho (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) :
    rho R (quadrantUnmap R hR q p) = rho R p := by
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> simp [quadrantUnmap]

@[simp] theorem quadrantUnmap_alpha (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) :
    alpha R (quadrantUnmap R hR q p) = alpha R p := by
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> simp [quadrantUnmap]

def AvenueMembership (R u a : ℤ) (q : Quadrant) (p : Site) : Prop :=
  InQuadrant R q p ∧ (rho R p = u ∨ rho R p = u + 2) ∧
    (alpha R p = a ∨ alpha R p = a + 2)

theorem quadrantAvenue_member (R : ℤ) (hR : R % 2 = 0) (q : Quadrant)
    (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) :
    AvenueMembership R (privateLevel R c up) (privateStrip R c) q
      (quadrantAvenue R hR q c hc up n) := by
  let k := if q.1 = q.2 then n else -n
  have h := avenue_private R c hc up k hy hz
  refine ⟨(quadrantMap_positive_iff R hR q _).2 h.1, ?_⟩
  simpa only [quadrantAvenue, k, quadrantMap_rho, quadrantMap_alpha] using h.2

theorem quadrantAvenue_exhaustive (R : ℤ) (hR : R % 2 = 0) (q : Quadrant)
    (c : Site) (hc : InASublattice c.val) (up : Bool) (p : Site)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c)
    (hp : AvenueMembership R (privateLevel R c up) (privateStrip R c) q p) :
    ∃ n : ℤ, quadrantAvenue R hR q c hc up n = p := by
  let p' := quadrantUnmap R hR q p
  have hp' : PositiveQuadrant R p' :=
    (quadrantMap_positive_iff R hR q p').1 (by simpa only [p', quadrantMap_unmap] using hp.1)
  have hrho : rho R p' = privateLevel R c up ∨ rho R p' = privateLevel R c up + 2 := by
    simpa only [p', quadrantUnmap_rho] using hp.2.1
  have halpha : alpha R p' = privateStrip R c ∨ alpha R p' = privateStrip R c + 2 := by
    simpa only [p', quadrantUnmap_alpha] using hp.2.2
  have he := avenue_exhaustive R c hc up p' hy hz hp' hrho halpha
  have he' := congrArg (quadrantMap R hR q) he
  simp only [p', quadrantMap_unmap] at he'
  by_cases hq : q.1 = q.2
  · refine ⟨X p' - X c, ?_⟩
    simpa only [quadrantAvenue, if_pos hq] using he'.symm
  · refine ⟨-(X p' - X c), ?_⟩
    simpa only [quadrantAvenue, if_neg hq, neg_neg] using he'.symm

theorem quadrantAvenue_one_per_x (R : ℤ) (hR : R % 2 = 0) (q : Quadrant)
    (c : Site) (hc : InASublattice c.val) (up : Bool)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) (x : ℤ) :
    ∃! p : Site, X p = x ∧ AvenueMembership R (privateLevel R c up) (privateStrip R c) q p := by
  refine ⟨quadrantAvenue R hR q c hc up (x - X (quadrantMap R hR q c)), ?_, ?_⟩
  · refine ⟨?_, quadrantAvenue_member R hR q c hc up _ hy hz⟩
    rw [quadrantAvenue_x]
    omega
  · intro p hp
    obtain ⟨n, rfl⟩ := quadrantAvenue_exhaustive R hR q c hc up p hy hz hp.2
    have hn := hp.1
    rw [quadrantAvenue_x] at hn
    have hn' : n = x - X (quadrantMap R hR q c) := by omega
    rw [hn']

end ProteinFolding.Tetrahedral.FarField
