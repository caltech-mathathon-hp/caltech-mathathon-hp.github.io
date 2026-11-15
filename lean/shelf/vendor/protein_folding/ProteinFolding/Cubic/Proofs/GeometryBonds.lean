import ProteinFolding.Cubic.Proofs.GeometryLines
import ProteinFolding.Cubic.Proofs.CertificatesDirections
import Mathlib.Data.Finset.Sigma

/-! Relating sequence-index bonds to positively oriented geometric edges. -/

namespace ProteinFolding.CubicGeometry

theorem stepPlus_adj (p : Site) (k : Fin 3) : cubicLattice.Adj p (stepPlus k p) := by
  have h : ∃ d : Fin 6, CubicCertificates.step p d = stepPlus k p := by
    match k with
    | 0 => exact ⟨0, CubicCertificates.site_ext (by simp [stepPlus, CubicCertificates.step])
        (by simp [stepPlus, CubicCertificates.step]) (by simp [stepPlus, CubicCertificates.step])⟩
    | 1 => exact ⟨2, CubicCertificates.site_ext (by simp [stepPlus, CubicCertificates.step])
        (by simp [stepPlus, CubicCertificates.step]) (by simp [stepPlus, CubicCertificates.step])⟩
    | 2 => exact ⟨4, CubicCertificates.site_ext (by simp [stepPlus, CubicCertificates.step])
        (by simp [stepPlus, CubicCertificates.step]) (by simp [stepPlus, CubicCertificates.step])⟩
  obtain ⟨d, hd⟩ := h
  rw [← hd]
  exact CubicCertificates.step_adj p d

theorem adj_stepPlus {p q : Site} (h : cubicLattice.Adj p q) :
    ∃ k : Fin 3, q = stepPlus k p ∨ p = stepPlus k q := by
  obtain ⟨d, rfl⟩ := CubicCertificates.adj_step h
  match d with
  | 0 => refine ⟨0, Or.inl ?_⟩; apply CubicCertificates.site_ext <;> simp [stepPlus, CubicCertificates.step]
  | 1 => refine ⟨0, Or.inr ?_⟩; apply CubicCertificates.site_ext <;> simp [stepPlus, CubicCertificates.step]
  | 2 => refine ⟨1, Or.inl ?_⟩; apply CubicCertificates.site_ext <;> simp [stepPlus, CubicCertificates.step]
  | 3 => refine ⟨1, Or.inr ?_⟩; apply CubicCertificates.site_ext <;> simp [stepPlus, CubicCertificates.step]
  | 4 => refine ⟨2, Or.inl ?_⟩; apply CubicCertificates.site_ext <;> simp [stepPlus, CubicCertificates.step]
  | 5 => refine ⟨2, Or.inr ?_⟩; apply CubicCertificates.site_ext <;> simp [stepPlus, CubicCertificates.step]

def height (p : Site) : ℤ := p 0 + p 1 + p 2

theorem height_stepPlus (p : Site) (k : Fin 3) : height (stepPlus k p) = height p + 1 := by
  match k with
  | 0 => simp [height, stepPlus]; omega
  | 1 => simp [height, stepPlus]; omega
  | 2 => simp [height, stepPlus]; omega

theorem stepPlus_axis_unique (p : Site) {k l : Fin 3}
    (h : stepPlus k p = stepPlus l p) : k = l := by
  by_contra hne
  have hk := congrFun h k
  simp [stepPlus, hne] at hk

def EdgeEnds (e : Fin 3 × Site) (p q : Site) : Prop :=
  (p = e.2 ∧ q = stepPlus e.1 e.2) ∨ (q = e.2 ∧ p = stepPlus e.1 e.2)

theorem edgeEnds_unique {e e' : Fin 3 × Site} {p q : Site}
    (h : EdgeEnds e p q) (h' : EdgeEnds e' p q) : e = e' := by
  rcases e with ⟨k, a⟩
  rcases e' with ⟨l, b⟩
  rcases h with ⟨hp, hq⟩ | ⟨hq, hp⟩ <;> rcases h' with ⟨hp', hq'⟩ | ⟨hq', hp'⟩
  · have hab : a = b := hp.symm.trans hp'
    subst b
    have hkl := stepPlus_axis_unique a (hq.symm.trans hq')
    exact Prod.ext hkl rfl
  · have ha := height_stepPlus a k
    have hb := height_stepPlus b l
    have hpa := congrArg height hp
    have hqa := congrArg height hq
    have hpb := congrArg height hp'
    have hqb := congrArg height hq'
    dsimp only at *
    omega
  · have ha := height_stepPlus a k
    have hb := height_stepPlus b l
    have hpa := congrArg height hp
    have hqa := congrArg height hq
    have hpb := congrArg height hp'
    have hqb := congrArg height hq'
    dsimp only at *
    omega
  · have hab : a = b := hq.symm.trans hq'
    subst b
    have hkl := stepPlus_axis_unique a (hp.symm.trans hp')
    exact Prod.ext hkl rfl

def positiveEdgeSet (s : Finset Site) : Finset (Fin 3 × Site) :=
  (Finset.univ ×ˢ s).filter fun e => stepPlus e.1 e.2 ∈ s

theorem positiveEdgeSet_card (s : Finset Site) :
    (positiveEdgeSet s).card = positiveEdgeCount s := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := (Finset.univ : Finset (Fin 3))) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro k _
  have he : (positiveEdgeSet s).filter (fun e => e.1 = k) =
      (positiveEdges s k).image (fun p => (k, p)) := by
    ext ⟨j, p⟩
    simp [positiveEdgeSet, positiveEdges]
    aesop
  rw [he, Finset.card_image_of_injective]
  intro p q hpq
  exact congrArg Prod.snd hpq

theorem bondEdge_exists (S : Sequence) (f : Fold cubicLattice S.length)
    (ij : Fin S.length × Fin S.length) (hij : ij ∈ hhBonds S f) :
    ∃ e ∈ positiveEdgeSet (hSupport S f), EdgeEnds e (f.pos ij.1) (f.pos ij.2) := by
  have h : ij.1 < ij.2 ∧ S.get ij.1 = Residue.H ∧ S.get ij.2 = Residue.H ∧
      cubicLattice.Adj (f.pos ij.1) (f.pos ij.2) := by simpa [hhBonds] using hij
  have hi : f.pos ij.1 ∈ hSupport S f :=
    (mem_hSupport S f _).mpr ⟨ij.1, h.2.1, rfl⟩
  have hj : f.pos ij.2 ∈ hSupport S f :=
    (mem_hSupport S f _).mpr ⟨ij.2, h.2.2.1, rfl⟩
  obtain ⟨k, hk | hk⟩ := adj_stepPlus h.2.2.2
  · refine ⟨(k, f.pos ij.1), ?_, Or.inl ⟨rfl, hk⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hi⟩, hk ▸ hj⟩
  · refine ⟨(k, f.pos ij.2), ?_, Or.inr ⟨rfl, hk⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hj⟩, hk ▸ hi⟩

noncomputable def bondEdge (S : Sequence) (f : Fold cubicLattice S.length)
    (ij : Fin S.length × Fin S.length) (hij : ij ∈ hhBonds S f) : Fin 3 × Site :=
  Classical.choose (bondEdge_exists S f ij hij)

theorem bondEdge_spec (S : Sequence) (f : Fold cubicLattice S.length)
    (ij : Fin S.length × Fin S.length) (hij : ij ∈ hhBonds S f) :
    bondEdge S f ij hij ∈ positiveEdgeSet (hSupport S f) ∧
      EdgeEnds (bondEdge S f ij hij) (f.pos ij.1) (f.pos ij.2) :=
  Classical.choose_spec (bondEdge_exists S f ij hij)

theorem indexPair_eq_of_edgeEnds (S : Sequence) (f : Fold cubicLattice S.length)
    {ij kl : Fin S.length × Fin S.length} (hij : ij.1 < ij.2) (hkl : kl.1 < kl.2)
    {e : Fin 3 × Site} (hi : EdgeEnds e (f.pos ij.1) (f.pos ij.2))
    (hk : EdgeEnds e (f.pos kl.1) (f.pos kl.2)) : ij = kl := by
  rcases hi with ⟨hi, hj⟩ | ⟨hj, hi⟩ <;> rcases hk with ⟨hk, hl⟩ | ⟨hl, hk⟩
  · exact Prod.ext (f.injective_pos (hi.trans hk.symm)) (f.injective_pos (hj.trans hl.symm))
  · have h1 := f.injective_pos (hi.trans hl.symm)
    have h2 := f.injective_pos (hj.trans hk.symm)
    have hbad : kl.2 < kl.1 := h1 ▸ h2 ▸ hij
    exact False.elim (lt_asymm hkl hbad)
  · have h1 := f.injective_pos (hi.trans hl.symm)
    have h2 := f.injective_pos (hj.trans hk.symm)
    have hbad : kl.2 < kl.1 := h1 ▸ h2 ▸ hij
    exact False.elim (lt_asymm hkl hbad)
  · exact Prod.ext (f.injective_pos (hi.trans hk.symm)) (f.injective_pos (hj.trans hl.symm))

theorem bondCount_eq_positiveEdgeCount (S : Sequence) (f : Fold cubicLattice S.length) :
    bondCount S f = positiveEdgeCount (hSupport S f) := by
  classical
  rw [← positiveEdgeSet_card]
  apply Finset.card_bij (bondEdge S f)
  · intro ij hij
    exact (bondEdge_spec S f ij hij).1
  · intro ij hij kl hkl he
    have hi := (bondEdge_spec S f ij hij).2
    have hk := (bondEdge_spec S f kl hkl).2
    rw [← he] at hk
    apply indexPair_eq_of_edgeEnds S f (by simpa [hhBonds] using (Finset.mem_filter.mp hij).2.1)
      (by simpa [hhBonds] using (Finset.mem_filter.mp hkl).2.1) hi hk
  · rintro ⟨k, p⟩ he
    have hed := Finset.mem_filter.mp he
    obtain ⟨i, hi, hpi⟩ := (mem_hSupport S f p).mp (Finset.mem_product.mp hed.1).2
    obtain ⟨j, hj, hpj⟩ := (mem_hSupport S f (stepPlus k p)).mp hed.2
    have hne : i ≠ j := by
      intro hij
      have hs : p = stepPlus k p := hpi.symm.trans (hij ▸ hpj)
      have hh := congrArg height hs
      rw [height_stepPlus] at hh
      omega
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hm : (i, j) ∈ hhBonds S f := by
        simp only [hhBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
        refine ⟨hij, hi, hj, ?_⟩
        rw [hpi, hpj]
        exact stepPlus_adj p k
      refine ⟨(i, j), hm, ?_⟩
      exact edgeEnds_unique (bondEdge_spec S f (i, j) hm).2 (Or.inl ⟨hpi, hpj⟩)
    · have hm : (j, i) ∈ hhBonds S f := by
        simp only [hhBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
        refine ⟨hji, hj, hi, ?_⟩
        rw [hpi, hpj]
        exact (stepPlus_adj p k).symm
      refine ⟨(j, i), hm, ?_⟩
      exact edgeEnds_unique (bondEdge_spec S f (j, i) hm).2 (Or.inr ⟨hpi, hpj⟩)

end ProteinFolding.CubicGeometry
