import ProteinFolding.Tetrahedral.NearFieldUnitCapFamily
import ProteinFolding.Tetrahedral.NearFieldWeaveWords
import ProteinFolding.Tetrahedral.NearFieldWordTransport
import ProteinFolding.Tetrahedral.NearFieldAssemblySupport
import ProteinFolding.Tetrahedral.FarFieldMixedRouting
import Mathlib.Data.List.OfFn

/-! Simultaneous mixed-cap routing followed by actual-word assembly. The
local unit and selected-column certificates are the concrete inputs. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 500000

private def innerLinkerRouteIndex {L : ℕ}
    (i : Fin (List.replicate (L - 2) Residue.P).length) : Fin L :=
  ⟨i.val + 1, by
    have hi := i.isLt
    simp only [List.length_replicate] at hi
    omega⟩

private theorem innerLinkerPiece_pos {L : ℕ} (hL : 3 ≤ L) (f : Fold tetrahedralLattice L)
    (i : Fin (innerLinkerPiece hL f).word.length) :
    (innerLinkerPiece hL f).fold.pos i = f.pos (innerLinkerRouteIndex i) := rfl

theorem weaveSeams_ofFn (n : ℕ) (us : Fin (n + 1) → PositionedWord) (ls : Fin n → PositionedWord)
    (hfirst : ∀ r, tetrahedralLattice.Adj (us r.castSucc).last (ls r).first)
    (hlast : ∀ r, tetrahedralLattice.Adj (ls r).last (us r.succ).first) :
    weaveSeams (List.ofFn us) (List.ofFn ls) := by
  induction n with
  | zero => simp [List.ofFn_succ, weaveSeams]
  | succ n ih =>
    have ht := ih (fun i => us i.succ) (fun i => ls i.succ)
      (by
        intro i
        have hi : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
        change tetrahedralLattice.Adj (us i.castSucc.succ).last (ls i.succ).first
        rw [hi]
        exact hfirst i.succ)
      (fun i => hlast i.succ)
    simpa only [List.ofFn_succ, weaveSeams] using
      And.intro (hfirst 0) (And.intro (hlast 0) ht)

theorem mixedCap_weave_exists {m n : ℕ} (us : Fin (n + 1) → PositionedWord)
    (hpair : ∀ i j, i ≠ j → WordsDisjoint (us i) (us j))
    (hlen : ∀ i, 2 ≤ (us i).word.length)
    (hlastDangling : ∀ i, IsDangling m (us i).last)
    (hfirstDangling : ∀ i, 0 < i.val → IsDangling m (us i).first)
    (e : FarField.Pairing (2 * n) n) (C : Fin (2 * n) → DanglingColumn m)
    (hseed : Function.Injective (fun i => (C i).seed))
    (hadj : ∀ i, tetrahedralLattice.Adj (wireCapSite us e i) ((C i).point 1))
    (O : Set Site) (hO : ∀ i, ∀ x ∈ foldSites (us i).fold, x ∈ O)
    (hlow : ∀ x ∈ O, FarField.rho (octRadius m) x < 20 * (m : ℤ) + 21)
    (hclear : ∀ i t, 1 ≤ t → (C i).point t ∈ O → False)
    (L : Fin n → ℕ) (hL : ∀ r, FarField.uniformLinkerLength m (2 * n) ≤ L r)
    (hL3 : ∀ r, 3 ≤ L r)
    (hparity : ∀ r, FarField.CapParity (wireCapSite us e (e.first r))
      (wireCapSite us e (e.second r)) (L r))
    (gaps : ℕ → ℕ) (hgap : ∀ r, L r - 2 = gaps r.val) :
    ∃ ls : List PositionedWord,
      ls.map PositionedWord.word = (List.range n).map (fun j => List.replicate (gaps j) .P) ∧
      (∀ l ∈ ls, hSupport l.word l.fold = ∅) ∧
      Nonempty (PieceAssembly (weavePieces (List.ofFn us) ls)) := by
  obtain ⟨f, hf, ht, hd, ho⟩ := FarField.mixed_cap_routes_avoiding C hseed (wireCapSite us e)
    (fun i => routedCapSite_dangling m us hlastDangling hfirstDangling (e i))
    (wireCapSite_injective us e hpair hlen) hadj e O hlow hclear L hL hparity
  let lp : Fin n → PositionedWord := fun r => innerLinkerPiece (hL3 r) (f r)
  let ls := List.ofFn lp
  have hwords : ls.map PositionedWord.word = (List.range n).map (fun j => List.replicate (gaps j) .P) := by
    rw [List.map_ofFn]
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp only [List.getElem_ofFn, Function.comp_def, List.getElem_map, List.getElem_range]
    change List.replicate (L ⟨i, by simpa only [List.length_ofFn] using hi⟩ - 2) Residue.P = _
    rw [hgap]
  have hlinkPair : ls.Pairwise WordsDisjoint := by
    apply List.pairwise_ofFn.mpr
    intro r s hrs
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha⟩ := (mem_foldSites _ _).mp hx
    obtain ⟨b, hb⟩ := (mem_foldSites _ _).mp hy
    have har : (f r).pos (innerLinkerRouteIndex a) = x :=
      (innerLinkerPiece_pos (hL3 r) (f r) a).symm.trans ha
    have hbs : (f s).pos (innerLinkerRouteIndex b) = x :=
      (innerLinkerPiece_pos (hL3 s) (f s) b).symm.trans hb
    exact Set.disjoint_left.mp (hd r s (ne_of_lt hrs))
      ⟨innerLinkerRouteIndex a, har⟩ ⟨innerLinkerRouteIndex b, hbs⟩
  have hcross : ∀ u ∈ List.ofFn us, ∀ l ∈ ls, WordsDisjoint u l := by
    intro u hu l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hl
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, rfl⟩ := (mem_foldSites _ _).mp hy
    exact innerLinkerFold_avoids_obstacles (hL3 r) (f r) O
      (wireCapSite us e (e.first r)) (wireCapSite us e (e.second r)) (hf r) (ht r)
      (fun j hj => ho r ((f r).pos j) ⟨j, rfl⟩ hj) a (hO i _ hx)
  have hseams : weaveSeams (List.ofFn us) ls := by
    apply weaveSeams_ofFn
    · intro r
      exact innerLinker_first_seam (hL3 r) (f r) (us r.castSucc).last
        (fun a ha => (hf r a ha).trans (wireCapSite_first us e r))
    · intro r
      exact innerLinker_last_seam (hL3 r) (f r) (us r.succ).first
        (fun a ha => (ht r a ha).trans (wireCapSite_second us e r))
  refine ⟨ls, hwords, ?_, ?_⟩
  · intro l hl
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hl
    exact innerLinkerPiece_hSupport (hL3 r) (f r)
  · refine ⟨assembleWeave (List.ofFn us) ls ?_
      (List.pairwise_ofFn.mpr (fun {i j} hij => hpair i j (ne_of_lt hij))) hlinkPair hcross hseams⟩
    intro heq
    have hh := congrArg List.length heq
    simp only [List.length_ofFn, List.length_nil] at hh
    omega

structure MixedUnitFamily (m n : ℕ) where
  units : Fin (n + 1) → PositionedWord
  pairwise : ∀ i j, i ≠ j → WordsDisjoint (units i) (units j)
  lengths : ∀ i, 2 ≤ (units i).word.length
  last_dangling : ∀ i, IsDangling m (units i).last
  first_dangling : ∀ i, 0 < i.val → IsDangling m (units i).first
  pairing : FarField.Pairing (2 * n) n
  columns : Fin (2 * n) → DanglingColumn m
  seeds_injective : Function.Injective (fun i => (columns i).seed)
  cap_adjacent : ∀ i, tetrahedralLattice.Adj (wireCapSite units pairing i) ((columns i).point 1)
  obstacles : Set Site
  unit_sites : ∀ i, ∀ x ∈ foldSites (units i).fold, x ∈ obstacles
  low : ∀ x ∈ obstacles, FarField.rho (octRadius m) x < 20 * (m : ℤ) + 21
  clear : ∀ i t, 1 ≤ t → (columns i).point t ∈ obstacles → False
  linkerLength : Fin n → ℕ
  linker_large : ∀ r, FarField.uniformLinkerLength m (2 * n) ≤ linkerLength r
  linker_three : ∀ r, 3 ≤ linkerLength r
  linker_parity : ∀ r, FarField.CapParity (wireCapSite units pairing (pairing.first r))
    (wireCapSite units pairing (pairing.second r)) (linkerLength r)
  gaps : ℕ → ℕ
  gaps_eq : ∀ r, linkerLength r - 2 = gaps r.val

theorem MixedUnitFamily.reduction_fold_exists {m n : ℕ} (d : MixedUnitFamily m n)
    (bodies : List Sequence) (hbodyLength : bodies.length = n)
    (hwords : (List.ofFn d.units).map PositionedWord.word = [.H, .P] :: bodies.map capWord)
    (hH : ∀ i, hSupport (d.units i).word (d.units i).fold ⊆ octahedron m)
    (hcount : hydrophobicCount (assembleReductionWord d.gaps bodies) = octahedralNumber m) :
    ∃ f : Fold tetrahedralLattice (assembleReductionWord d.gaps bodies).length,
      hSupport (assembleReductionWord d.gaps bodies) f = octahedron m := by
  obtain ⟨ls, hls, hP, ⟨a⟩⟩ := mixedCap_weave_exists d.units d.pairwise d.lengths d.last_dangling
    d.first_dangling d.pairing d.columns d.seeds_injective d.cap_adjacent d.obstacles d.unit_sites
    d.low d.clear d.linkerLength d.linker_large d.linker_three d.linker_parity d.gaps d.gaps_eq
  have hword : a.piece.word = assembleReductionWord d.gaps bodies :=
    a.word_eq.trans (pieceWords_weave_reduction _ _ _ _ hwords (by rw [hbodyLength]; exact hls))
  have hsub : hSupport a.piece.word a.piece.fold ⊆ octahedron m := by
    apply a.hSupport_subset
    intro p hp
    rcases mem_weavePieces (List.ofFn d.units) ls p hp with hp | hp
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      exact hH i
    · rw [hP p hp]
      exact Finset.empty_subset _
  let f := transportWordFold hword a.piece.fold
  refine ⟨f, hSupport_eq_oct_of_subset_count (S := assembleReductionWord d.gaps bodies) f m ?_ hcount⟩
  rw [transportWordFold_hSupport]
  exact hsub

end ProteinFolding.Tetrahedral.NearField
