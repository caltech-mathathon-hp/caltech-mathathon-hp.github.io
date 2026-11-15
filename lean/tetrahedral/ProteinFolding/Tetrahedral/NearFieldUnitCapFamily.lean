import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly
import ProteinFolding.Tetrahedral.FarFieldFamilies

/-! Routed caps are previous-piece exits and next-piece entries. The final
piece's trailing cap remains local and has no routed wire. -/

namespace ProteinFolding.Tetrahedral.NearField

noncomputable def unitCapPairing (n : ℕ) : FarField.Pairing (2 * n) n :=
  Fintype.equivOfCardEq (by simp [Nat.mul_comm])

theorem PositionedWord.first_mem_sites (p : PositionedWord) : p.first ∈ foldSites p.fold :=
  (mem_foldSites _ _).mpr ⟨⟨0, p.length_pos⟩, p.first_eq _ rfl⟩

theorem PositionedWord.last_mem_sites (p : PositionedWord) : p.last ∈ foldSites p.fold := by
  let a : Fin p.word.length := ⟨p.word.length - 1, by have h := p.length_pos; omega⟩
  have ha : a.val + 1 = p.word.length := by
    change p.word.length - 1 + 1 = p.word.length
    have h := p.length_pos
    omega
  exact (mem_foldSites p.fold p.last).mpr ⟨a, p.last_eq a ha⟩

theorem PositionedWord.first_ne_last (p : PositionedWord) (hlen : 2 ≤ p.word.length) : p.first ≠ p.last := by
  intro heq
  let a : Fin p.word.length := ⟨0, p.length_pos⟩
  let b : Fin p.word.length := ⟨p.word.length - 1, by omega⟩
  have hi := p.fold.injective_pos ((p.first_eq a rfl).trans
    (heq.trans (p.last_eq b (by dsimp [b]; omega)).symm))
  have hv := congrArg Fin.val hi
  dsimp [a, b] at hv
  omega

def wordEndpoint (p : PositionedWord) (first : Bool) : Site := if first then p.first else p.last

theorem wordEndpoint_mem_sites (p : PositionedWord) (b : Bool) : wordEndpoint p b ∈ foldSites p.fold := by
  cases b
  · exact p.last_mem_sites
  · exact p.first_mem_sites

theorem wordEndpoint_injective (p : PositionedWord) (hlen : 2 ≤ p.word.length) :
    Function.Injective (wordEndpoint p) := by
  intro b c heq
  cases b <;> cases c
  · rfl
  · exact False.elim (p.first_ne_last hlen heq.symm)
  · exact False.elim (p.first_ne_last hlen heq)
  · rfl

theorem unitEndpointFamily_injective {n : ℕ} (us : Fin (n + 1) → PositionedWord)
    (hpair : ∀ i j, i ≠ j → WordsDisjoint (us i) (us j))
    (hlen : ∀ i, 2 ≤ (us i).word.length) :
    Function.Injective (fun a : Fin (n + 1) × Bool => wordEndpoint (us a.1) a.2) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ heq
  change wordEndpoint (us i) b = wordEndpoint (us j) c at heq
  have hij : i = j := by
    by_contra hne
    have hx := wordEndpoint_mem_sites (us i) b
    have hy := wordEndpoint_mem_sites (us j) c
    rw [heq] at hx
    exact Finset.disjoint_left.mp (hpair i j hne) hx hy
  subst j
  exact Prod.ext rfl (wordEndpoint_injective (us i) (hlen i) heq)

def routedCapLabel {n : ℕ} (a : Fin n × Bool) : Fin (n + 1) × Bool :=
  if a.2 then (a.1.succ, true) else (a.1.castSucc, false)

theorem routedCapLabel_snd {n : ℕ} (a : Fin n × Bool) : (routedCapLabel a).2 = a.2 := by
  rcases a with ⟨r, b⟩
  cases b <;> rfl

theorem routedCapLabel_injective (n : ℕ) : Function.Injective (@routedCapLabel n) := by
  rintro ⟨r, b⟩ ⟨s, c⟩ heq
  have hb := congrArg Prod.snd heq
  rw [routedCapLabel_snd, routedCapLabel_snd] at hb
  change b = c at hb
  subst c
  cases b
  · have hi := congrArg (fun a : Fin (n + 1) × Bool => a.1) heq
    change r.castSucc = s.castSucc at hi
    exact Prod.ext (Fin.castSucc_injective n hi) rfl
  · have hi := congrArg (fun a : Fin (n + 1) × Bool => a.1) heq
    change r.succ = s.succ at hi
    exact Prod.ext (Fin.succ_injective n hi) rfl

theorem routedCapLabel_ne_final (n : ℕ) (a : Fin n × Bool) :
    routedCapLabel a ≠ (Fin.last n, false) := by
  rintro heq
  have hb := congrArg Prod.snd heq
  rw [routedCapLabel_snd] at hb
  rcases a with ⟨r, b⟩
  cases b
  · have hi := congrArg (fun a : Fin (n + 1) × Bool => a.1.val) heq
    change r.val = n at hi
    have hr := r.isLt
    omega
  · change true = false at hb
    cases hb

def routedCapSite {n : ℕ} (us : Fin (n + 1) → PositionedWord) (a : Fin n × Bool) : Site :=
  wordEndpoint (us (routedCapLabel a).1) (routedCapLabel a).2

theorem routedCapSite_injective {n : ℕ} (us : Fin (n + 1) → PositionedWord)
    (hpair : ∀ i j, i ≠ j → WordsDisjoint (us i) (us j))
    (hlen : ∀ i, 2 ≤ (us i).word.length) : Function.Injective (routedCapSite us) :=
  (unitEndpointFamily_injective us hpair hlen).comp (routedCapLabel_injective n)

theorem routedCapSite_ne_final {n : ℕ} (us : Fin (n + 1) → PositionedWord)
    (hpair : ∀ i j, i ≠ j → WordsDisjoint (us i) (us j))
    (hlen : ∀ i, 2 ≤ (us i).word.length) (a : Fin n × Bool) :
    routedCapSite us a ≠ (us (Fin.last n)).last := by
  intro heq
  have hi := unitEndpointFamily_injective us hpair hlen
    (a₁ := routedCapLabel a) (a₂ := (Fin.last n, false)) (show
    wordEndpoint (us (routedCapLabel a).1) (routedCapLabel a).2 = wordEndpoint (us (Fin.last n)) false from heq)
  exact routedCapLabel_ne_final n a hi

theorem routedCapSite_dangling {n : ℕ} (m : ℕ) (us : Fin (n + 1) → PositionedWord)
    (hlast : ∀ i, IsDangling m (us i).last)
    (hfirst : ∀ i, 0 < i.val → IsDangling m (us i).first) (a : Fin n × Bool) :
    IsDangling m (routedCapSite us a) := by
  rcases a with ⟨r, b⟩
  cases b
  · exact hlast r.castSucc
  · exact hfirst r.succ (by change 0 < r.val + 1; omega)

theorem routedCapSite_mem_obstacles {n : ℕ} (us : Fin (n + 1) → PositionedWord) (O : Set Site)
    (hO : ∀ i, ∀ s ∈ foldSites (us i).fold, s ∈ O) (a : Fin n × Bool) : routedCapSite us a ∈ O :=
  hO (routedCapLabel a).1
    (wordEndpoint (us (routedCapLabel a).1) (routedCapLabel a).2)
    (wordEndpoint_mem_sites (us (routedCapLabel a).1) (routedCapLabel a).2)

def wireCapSite {n : ℕ} (us : Fin (n + 1) → PositionedWord) (e : FarField.Pairing (2 * n) n)
    (a : Fin (2 * n)) : Site := routedCapSite us (e a)

theorem wireCapSite_first {n : ℕ} (us : Fin (n + 1) → PositionedWord) (e : FarField.Pairing (2 * n) n)
    (r : Fin n) : wireCapSite us e (e.first r) = (us r.castSucc).last := by
  simp [wireCapSite, FarField.Pairing.first, routedCapSite, routedCapLabel, wordEndpoint]

theorem wireCapSite_second {n : ℕ} (us : Fin (n + 1) → PositionedWord) (e : FarField.Pairing (2 * n) n)
    (r : Fin n) : wireCapSite us e (e.second r) = (us r.succ).first := by
  simp [wireCapSite, FarField.Pairing.second, routedCapSite, routedCapLabel, wordEndpoint]

theorem wireCapSite_injective {n : ℕ} (us : Fin (n + 1) → PositionedWord) (e : FarField.Pairing (2 * n) n)
    (hpair : ∀ i j, i ≠ j → WordsDisjoint (us i) (us j))
    (hlen : ∀ i, 2 ≤ (us i).word.length) : Function.Injective (wireCapSite us e) :=
  (routedCapSite_injective us hpair hlen).comp e.injective

theorem wireCapSite_ne_final {n : ℕ} (us : Fin (n + 1) → PositionedWord) (e : FarField.Pairing (2 * n) n)
    (hpair : ∀ i j, i ≠ j → WordsDisjoint (us i) (us j))
    (hlen : ∀ i, 2 ≤ (us i).word.length) (a : Fin (2 * n)) :
    wireCapSite us e a ≠ (us (Fin.last n)).last := routedCapSite_ne_final us hpair hlen (e a)

end ProteinFolding.Tetrahedral.NearField
