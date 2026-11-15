# HP folding on the tetrahedral (diamond) lattice is NP-complete

Proof document, assembled from the working notes HP_tetrahedral_notes.md (which keep the history, the superseded
designs and more detail on the experiments). Method: that of Berger and Leighton for the cubic lattice ("Protein
folding in the hydrophobic-hydrophilic (HP) model is NP-complete", RECOMB 1998), with a new extremal lemma and new
gadgets, because their cube lemma and their surface gadgets do not exist on this lattice.

## 1. Result and status

**Theorem.** The following problem is NP-complete. Given a word s ∈ {H,P}* and an integer k: is there a self-avoiding
walk on the tetrahedral lattice, carrying the letters of s in order, with at least k pairs of H's on adjacent
sites? (Pairs that are consecutive in s are counted; leaving them out changes k by a constant of s.)

**What kind of proof this is.** Sections 2–7 (the upper bound, the uniqueness of the optimal shape, all local facts,
and the direction "optimal fold ⇒ packing") are ordinary hand proofs, complete. Section 8 (the direction "packing ⇒
optimal fold") is an explicit construction. Three of its lemmas are of different kinds:
* the Bulk Lemma (§8.3) and the near-field Lemma N (§8.4) are **computer-assisted**: each is reduced, by transfer
 arguments that are proved here, to finite checks carried out by the scripts listed in Appendix A;
* the far-field Lemma F (§8.5) is proved by hand.
Marks: [CHECKED …] = verified by the named script in the stated range. The complete construction was also run end
to end on many instances and each resulting fold was confirmed by an independent checker (Appendix A).
**Project revision, 14 November 2026.** Independent review found a residue-class gap in the original padding
argument of Lemma F(D). Parts D–E below replace it with a hand proof covering every sufficiently large length of
the required parity, an explicit packing-independent bound, and a separate coordinate checker. The earlier
arithmetic also received finite independent checks. The original companion archive has not been supplied in
this project, so the Bulk and near-field computer-assisted certificates remain unaudited here. This remains
a proof manuscript with computer-assisted dependencies, not an independently established theorem.
**Author's note on that revision (same day).** The gap was real: the original step D reaches one residue class
modulo eight, and the author's script `faru.py` had hidden this by pooling over four start positions. The author has
re-checked the replacement Parts D–E of §8.5 by hand and by two new scripts by the same author (`faru3.py`; far-field mode
`text` of `build3.py`, which executes Parts A–E literally inside complete folds); see the note at the end of §8.5 and
Appendix A. This settles Lemma F(D) only. It adds no verification of the Bulk Lemma or of Lemma N, which remain
computer-assisted and checked only by the author's own programs.

**Second audit, 14 November 2026.** An independent audit produced three further witnesses; all three are
confirmed and repaired in this version. (1) Bulk Lemma: the potential Ω with the fixed constants 10⁴, 10⁹ fails
for m ≥ 50 004; it is replaced by a lexicographic potential, and the comparisons and the ten vertex certificates
are proved to be independent of m (§8.3; proof by hand given the finite checks named there). (2) Lemma N: the
earlier base cases and induction did not cover the parameters of §6; the lemma is restated for an explicit
family 𝓕 of layouts that contains those of §6, the frame links are now explicit paths (Appendix C) instead of
the outcome of a search, and the proof is a reduction, by hand, to two test layouts of 𝓕 that are checked by
machine (§8.4). (3) Lemma T: the stated hypothesis was insufficient (counterexample m = 11); it is corrected, shown
to be unused, and the coverage statement actually used is proved (Lemma T′, Lemma E in §5.6).
What is proved by hand in these repairs: Lemma T, T′, E, K; parts (i)–(iv) of Claim 2; the reduction (1)–(5) of
Lemma N. What remains computer-assisted, with programs written by the author and run by nobody else: the finite
checks behind Claim 1 (m = 88, 89), Claim 2 (m ≤ 60; table (a); (S2)–(S4)), and the two test layouts of Lemma N.
What remains an assumption: that those programs implement the constructions as described in the text.

**Third audit, 14 November 2026** (six findings, all confirmed). Substantive: (1) the tether lengths in the word
did not match the rows stated in Lemma N (for K = B = 1: 273 P's prescribed, 279 needed) — the tethers are now
explicit routes with proved lengths σ_e(k) = 10k+2, σ_x(k) = 14K+22−6k, in text and code; (2) the radius of a PPP
around its owner is 3, not 2 — owners are now defined, the cutoffs are 20/13/6 and the coverage argument of
Lemma N is redone; (3) the test layouts had been built with chained bulk paths, not the assembly of §6 — they
are now built unchained; (4) the bulk table does not have "74 entries for every m" — it has 39 for each parity
of m; **the proof that table (a) covers every m was incomplete** (now Proposition A in §8.3). Minor: (5) the
sizes 61–87 missing in Claim 1 are now checked; (6) an intermediate bound in Corollary 4 was false and is replaced.
**After the third audit (same day):** the coverage of table (a) for all m is now proved as Proposition A in §8.3
(per-end translations between sizes of equal parity; reference sizes 59, 60 and 79, 80). With it every step of the
manuscript has a written proof or a named finite computation. **What this does not mean:** Proposition A, the
rewritten Lemma N and the explicit tethers were written today and have been read by nobody else; three audits
found errors in parts previously presented as finished, so further errors are likely rather than excluded.
**Fourth audit, 14 November 2026** (five items; all reproduced; ledger in Appendix D). Failed statements, now
replaced: the owner-distance claim and the pair enumeration on e3 in Lemma N (replaced by a table of all 50
type/offset combinations, valid for all items and cuts); "all owners are zigzag sites or vertices" (bulk caps are
now treated separately, (1′)); the bound |Y| ≥ 12 in Proposition A (A5) (not needed). Convention: §6 now states the
one word that the builder writes (order of units, final P, L*); a packing-free generator reproduces the words of
all packings byte for byte in run-length encoding.
**Still not possible:** to build a complete fold of an actual reduction instance with the available programs
(m ≥ 336 means more than 5·10⁷ H's); at those sizes there are only local coordinate checks, and the direct validation
of the bulk cover stops at m = 100.

## 2. Setting

Lattice **D**: sites (x,y,z) ∈ Z³, x≡y≡z (mod 2), x+y+z ≡ 0 (sublattice A) or 3 (sublattice B) mod 4.
Bond vectors t1=(1,1,1), t2=(1,−1,−1), t3=(−1,1,−1), t4=(−1,−1,1); A-site v ~ v+t_k, B-site v ~ v−t_k.
4-regular, bipartite, girth 6; two sites have at most one common neighbour.
Distance between two A-sites differing by Σ n_k t_k (Σ n_k = 0) is Σ|n_k|; the geodesic along a ⟨110⟩ direction
t_a − t_b is unique (the straight zigzag).

Fold of s ∈ {H,P}^N: injective, consecutive letters adjacent. S = H-sites, h = |S|, e(S) = bonds inside S
(B–L convention: chain bonds included), ∂S = bonds leaving S; 4h = 2e(S) + |∂S|.

## 3. Outline

1. *Upper bound* (§4). A set S of sites with boundary |∂S| has |S| ≤ (4/3)(|∂S|/4)^{3/2}. So N_m = m(4m²−1)/3 H's make
 at most 2N_m − 2m² contacts.
2. *Uniqueness* (§5). Equality holds only when the H's form the octahedron Oct(m) (Theorem 5). This replaces
 Berger–Leighton's cube.
3. *The word* (§6). From an instance of bin packing we build a word with N_m H's: a rigid frame on two edges of
 one small face of the octahedron, with slots; chains of "dimers" HH that can only lie on edges; separators hung
 on two tethers each; items; fillers; long runs for the interior.
4. *Only if* (§7). In a fold with 2N_m − 2m² contacts the frame is rigid, the dimers are a perfect matching of the
 remaining edge sites, the tethers pin the separators on the third edge at prescribed places, and the items
 between consecutive separators are a packing.
5. *If* (§8). Given a packing, all H's are placed on Oct(m), and the P's are routed outside: near the surface by
 explicit local rules, far away by a product-like scheme. Then the fold has exactly 2N_m − 2m² contacts (5.1).

## 4. Theorem 3 (sharp edge-isoperimetric inequality on D)

**For every finite S ⊂ D: |S| ≤ (4/3)·(|∂S|/4)^{3/2}**, i.e. e(S) ≤ 2|S| − 2(3|S|/4)^{2/3}.

Proof. Layers L_k = {x = k}; every bond joins consecutive layers; gap g_k = bonds between L_k and L_{k+1}.
For k even these are the t1,t2 bonds and split into disjoint zigzag chains in direction (0,1,1); for k odd the
t3,t4 bonds, chains in direction (0,1,−1). A chain alternates between its two layers. A site of L_k lies on one
chain of g_k and one of g_{k−1} and is determined by that pair.
Let s_k = |S∩L_k| and β_k = number of maximal runs of consecutive S-sites on the chains of g_k.
Each run has exactly two boundary bonds: |∂S| = 2Σβ_k =: 2C.
 (a) |s_k − s_{k+1}| ≤ β_k (a run alternates layers).
 (b) s_k ≤ β_{k−1}β_k (S∩L_k injects into {chains hit in g_{k−1}} × {chains hit in g_k}).
With x_k = Σ_{j<k} β_j, (a) telescopes to s_k ≤ min(x_k, C−x_k). Let f(x) = sqrt(min(x, C−x)) (concave, f(0)=f(C)=0).
Then s_k ≤ sqrt(min(x_k,C−x_k)·β_{k−1}β_k) ≤ f(x_k)(β_{k−1}+β_k)/2, and
Σ_k s_k ≤ Σ_k β_k (f(x_k)+f(x_{k+1}))/2 ≤ ∫_0^C f = (4/3)(C/2)^{3/2}. ∎

**Corollary 4.** N_m := m(4m²−1)/3 = 1, 10, 35, 84, … If |S| = N_m then |∂S| ≥ 4m², i.e. e(S) ≤ 2N_m − 2m².
(If C ≤ 2m²−1: |S| ≤ (4/3)(m²−½)^{3/2} ≤ (4/3)m(m²−½) = (4/3)m³ − (2/3)m < (4/3)m³ − m/3 = N_m, for every m ≥ 1.
[Corrected 14 November 2026: the earlier intermediate bound (4/3)m³ − m + 1/(8m) was false, by a term of order m⁻³.])
[CHECKED] Theorem 3 on 1500 random connected clusters (largest ratio |S|/bound = 0.82).

## 5. The octahedron and its uniqueness

### 5.1 Definition of Oct(m) and its numbers

Put c = (0, 2m−2, 0) and, for the 8 sign vectors s = (±1,±1,±1), bound(s) = 2m−2 if s_x s_y s_z = +1 ("big face")
and 2m−1 otherwise ("small face").
**Oct(m) := { v ∈ D : s·(v − c) ≤ bound(s) for all 8 sign vectors s }.**
With Y = y − (2m−2), p = (Y+z)/2, q = (Y−z)/2 the 8 inequalities read
 |Y+z| ≤ min(2m−2−x, 2m−1+x), |Y−z| ≤ min(2m−2+x, 2m−1−x).
The map (x,Y,z) → (−x,Y,−z) is a lattice symmetry (it exchanges t1↔t3, t2↔t4) and preserves Oct(m), so it is enough
to look at layers x = k ≥ 0. There the conditions are |p| ≤ (2m−2−k)/2 and |q| ≤ (2m−1−k)/2. The lattice condition
(x+y+z ≡ 0 mod 4 for even k, ≡ 3 mod 4 for odd k) says: p, q are integers, with p ≡ q ≡ m−1−k/2 (mod 2) for even k,
and p ≡ m−(k+3)/2, q ≡ p+1 (mod 2) for odd k. Put
 a_k = b_k = m−1−k/2 (k even), a_k = m−(k+3)/2, b_k = m−(k+1)/2 (k odd).
Then **layer k of Oct(m) = { |p| ≤ a_k, p ≡ a_k (2) } × { |q| ≤ b_k, q ≡ b_k (2) }**, a rectangle of (a_k+1)(b_k+1)
sites: (m−k/2)² for even k, (m−(k+1)/2)(m−(k−1)/2) for odd k; i.e. m², m(m−1), (m−1)², (m−1)(m−2), …, 2, 1.
* |Oct(m)| = m² + 2Σ_{j=1}^{m−1}(j² + j(j+1)) = m(4m²−1)/3 = N_m.
* A site of layer k+1 ≥ 1 has two neighbours in layer k: (p±1, q) if k+1 is odd, (p, q±1) if k+1 is even. Since
 a_{k+1} = a_k − 1, b_{k+1} = b_k (k+1 odd) and a_{k+1} = a_k, b_{k+1} = b_k − 1 (k+1 even), both are in Oct(m).
 Every bond joins consecutive layers, so e(Oct(m)) = 2(N_m − m²) and |∂Oct(m)| = 4N_m − 2e = **4m²**: Oct(m) attains
 Corollary 4.
* The six sites with two outside neighbours ("vertices") are (0,0,0), (0,4m−4,0), (±(2m−2),2m−2,0),
 (0,2m−2,±(2m−2)). In absolute coordinates the four faces with s_y = −1 do not depend on m.
[CHECKED m = 4 … 14, halfspace.py: this set coincides with the octahedron used in all scripts. m = 2 is adamantane
C10H16, m = 3 is C35H36.]
8 triangular {111} faces: four big (T_m = m(m+1)/2 dangling bonds, majority sublattice, corners = vertices) and four
small (T_{m−1}, minority sublattice). 12 edges; each edge is a zigzag of bonded surface sites alternating between
its big and its small face.

### 5.2 The one-dimensional relaxation

From §4: with β_k the number of runs in gap k and C = Σβ_k = |∂S|/2, s_k ≤ min(x_k, C−x_k, β_{k−1}β_k), x_k = Σ_{j<k}β_j.
If β_k = 0 then layers k and k+1 are empty. So, deleting the zero gaps: there is a *composition* β = (β_1,…,β_n) of C
(positive integers with sum C) with breakpoints x_i = β_1+…+β_i such that
 |S| ≤ V(β) := Σ_{i=1}^{n−1} min(x_i, C − x_i, β_iβ_{i+1}),
with equality only if no gap inside is zero and every layer bound is tight.
**Claim U.** For C = 2m²: V(β) ≤ N_m, with equality only for β = (1,1,2,2,…,m−1,m−1,m,m,m−1,m−1,…,2,2,1,1).

### 5.3 The one-sided problem

For a composition β of x put U(β) := Σ_{i=1}^{n−1} min(x_i, β_iβ_{i+1}). Let F(x) := Σ_{0≤y<x} ⌊√y⌋ and
W(u,v) := F(v) − F(u). Call β *optimal* if U(β) = F(x).

**Lemma 5.1 (⋆).** Let a ≥ 1, s = ⌊√a⌋, a = s² + r (0 ≤ r ≤ 2s), s+1 ≤ t ≤ a, ℓ ≥ 1. Then
 (a − t) + min(a, ℓt) ≤ W(a−t, a) + W(a, a+ℓ).
If equality holds then r ≥ s and ℓ ≤ s.
Proof. (i) For y ≥ a, ⌊√y⌋ ≥ s, and ⌊√y⌋ ≥ s+1 once y ≥ (s+1)² = a + u, u := 2s+1−r ≥ 1. So
W(a,a+ℓ) ≥ sℓ + e(ℓ), e(ℓ) := max(0, ℓ−u). Note 0 ≤ e(ℓ+1) − e(ℓ) ≤ 1.
(ii) Put φ(ℓ) := min(a,ℓt) − sℓ − e(ℓ) and L(t) := W(a−t,a). It suffices to show L(t) ≥ (a−t) + max_ℓ φ(ℓ).
Let ℓ_0 = ⌊a/t⌋ and q = a − ℓ_0t; then 1 ≤ ℓ_0 ≤ s (as a < (s+1)² ≤ (s+1)t) and 0 ≤ q < t. For ℓ < ℓ_0:
φ(ℓ+1) − φ(ℓ) = (t−s) − (e(ℓ+1)−e(ℓ)) ≥ 0. For ℓ ≥ ℓ_0+1: φ(ℓ) = a − sℓ − e(ℓ) is strictly decreasing. Hence
 max φ = max(φ(ℓ_0), φ(ℓ_0+1)) = a − sℓ_0 − μ, μ := min(q + e(ℓ_0), s + e(ℓ_0+1)),
and we have to show **L(t) ≥ Req(t) := 2a − t − sℓ_0 − μ** (ℓ_0, q, μ depend on t).
(iii) Base t = s+1. L(s+1) = Σ_{y=a−s−1}^{a−1}⌊√y⌋ equals s²+r−1 if r ≤ s (s+1−r terms equal to s−1, r terms equal
to s) and s²+s if r ≥ s+1.
 – r ≤ s−1: a = (s+1)(s−1) + (r+1), so ℓ_0 = s−1, q = r+1; u ≥ s+2 so e(ℓ_0) = e(ℓ_0+1) = 0, μ = r+1,
 Req = s²+r−2 < L.
 – r = s: ℓ_0 = s, q = 0, μ = 0, Req = s²+s−1 = L.
 – r = s+j, 1 ≤ j ≤ s: ℓ_0 = s, q = j, e(s) = j−1, e(s+1) = j, μ = min(2j−1, s+j) = 2j−1, Req = s²+s = L.
 So L(s+1) ≥ Req(s+1), with equality iff r ≥ s.
(iv) Step t → t+1 (s+1 ≤ t < a): Req(t+1) − Req(t) ≤ ℓ_0 − 1 ≤ ⌊√(a−t−1)⌋ = L(t+1) − L(t). Write ℓ_0', q', μ' for t+1.
 Since t(t+1) > a we have a/(t+1) > a/t − 1, so ℓ_0' ∈ {ℓ_0, ℓ_0−1}.
 – ℓ_0' = ℓ_0: q' = q − ℓ_0, so μ' ≥ μ − ℓ_0 and Req(t+1) − Req(t) = −1 − (μ'−μ) ≤ ℓ_0 − 1.
 – ℓ_0' = ℓ_0−1: then q < ℓ_0 and q' = q + t − ℓ_0 + 1; μ ≤ q + e(ℓ_0);
 (q' + e(ℓ_0−1)) − μ ≥ t − ℓ_0 ≥ s+1−ℓ_0 and (s + e(ℓ_0)) − μ ≥ s − q ≥ s+1−ℓ_0; so μ' − μ ≥ s+1−ℓ_0 and
 Req(t+1) − Req(t) = −1 + s − (μ'−μ) ≤ ℓ_0 − 2.
 – ⌊√(a−t−1)⌋ ≥ ℓ_0 − 1: clear for ℓ_0 = 1. For j := ℓ_0 ≥ 2: t ≤ a/j and a ≥ jt ≥ j(j+1), so
 a − t − 1 ≥ a(j−1)/j − 1 ≥ (j+1)(j−1) − 1 ≥ (j−1)².
 By induction L(t) ≥ Req(t) for all t, and L(t) − Req(t) is non-decreasing in t.
(v) Equality. Equality in (⋆) forces L(t) = Req(t), hence L(s+1) = Req(s+1), hence r ≥ s by (iii). It also forces
φ(ℓ) = max φ, so ℓ ≤ ℓ_0+1 ≤ s+1, and ℓ = s+1 only if ℓ_0 = s and φ(s+1) ≥ φ(s). ℓ_0 = s means st ≤ a, i.e. t = s+1
(then q = r−s) or t = s+2, r = 2s (then q = 0). In both cases s + e(s+1) > q + e(s) (equality would need q = s and
e(s+1) = e(s), but q = s gives r = 2s, u = 1, e(s+1) = e(s)+1). So φ(s+1) < φ(s) and ℓ ≤ s. ∎
[CHECKED a < 260, all t, ℓ: (⋆) holds; equality occurs 696 times, always with r ≥ s and ℓ ≤ s; for s ≥ 2 exactly when
t = s+1, r ≥ s, min(2s+1−r, s) ≤ ℓ ≤ s — tight2.py. The route (iii),(iv) itself: star_route.py, a < 3000.]

**Lemma 5.2 (one-sided optimum).** U(β) ≤ F(x) for every composition β of x, and F(x) is attained.
Proof. Induction on x. If β = (x) then U = 0. Otherwise let ℓ be the last part, a = x − ℓ ≥ 1 the last breakpoint,
ℓ' the part before it, β⁻ = β without ℓ (a composition of a), s = ⌊√a⌋.
*Case I: ℓ' ≤ s.* U(β) = U(β⁻) + min(a, ℓ'ℓ) ≤ F(a) + sℓ ≤ F(a) + W(a,a+ℓ) = F(x).
*Case II: ℓ' ≥ s+1.* Let a' = a − ℓ' ≥ 0 and β'' = β without its last two parts. If a' ≥ 1,
U(β) = U(β'') + (term at a') + min(a,ℓ'ℓ) ≤ F(a') + a' + min(a,ℓ'ℓ) ≤ F(a') + W(a',a) + W(a,x) = F(x) by (⋆) with
t = ℓ'. If a' = 0 the same with U(β'') and the term at a' replaced by 0.
Attained: the *canonical* composition 1,1,2,2,3,3,… has breakpoints k² (between parts k, k) and k²+k (between k,
k+1) and every term equals its breakpoint; cut off at x = s²+r it gives last part r (1 ≤ r ≤ s; term at s² is
sr = W(s²,x)), r−s (s < r ≤ 2s; term at s²+s is s(r−s) = W(s²+s,x)), or s (r = 0). ∎

**Lemma 5.3 (equality cases).** Let β be an optimal composition of x ≥ 2, with ℓ, ℓ', a, s as above. Then either
 (Type I) ℓ' = s, sℓ ≤ a, a + ℓ ≤ (s+1)², and β⁻ is an optimal composition of a; or
 (Type II) ℓ' ≥ s+1, a ≥ s²+s and ℓ ≤ s.
Proof. Equality in Case I needs U(β⁻) = F(a), min(a,ℓ'ℓ) = ℓ'ℓ = sℓ and W(a,a+ℓ) = sℓ. Equality in Case II needs
equality in (⋆); apply Lemma 5.1. ∎

**Lemma 5.4.** Let m ≥ 1.
 (F2) For 1 ≤ v ≤ m−1 no optimal composition of m²+v has last part ≥ m.
 (F3) Every optimal composition of m² has last part ≤ m.
 (F4) The only optimal composition of m² with last part m is the canonical one, c_m = (1,1,2,2,…,m−1,m−1,m).
Proof. Let β be optimal for x = m²+v, 0 ≤ v ≤ m−1, with last part ℓ ≥ m (m ≥ 2; m = 1 is trivial). Then a = x−ℓ <
m², so s ≤ m−1 < ℓ: Type II is impossible. So β is of Type I: m²+v = a+ℓ ≤ (s+1)² ≤ m² gives v = 0 and s = m−1
[F2]; then (m−1)ℓ ≤ a = m²−ℓ gives ℓ ≤ m [F3]. If ℓ = m then a = m²−m, ℓ' = m−1 and β⁻ is an optimal composition of
(m−1)² + (m−1) with last part m−1. For such a composition (write n = m−1): its last breakpoint is n², ⌊√n²⌋ = n;
Type II would need n² ≥ n²+n; so it is of Type I, its part before the last is n and its β⁻ is an optimal composition
of n² with last part n. By induction that is c_n, so β = c_n + (n, m) = c_m [F4]. ∎
[CHECKED x ≤ 110 by exhaustive DP with counting, lastparts.py: F2, F3 hold and the optimal composition of s² with
last part s, and of s²+s with last part s, is unique. Optimal compositions are not unique in general, e.g. both
(1,1,2,2,2) and (1,1,1,3,2) are optimal for x = 8; the lemma only needs the cases above.]

### 5.4 Proof of Claim U

M := m², C = 2M, and N_m = M + 2F(M) (as F(M) = Σ_{k<m} k(2k+1) = m(m−1)(4m+1)/6). Let β be a composition of 2M.
For a breakpoint x_i ≤ M the term of V is ≤ min(x_i, β_iβ_{i+1}); for x_i ≥ M use the mirror image.
*Case A: M is a breakpoint,* between parts ℓ (left) and r (right). Then V(β) ≤ U(β_left) + min(M, ℓr) +
U(mirror of β_right) ≤ F(M) + M + F(M) = N_m. Equality needs both halves optimal for M and ℓr ≥ m²; by (F3) ℓ, r ≤ m,
so ℓ = r = m, and by (F4) both halves are canonical: β is the octahedral composition.
*Case B: M lies inside a part of length b,* which covers [M−v', M+v], v, v' ≥ 1, v+v' = b. The terms at breakpoints
≤ M−v' are the terms of U for the composition (left parts, b) of M+v; likewise on the right for M+v'. So
V(β) ≤ U_L + U_R with U_L ≤ F(M+v), U_R ≤ F(M+v'), and also U_L ≤ F(M−v') + (M−v'), U_R ≤ F(M−v) + (M−v).
 – b ≤ m−1: V ≤ F(M+v) + F(M+v') = 2F(M) + mb < N_m (⌊√y⌋ = m for M ≤ y < M+m).
 – b = m: V ≤ 2F(M) + m² = N_m, and equality would need an optimal composition of M+v, 1 ≤ v ≤ m−1, with last part
 m: excluded by (F2). So V < N_m.
 – b ≥ m+1: G(y) := F(y) + y is non-decreasing and convex (G(y+1) − G(y) = ⌊√y⌋ + 1). V ≤ G(M−v') + G(M−v) with
 v, v' ≥ 1, v+v' ≥ m+1; the maximum is at {v,v'} = {1,m}: G(M−1) + G(M−m) = 2F(M) + 2M − (m−1) − m(m−1) − 1 − m
 = 2F(M) + m² − m < N_m. ∎
[CHECKED independently: exact DP for all m ≤ 14 (pdp.cpp): maximum N_m, exactly one optimal composition; and for
m = 2 exhaustive enumeration of all 381 250 connected 10-site clusters: max 12 bonds, exactly 2 maximisers up to
translation.]

### 5.5 Profile ⇒ shape

Let |S| = N_m and |∂S| = 4m². By 5.2 and Claim U the gaps are 1,1,2,2,…,m,m,…,2,2,1,1 and every layer bound is tight.
In a layer the chains of the two adjacent gaps are the rows and columns of a square grid (a step along a chain of
one gap moves to the next chain of the other gap).
(b) tight: s_k = β_{k−1}β_k. Since (#chains of g_k that S meets) ≤ (#runs) = β_k, equality gives: every chain that S
meets carries exactly one run and meets S∩L_k, and S∩L_k is the full product (rows met) × (columns met). A run
occupies consecutive sites of its chain, so the rows met are consecutive, likewise the columns: S∩L_k is a
β_{k−1} × β_k rectangle.
(a) tight: on the left half s_{j+1} − s_j = β_j, so every run of gap j begins and ends in L_{j+1}: on each chain of
g_j the sites of S∩L_j are exactly the positions strictly between the sites of S∩L_{j+1}. So S∩L_j is determined by
S∩L_{j+1}; symmetrically on the right half. Hence S is determined by its central m × m layer, i.e. by the position
and the parity (A- or B-layer) of that layer. Oct(m) has this structure (5.1), so **S is a translate of Oct(m) or of
its mirror image** (the image under a lattice symmetry exchanging the sublattices). ∎

**Theorem 5.** A set S ⊂ D of N_m sites has at most 2N_m − 2m² bonds, with equality iff S is a translate of
Oct(m) or of its mirror image. Consequently (analogue of B–L Theorem 3.2) a string with N_m H's has a fold with
2N_m − 2m² H–H bonds iff it has a fold whose H's form Oct(m) (up to mirror image).

### 5.6 Tetrahedral coordinates and the local facts (O1)–(O7)

**Coordinates.** f_j(v) := t_j·(v − c), j = 1…4. Then Σ_j f_j = 0, v − c = ¼Σ_j f_j t_j, and in the coordinates of 5.1
X = (f_1+f_2)/2, Y = (f_1+f_3)/2, z = (f_1+f_4)/2. The sites of D are exactly the integer vectors (f_j) with sum 0
and all f_j ≡ 2m−2 (mod 4) [A-sites] or all f_j ≡ 2m+1 (mod 4) [B-sites]. (A-sites are Σ n_j t_j with Σ n_j = 0, and
t_j·t_j = 3, t_i·t_j = −1.) A bond from an A-site, v → v + t_k, changes f_k by +3 and the other three by −1; a bond
from a B-site, v → v − t_k, changes f_k by −3 and the others by +1. The 8 inequalities of 5.1 are f_j ≤ 2m−2 (big
face j) and −f_j ≤ 2m−1 (small face j); with the congruences:
 **A-site ∈ Oct(m) ⟺ |f_j| ≤ 2m−2 for all j; B-site ∈ Oct(m) ⟺ −(2m−1) ≤ f_j ≤ 2m−3 for all j.**

**(O1) Dangling bonds.** For an A-site v ∈ Oct(m): v + t_k ∉ Oct(m) ⟺ f_k(v) = 2m−2 ("v lies on big face k").
For a B-site: v − t_k ∉ Oct(m) ⟺ f_k(v) = −(2m−1) ("v lies on small face k"). (The other coordinates change by 1
towards the inside of their range, which by the congruence cannot leave it.)
 * Two faces: if f_j = f_k = 2m−2 the other two coordinates sum to −(4m−4), so both are −(2m−2): the six vertices
 c ± (2m−2)e_i. A B-site cannot have f_j = f_k = −(2m−1) (the other two would sum to 4m−2 > 2(2m−3)). So the
 vertices have two dangling bonds and every other surface site exactly one.
 * A dangling site has exactly one neighbour in Oct(m): w = v + t_k has f_k(w) = 2m+1 and its other neighbours
 w − t_j have f_k = 2m+2; w = v − t_k has f_k(w) = −(2m+2) and its other neighbours have f_k = −(2m+3).
 * Two dangling sites are never adjacent: if w = v + t_k (v on big face k) were adjacent to w' = w − t_i, i ≠ k, with
 w' dangling over a small face j, then v' = w' + t_j ∈ Oct(m), j ≠ i, but f_k(v') = 2m−2+3+1+t_k·t_j ≥ 2m+1.
**Faces.** Big face k: the A-sites with f_k = 2m−2; g_j := (f_j + 2m−2)/4 (j ≠ k) are integers ≥ 0 with sum m−1 and
all such triples occur: a triangle of the triangular lattice with m sites on a side, T_m sites. Small face k: the
B-sites with f_k = −(2m−1); g_j := (2m−3−f_j)/4 ≥ 0 with sum m−2: a triangle with m−1 sites on a side. So Oct(m) has
4T_m + 4T_{m−1} = 4m² dangling bonds (again).
**(O3) Edges.** Let an A-site v on big face k be bonded to a surface B-site v' = v + t_i on small face j. Then
i ∉ {j,k}, j ≠ k, f_j(v) = −(2m−2), and f_k(v') = 2m−3. So bonded pairs of surface sites are exactly the consecutive
sites of the 12 *edge zigzags*
 E(k,j) := {A-sites with f_k = 2m−2, f_j = −(2m−2)} ∪ {B-sites with f_k = 2m−3, f_j = −(2m−1)} (k ≠ j),
on which, with {a,b} the other two indices, f_a = −(2m−2)+4n, f_b = 2m−2−4n (A-site of index 2n, n = 0…m−1; n = 0
and m−1 are vertices) and f_a = −2m+5+4n, f_b = 2m−3−4n (B-site of index 2n+1, n = 0…m−2). The edge has direction
u = t_a − t_b and π := (f_a − f_b)/4 increases by exactly 1 per zigzag step. Over all of Oct(m), π − π(c) ∈ [−(m−1), m−1];
the maximum is attained exactly on the edge E(a,b) and the minimum exactly on E(b,a), so the two ends of E(k,j) (one
on E(b,a), one on E(a,b)) differ by 2m−2 in π, the largest difference between two sites of Oct(m). Through each of
the two vertices of E(b,a) there is exactly one edge of direction u (E(k,j) and E(j,k)).
**(O2) P^3 links.** Let v, p_1, p_2, p_3, v' be a path with v, v' ∈ Oct(m) and p_i ∉ Oct(m). By bipartiteness v, v' are
on the same sublattice. If v is an A-site on big face k: p_1 = v + t_k, p_2 = p_1 − t_i (i ≠ k, f_k = 2m+2),
p_3 = p_2 + t_l (l ≠ i), v' = p_3 − t_n; f_k(v') ≤ 2m−2 forces l ≠ k and n = k. So v' = v + t_l − t_i with i, l ≠ k,
i ≠ l: v' is on the same big face and is one of the 6 nearest neighbours of v in its triangular lattice
("T-neighbour"). Conversely for T-neighbours this path is outside Oct(m). Same for B-sites and small faces.
**(O5)** follows from the triangle description: two boundary sites of a triangle on different sides, at distances
i, j ≥ 1 from the common corner, are T-neighbours iff i = j = 1; on the same side iff consecutive. (Big face:
boundary = a-sites, corners = vertices. Small face: boundary = b-sites, corners = the "corners" b_0.)

**(O4) Links, for every k ≤ 2m and every m.** Fix u = t_a − t_b and π = (f_a − f_b)/4. A bond is *advancing* (π
changes by +1) if it is +t_a from an A-site or −t_b from a B-site, *retreating* (−1) if it is +t_b or −t_a, and
*neutral* otherwise. Effect on (f_a, f_b): advancing +t_a: (+3,−1), −t_b: (+1,−3); neutral from A: (−1,−1), from B:
(+1,+1); retreating +t_b: (−1,+3), −t_a: (−3,+1). The *loss* of a path is #neutral + 2·#retreating; advance =
#bonds − loss. A link P^k from a surface site v to a surface site v' has k+1 bonds; its first and last bonds are
dangling bonds. Write n_i^± for the numbers of bonds ±t_i; then f_i(v') − f_i(v) = 4(n_i^+ − n_i^−) − (#A-bonds − #B-bonds).
 *Odd k: loss ≥ 2.* (v, v' on the same sublattice.) If the first bond is advancing, v is an A-site on big face a
 (or a B-site on small face b); then f_a(p_1) = 2m+1 must come down to ≤ 2m−2 (resp. f_b(p_1) = −(2m+2) must come
 up to ≥ −(2m−1)), and a change of 3 in that direction costs loss ≥ 2. Same for the last bond, read backwards.
 If neither is advancing the loss is ≥ 2 anyway.
 *Even k: loss ≥ 4.* By reversing the path (which exchanges u and −u) let v be an A-site on big face K, v' a
 B-site on small face j'; there are k/2+1 bonds from A-sites and k/2 from B-sites, f_i(v') − f_i(v) = 4(n_i^+ − n_i^−) − 1.
 – K = a: f_a must drop from 2m+1 (at p_1) to ≤ 2m−3: by ≥ 4. With loss ≤ 3 the only way is one −t_a and one
 neutral +t_c, everything else advancing; the last bond is then that +t_c (it cannot be +t_a: v' would have
 f_a = −(2m−1)), and counting gives f_c(v) = f_c(p_k) = −(2m+2): v ∉ Oct(m).
 – j' = a: f_a must drop from ≥ −(2m−2) to −(2m+2): the same pair of bonds, the first bond is the +t_c, and
 counting gives f_c(v') = f_c(v) + 3 = 2m+1.
 – neither: first and last bond are not advancing. Loss 2 (both neutral, +t_c first, +t_{c'} last, rest
 advancing) gives f_c(v') ≥ f_c(v) + 3. Loss 3 = one more neutral bond: if it is from an A-site, again
 f_c(v') ≥ f_c(v) + 3; if it is −t_{c''}, then f_c(v') ≤ 2m−3 forces c'' = c ≠ c', and then
 f_{c'}(v) = f_{c'}(v') − 3 = −(2m+2). All impossible.
 So **the advance of a link P^k is at most k−1 (k odd) and k−3 (k even).** (A run H^ℓ advances ≤ ℓ−1.)
 *Maximisers that start on the edge E(K,j) with direction u* ({a,b,K,j} = {1,2,3,4}) *end on E(K,j).*
 – k odd, v an A-site: v lies on big face K (and b, if v is the first vertex), not on a, so the first bond is
 not advancing; loss 2 then means first and last bond neutral, all others advancing (the other combinations
 cost ≥ 3 by the argument above). Then f_K(v') − f_K(v) = 4(1 − [K' = K]) forces the last bond to be −t_K, and
 f_j(v') = f_j(v): v' ∈ E(K,j). k odd, v a B-site: the same with the roles of K and j exchanged.
 – k even, v an A-site (not the vertex case): f_K(v') ≤ 2m−3 forces n_K^− ≥ n_K^+ ≥ 1; f_j(v') ≥ −(2m−1) forces
 n_j^+ ≥ n_j^−. If j' = j: the bonds +t_K, −t_K, +t_j and (because f_j(v') = f_j(v) − 1) a bond −t_j are the four
 neutral bonds, all others advance, and v' ∈ E(K,j). If j' ≠ j, f_{j'}(v) ≥ −(2m−2) forces n_{j'}^− ≥ n_{j'}^+ + 1 ≥ 2:
 for j' = K or a the loss is ≥ 5; for j' = b the loss is 4 but then v' would lie on the two small faces j and b.
 Vertex case (first bond +t_b, retreating): the same analysis; the only extra solution needs k = 2m+2.
 – k even, v a B-site, v' an A-site on big face K': f_j(v') ≥ f_j(v) + 1 forces a bond +t_j. If K' = K the four
 neutral bonds are −t_j, +t_j, +t_K, −t_K and v' ∈ E(K,j). K' = j is impossible by a congruence; K' = b needs k = 2;
 K' = a gives loss 4 with v' on big faces K and a: v' is the last vertex of E(K,j), still on the edge.
 Since π increases by 1 per zigzag step, a maximiser starting at index i ends at index i+k−1 resp. i+k−3: **the links
 P^3, P^6, P^10 skip exactly 1, 2, 6 zigzag sites.**
 [CHECKED independently by exhaustive search over all links between all pairs of surface sites: m = 8, 11
 (k ≤ 11) and m = 16 (k ≤ 10), adv.py.]

**(O7).** With a,b,c,d = 1,2,3,4: h = X, k = z (5.1 coordinates), V_a = c − (2m−2)e_z, V_b = c + (2m−2)e_y,
V_c = c + (2m−2)e_x; the small face F' is s = (1,1,−1) (index 4). e3 = E(2,4): sites (i, [i odd], −(2m−2)+i);
e1 = E(3,4): (i mod 2, i, −(2m−2)+i); e2 = E(1,4) from V_c: A-sites (2m−2−i, i, 0), B-sites (2m−2−i, i, −1); the
corner at V_a is (1,1,−(2m−3)), so h_0 = 1, k_0 = −(2m−3) and the stated formulas hold. Last claim: a zigzag site
with X ≥ 3 and z ≤ −3, i.e. f_1+f_2 ≥ 6 and f_1+f_4 ≤ −6. Going through the 12 pairs (k,j) with the values of E(k,j)
above: {k,j} = {1,2}, {3,4}, {1,4}, {2,3} give f_1+f_2 ∈ {0,±2} or f_1+f_4 ∈ {0,±2}; (1,3), (3,1), (4,2) would need a
coordinate outside its range; only E(2,4) = e3 remains, and there X ≥ 3, z ≤ −3 means index 3 … 2m−5. ∎

**Lemma T (transfer between sizes) — corrected 14 November 2026.** [Erratum. The earlier version assumed only
4m ≥ 3R + 2R' + 24. That is not sufficient. Counterexample (independent audit, reproduced by transfer_cov.py): m = 11,
R = 0, R' = 10, v = (0,30,10) ∈ Oct(11); only the x-axis is eligible, τ(v) = (−2,28,10), and the depth below the small
face (−,+,+) drops from 1 to −3. The error was in the last two lines of the proof.]
Depths: d_j := 2m−2−f_j (below big face j), d'_j := 2m−1+f_j (below small face j); Oct(m) = {all d_j, d'_j ≥ 0}; r bonds
change each depth by at most 2r+1.
*Claim.* Let R ≥ 0, R' ≥ 1 and **m ≥ R + R' + 5**. For v ∈ D with all depths ≥ −R, choose among the axes {x} ∪ {y if |Y| ≥ R'+2}
∪ {z if |Z| ≥ R'+2} the one with the largest |coordinate| of v − c, and let e be the unit vector on that axis
pointing from c towards v (any sign if the coordinate is 0). Then τ(w) := w − 2e − (0,2,0) is a lattice translation,
and relative to Oct(m−1) the site τ(v) has the same depths as v relative to Oct(m), except that four depths, each
≥ R + 5, have decreased by 4; Y and Z (relative to the new centre) are unchanged, or keep their sign and stay ≥ R'
in absolute value.
Proof. The shift by −2e relative to the centre changes each f_j by −2 (for the two j with t_j·e = 1) or +2. In the
first case d_j is unchanged and d'_j drops by 4; in the second d'_j is unchanged and d_j drops by 4. The four depths
that drop belong to the faces s with s·e = −1, and for those
depth = bound(s) − s·(v−c) ≥ 2m−2 + |c_e| − |c'| − |c''| (c_e the coordinate on the chosen axis, c', c'' the other two).
The sum |c_e| + |c'| + |c''| is at most 2m−1+R. An eligible axis other than the chosen one has |coordinate| ≤ |c_e|; a
non-eligible one has |Y| ≤ R'+1 resp. |Z| ≤ R'+1, i.e. |coordinate| ≤ R'+1 resp. R'+2. (i) Both other axes eligible:
|c'|+|c''|−|c_e| ≤ min(|c'|,|c''|) ≤ (2m−1+R)/3, so depth ≥ (4m−5−R)/3 ≥ R+5 because m ≥ R+5. (ii) Exactly one:
|c'|+|c''|−|c_e| ≤ R'+2, depth ≥ 2m−4−R' ≥ R+5. (iii) None: |c'|+|c''| ≤ 2R'+3, depth ≥ 2m−5−2R' ≥ R+5 because 2m ≥ 2R+2R'+10. ∎
*Use.* None. No statement of this paper depends on Lemma T; the earlier remark that the Bulk Lemma uses it was
inaccurate. What §8 uses are the region transfers below with Lemma T′, and Lemma E; their hypotheses are checked at
each application (Claim 1 of §8.3: Lemma T′ with D = 26, R = 0, m_0 = 88; Claim 2 of §8.3: Lemma E(a) with D = 48 and
Lemma E(b), Lemma K; Lemma N: Lemma E(a) with D = 60, Lemma E(b) with D = 4, 12, 20; all with m ≥ 80).

**Region transfers (the form used in §8) [CHECKED D = 3, m = 17, 18, regiontransfer.py].** Put Oct(m+2)° :=
Oct(m+2) − (0,4,0), the octahedron of size m+2 with the same centre c, so that Oct(m) ⊂ Oct(m+2)° and Y, Z, ρ, α mean
the same for both. Fix a radius D; "far" means depth > 3D. Let v ∈ Oct(m).
 (T-x) If all four faces with s_x = −σ are far from v: the D-ball of v + 4σe_x in Oct(m+2)° is the translate of the
 D-ball of v in Oct(m) (which sites belong to the octahedron, to which faces, edges, vertices); Y and Z are
 unchanged, X increases by 4σ.
 (T-y) If the faces with s_y = −σ are far and σY > D+1: the same with 4σe_y; X, Z unchanged, the sign of Y is kept.
 (T-z) If the faces with s_z = −σ are far and σZ > D+1: the same with 4σe_z.
 (T-r) If |Y|, |Z| > D+1 and all faces except the two of the quadrant of v (big k, small i(k)) are far: the same
 with the arm vector u = t_k − t_{i(k)} = (0, 2 sgn Y, 2 sgn Z); X and α are unchanged, ρ increases by 4.
 Proof: the bounds of Oct(m+2)° exceed those of Oct(m) by 4; s·(4σe_x) = 4 when s_x = σ, and t_k·u = (−t_i)·u = 4;
 faces that are far stay far. The foliation of 8.3 depends only on the signs of Y and Z (and on which sites
 have Y = 0 or Z = 0), which each transfer keeps inside the ball. ∎
 **Lemma T′ (coverage of the transfers)** [added 14 November 2026; it replaces an unproved sentence]. Notation
 for Oct(M)°, M = m+2, centre c: for a lattice site p write (a, b, c′) := p − c, Y = b, Z = c′ − 1, A = |a|, B = |b|,
 C = |c′|; the depth of p below the face s is b_s − s·(p − c) with b_s = 2M−2 or 2M−1. Fix D ≥ 1, R ≥ 0, put F := 4D + 12
 and assume **4M ≥ 12D + 46 + R**. Then for every lattice site p all of whose depths are ≥ −R at least one of
 (x), (y), (z), (r) holds; and whenever one of them holds, its translation τ has this property: for every site w
 within D bonds of p, the depths of w − τ relative to Oct(m) equal the depths of w relative to Oct(M)° for the
 faces not required to be far, both are ≥ 2D + 3 for the faces required to be far, and Y, Z have the same signs
 (zero included) at w and at w − τ.
 (x) the four faces with s_x = −sgn a have depth ≥ F; τ = 4 sgn(a) e_x (either sign if a = 0);
 (y) |Y| ≥ D+5 and the four faces with s_y = −sgn Y have depth ≥ F; τ = 4 sgn(Y) e_y;
 (z) |Z| ≥ D+5 and the four faces with s_z = −sgn Z have depth ≥ F; τ = 4 sgn(Z) e_z;
 (r) |Y|, |Z| ≥ D+3 and the six faces with (s_y, s_z) ≠ (sgn Y, sgn Z) have depth ≥ F; τ = (0, 2 sgn Y, 2 sgn Z).
 Proof. *Transfer.* The depth of w − τ below s relative to Oct(m) is (b_s − 4) − s·(w − τ − c) = depth(w) − 4 + s·τ.
 In (x), s·τ = 4 if s_x = sgn a (depth unchanged) and −4 otherwise (depth − 8); (y), (z) alike; in (r), s·τ = 4, 0, −4
 according to the number of signs of (s_y, s_z) that agree. D bonds change a depth by at most 2D + 1, so a face of
 depth ≥ F at p has depth ≥ 2D + 11 at w, and ≥ 2D + 3 after subtracting 8. Signs: (x) does not change Y, Z; in (y),
 |Y(w)| ≥ 5 and Y changes by 4 towards 0; in (r), |Y(w)|, |Z(w)| ≥ 3 and both change by 2 towards 0; (z) alike.
 *Coverage.* A + B + C = max_s s·(p − c) ≤ 2M − 1 + R. The faces with s_x = −sgn a have depth ≥ 2M−2+A−B−C. If (x) fails,
 (1) B + C − A ≥ 2M − 1 − F. Case B ≤ D+4: by (1), C ≥ 2M−5−F−D ≥ D+6, so |Z| ≥ D+5 and sgn Z = sgn c′; the faces opposite
 in z have depth ≥ 2M−2+C−A−B ≥ 4M−3−F−2B ≥ F: (z) holds. Case |Z| ≤ D+4 (then C ≤ D+5): alike B ≥ 2M−6−F−D ≥ D+5 and the
 faces opposite in y have depth ≥ 4M−3−F−2C ≥ F: (y) holds. Otherwise B ≥ D+5 and |Z| ≥ D+5, and the six faces of (r)
 have depth ≥ 2M−2−A−|B−C|. If (r) fails too, (2) A + |B − C| ≥ 2M−1−F. For B ≥ C, adding (1) and (2) gives B ≥ 2M−1−F,
 so A + C ≤ R + F and the faces opposite in y have depth ≥ 2M−2+B−A−C ≥ 4M−3−2F−R ≥ F: (y) holds; for C > B the same
 with (z). The inequalities used, 2M ≥ F+2D+11, 4M ≥ 2F+2D+13, 4M ≥ 3F+R+3, follow from 4M ≥ 12D+46+R. ∎
 [CHECKED, transfer_cov.py: all sites with depths ≥ −R, both parities of the centre, (D,R,M) = (2,0,18), (2,5,20),
 (3,0,21), (3,7,23), (4,0,24): a hypothesis holds, and for every hypothesis that holds the transfer property was
 verified for all sites within D bonds.]
 *Consequence (the only form in which transfers are used).* Let 𝒫 be a property of a site that depends only on
 the depths (truncated at 2D+3) of the sites within D bonds, on the signs of Y, Z there and, if a vertex lies
 within D bonds, on the position relative to that vertex. If 𝒫 holds at all sites with depths ≥ −R for two
 consecutive sizes m_0, m_0+1 with 4(m_0+2) ≥ 12D+46+R, then it holds for all m ≥ m_0. (If a vertex lies within D bonds
 of p, its four faces have depth < F at p, so only the transfer along the axis of that vertex can apply, and it
 maps that vertex of Oct(m) to that of Oct(M)°.) The transfers (T-x), …, (T-r) above are (x), …, (r) read from Oct(m)
 to Oct(m+2)°.

 **Lemma E (vertex boxes and edge boxes)** [added 14 November 2026; elementary, no induction]. Box(v, D) := {w ∈ D :
 |w − v|_∞ ≤ D}. It contains all sites within D bonds of v (a bond changes every coordinate by ±1), and
 s·(w − v) ≤ 3D for w ∈ Box(v, D).
 (a) Let V = c + (2m−2)σe_i be a vertex and m ≥ D + 2. Then Box(V,D) ∩ Oct(m) = {w : s·(w − V) ≤ b_s − (2m−2) for the four
 faces s with s_i = σ}, where b_s − (2m−2) ∈ {0, 1} does not depend on m, and the signs of Y and Z on Box(V,D) are
 functions of w − V. So for m, m′ ≥ D + 2 the translation V ↦ V′ maps Box(V,D) ∩ Oct(m), the zigzags in it and the signs
 (and zeros) of Y, Z onto the same data for Oct(m′).
 Proof. For s_i = −σ: s·(w − c) ≤ 3D − (2m−2) ≤ b_s. For s_i = σ: s·(w − c) = s·(w − V) + 2m−2. If V is on the x-axis, Y and Z
 are coordinates of w − V (up to the constant 1). If V is on the y-axis, Z is such a coordinate and
 |Y − σ(2m−2)| ≤ D < 2m−2; on the z-axis alike with D < 2m−3. All vertices are A-sites, so the zigzags leave V by the
 same bonds for every m. ∎
 (b) Let e[0] = V_1, …, e[2m−2] = V_2 be an edge zigzag, D ≥ 3 and 2D ≤ i ≤ 2m−2−2D. Then Box(e[i], D) meets only the two
 faces through the edge. If also 2D ≤ i′ ≤ 2m′−2−2D and i′ ≡ i (mod 2), the translation e[i] ↦ e′[i′] (the same edge of
 Oct(m′); m′ = m allowed) maps Box(e[i],D) ∩ Oct(m), the zigzag and the signs (and zeros) of Y, Z onto the same data
 for Oct(m′).
 Proof. e[i] = V_1 + ⌈i/2⌉u + ⌊i/2⌋u′ with two bond vectors u, u′, u + u′ = (V_2 − V_1)/(m−1). For a face through both
 vertices s·(u+u′) = 0, and its depth at e[i] is b_s − (2m−2) − s·(e[i] − V_1), a function of the parity of i. For a
 face through V_1 only, s·(u+u′) = −4 and s·u, s·u′ ∈ {−1, −3}, so its depth at e[i] is ≥ 2i − 1 > 3D; through V_2 only:
 ≥ 2(2m−2−i) − 1 > 3D; through neither: ≥ 4m − 7 > 3D. Signs: a multiple of u + u′ does not change the coordinate of the
 axis that carries neither V_1 nor V_2 (so Y is preserved exactly along Y-plane edges, Z along Z-plane edges), and
 on the box the other two of X, Y, Z differ from 0 by at least 2D − 2 − D > 0. ∎

## 6. The word

Input: K bins of capacity B, items s_1 … s_n with Σ s_i = K·B (bin packing in unary, strongly NP-complete).
 Σ* := 18K + 40 (an upper bound for the tether slacks below), λ := Σ* + 8, C := λB; item i becomes a chain of λ·s_i
 dimers. J := C + Σ* + 8; j_k := J + (k−1)(C+2) for k = 1 … K+1; R := C + Σ* + 9; m := j_{K+1} + R + 3.
 (J, C, all j_k are even, R is odd, m is even.)
"Dimer chain of q dimers" = (HH PPP)^{q−1} HH. **Canonical form of the word** [fixed 14 November 2026; this is exactly what
build3.py writes]: the units below, in this order; between two consecutive units one *long P-run* of exactly L_i P's,
where L* := 1000(m + w + 1) + 6, w := twice the number of long P-runs, and L_i := L* + 1 if the two H's next to the run lie
on the same sublattice in the placement of §8.4, L_i := L* otherwise (a run of L P's between two H's is a path with
L + 1 bonds, and L* is even; which case applies does not depend on the packing, §9); the word begins with the H of unit 1 and ends
with one more P after the last unit. (In §8 the first and the last P of a long P-run are called caps; the lengths
of Lemma F count them.)

1. H — the first monomer of the chain.
2. Three single H's, one after the other (each between two long P-runs: … P H P …).
3. Frame chain PHP · [e1] · PHP · [e2] · PHP: H-runs separated by links P^3, P^6, P^10 so that, laid along two
 edges, the links skip: on e1 (indices from V_a) {1,2}, the 2-slots {6k, 6k+1} (k = 1 … K+1) and {2m−3}; on e2
 (indices from V_c) {1}, the 6-slots {10k+6, …, 10k+11} (k = 0 … K) and {2m−3}. All frame runs have length ≥ 3.
 The link lengths add up to the maximal advance 2m−2 on each of the two parts.
4. For k = 1 … K+1 a separator group: HH · P^{2j_k+3+σ_e(k)} · HH PPP HH · P^{2(m−2−j_k)+3+σ_x(k)} · HH PPP HH PPP HH
 (entry anchor = 1 dimer, separator = 2 dimers, exit anchor = 3 dimers; the two long P-runs are the tethers).
 The slacks are **σ_e(k) := 10k + 2** and **σ_x(k) := 14K + 22 − 6k**: the tethers are the explicit routes of §8.4 (Lemma N,
 (N4)), whose P-sites are counted there. Both are even, at most 14K + 16 < Σ*, and depend only on k and K.
 [Corrected 14 November 2026: the earlier version quoted σ_e(1) = 6, σ_e(k) = 10k − 2, values measured by a search over a
 larger region than the routes of (N4); see the erratum there.]
5. Left filler: a dimer chain of J dimers.
6. Items: dimer chains of λ·s_i dimers, in the order i = 1 … n.
7. Right filler: a dimer chain of R dimers.
8. Three rings: dimer chains of 3(m−2) dimers each.
9. Bulk units: one run H^ℓ, ℓ ≥ 3, for each path of the cover of §8.3, in the order in which canon.py lists the paths.
[Convention fixed after the fourth audit: earlier versions listed the items before the fillers, did not mention
the final P, and used a second value 280m + 240w + 412 for the long runs in one test mode. These are changes of
convention, not of mathematics; §7 uses neither the order of these units nor the last monomer.]

The number of H's is N_m and the number of dimers is D = (m−1) + 4(K+1) + 9(m−2). Question: is there a fold with
2N_m − 2m² H–H bonds? (By Corollary 4 no fold has more.) Everything has size polynomial in K·B.

## 7. "Only if": a fold with 2N_m − 2m² contacts yields a packing

### 7.1 Notation on edges, and the facts used

Edge zigzag: V, b_0, a_1, b_1, …, a_{m−2}, b_{m−2}, V' (zigzag index 0 … 2m−2); a-sites are Maj and have their free
bond on the big face of the edge, b-sites are Min with the free bond on the small face. b_0 and b_{m−2} are "corners":
a corner belongs to the two edges of its small face that meet there; its three neighbours are the vertex and the two
a_1's. "Dangling site" = outside site adjacent to Oct(m).

* (O1) [5.6] Each surface site has one dangling site, the 6 vertices have two. A dangling site has exactly
 one neighbour in Oct(m); two dangling sites are never adjacent.
* (O2) [5.6] The surface sites of a face form a triangular lattice T; a link P^3 joins two surface sites
 iff they are T-neighbours on a common face.
* (O3) [5.6] Two surface sites are bonded only along the edge zigzags.
* (O4) Link table [5.6; also CHECKED m = 8, 11, 16, all pairs of surface sites, adv.py]. For an edge direction u, π = v·u/4. The
 largest π-advance of a link P^k between surface sites is k−1 for odd k and k−3 for even k (k = 3…11). If the link
 starts at zigzag index i of an edge with direction u and attains the maximum, it ends at index i+k−1 (k odd) or
 i+k−3 (k even) of the same edge. In particular P^3, P^6, P^10 skip exactly 1, 2, 6 zigzag sites.
* (O5) [5.6] T-neighbours among non-vertex zigzag sites: along one edge (a_i, a_{i+1}), (b_i, b_{i+1})
 (corners count as b_0); at a vertex of a big face the two a_1's; at a corner of a small face the two b_1's.
* (O6) A lattice path between sites differing by Σ n_k t_k with Σ n_k = 0 has at least Σ|n_k| bonds (each
 bond changes one coefficient by 1 in the representation with Σ n_k ∈ {0, ±1} given by the path). Paths of P's are
 lattice paths, so this bounds every tether from below.

* (O7) Two "height" functions [5.6; also CHECKED m = 6 … 20, coordfacts.py]. With e1 ∥ t_a − t_b and e3 ∥ t_a − t_c from V_a, put h(v) = v·(t_a+t_b)/2 and k(v) = v·(t_a+t_d)/2.
 Every bond changes h and k by exactly ±1. Along the track (zigzag index i from V_a) h = h_0 + i − 1 and
 k = k_0 + i − 1, where h_0, k_0 are the values at the corner at V_a. On e1: |h − h_0| ≤ 1 and k = k_0 + i − 1.
 On e2 (index i from V_c): h = h_0 + 2m − 3 − i and |k − (k_0 + 2m − 3)| ≤ 1. Every zigzag site of Oct(m) that is not
 one of the track sites a_1 … b_{m−3} of e3 has h ≤ h_0 + 1 or k ≥ k_0 + 2m − 5.

All of (O1)–(O7) are proved in 5.6.

### 7.2 The proof

Assume a fold with 2N_m − 2m² bonds.
1. *Shape.* The H's form Oct(m) (Claim U, §5). Every H–P chain bond uses a dangling site.
2. *Vertices.* An H between two P's needs two dangling sites, so the six PHP's occupy the six vertices.
3. *Frames.* Between two consecutive PHP's of the frame chain the total of the maximal advances (runs: length − 1;
 links: (O4)) is exactly 2m−2, the largest π-difference of two sites of Oct(m). Taking u with π_u(end) − π_u(start)
 = 2m−2 (such u exists for adjacent and for antipodal vertices) every piece must be advance-maximal, so by (O4) the
 part lies on the edge leaving its first vertex in direction u; hence the end vertex is adjacent and every frame
 monomer has a determined position. The link into V_b and the link out of V_b use the two dangling sites of V_b, which
 lie on different big faces, so e2 either shares a small face with e1 (intended) or is the edge "opposite" to e1.
 In the opposite case the entry slots and the exit slots are near antipodal vertices: by (O6) their dangling sites
 are ≥ 4m − 16K − 28 apart, but a separator group spans at most 2m + 10 + 2Σ* bonds. Since m > 8K + 19 + Σ* this is impossible
 (slot occupancy, step 6, does not depend on the geometry). So the geometry is the intended one, unique up to symmetry.
4. *The corner between e1 and e2.* Its three neighbours are V_b and the two frame run-ends next to it, whose chain
 neighbours are already fixed. So this H has no H chain-neighbour; not being a vertex it is not a PHP; hence it is
 the first monomer of the chain.
5. *Dimers form a perfect matching.* Let Z = non-vertex zigzag sites not covered in steps 3–4: the slots, the "track"
 (a_1 of e1, the corner at V_a, then a_1, b_1, …, a_{m−2} of e3 and the corner at V_c: an even path of 2m−2 sites) and
 three "rings" (the boundaries of the other small faces, even cycles of 6(m−2) sites). Each run HH has a P on both
 sides, so by (O3) it is a zigzag bond, and its sites are in Z. There are D dimers and |Z| = 2D, so the dimers are a
 perfect matching of Z. On the track the perfect matching is unique: D_0 = (a_1(e1), corner), D_i = (a_i, b_i).
6. *Anchors sit in slots.* A P^3 in the string joins two dimers (or frame pieces); by (O2), (O5) it joins
 T-neighbours in Z. No site of a slot has a T-neighbour in Z outside its slot. So the dimer in a 2-slot is a chain
 of one dimer; there are K+1 such chains (the entry anchors) and K+1 two-slots: a bijection. A 6-slot holds whole
 chains with 3 dimers in total; one-dimer chains are used up, items have ≥ 4 dimers, so it holds an exit anchor.
7. *Separators are pinned*. A separator is two matched dimers joined by a P^3 (its four sites are
 within 4 bonds of each other), with a tether of L_e = 2j_k+3+σ_e P's from an H in a 2-slot of e1 (zigzag index
 ≤ 6K+7) and a tether of L_x = 2(m−2−j_k)+3+σ_x P's to an H in a 6-slot of e2 (index ≤ 10K+11 from V_c);
 σ_e, σ_x ≤ Σ*. h and k change by 1 per bond, so for the first H w and the last H w' of the separator:
 h(w) ≤ h_0 + 2j_k + 5 + σ_e, k(w) ≤ k_0 + 2j_k + 6K + 10 + σ_e,
 h(w') ≥ h_0 + 2j_k − 10K − 14 − σ_x, k(w') ≥ k_0 + 2j_k − 4 − σ_x.
 Hence all four sites have h ≥ h_0 + 2j_k − 10K − 18 − Σ* > h_0 + 1 (as j_k ≥ J > 5K + 10 + Σ*/2) and
 k ≤ k_0 + 2j_k + 6K + 14 + Σ* < k_0 + 2m − 5 (as 2(m−2−j_k) ≥ 2(R+1) > 6K + 19 + Σ*). By (O7) they are track sites: the
 separator is D_i, D_{i+1}. Its first H has h ≥ h_0 + 2i − 1, so i ≤ j_k + 3 + σ_e/2; its last H has k ≤ k_0 + 2i + 2,
 so i ≥ j_k − 3 − σ_x/2. **So separator k sits on D_i, D_{i+1} with |i − j_k| ≤ 3 + Σ*/2.**
8. *Bins.* The windows of different separators are disjoint and ordered (spacing C + 2 ≥ Σ* + 10 > 2(3 + Σ*/2)).
 Between separators k and k+1 lie c_k = i_{k+1} − i_k − 2 track dimers, |c_k − C| ≤ 6 + Σ*. By (O5) a chain cannot pass
 a separator, so these dimers are a union of whole chains with at most C + 6 + Σ* dimers: not fillers (≥ C + Σ* + 8),
 not anchors (step 6), not separators (step 7); so they are items. Item sizes are multiples of λ = Σ* + 8 > 6 + Σ*,
 hence c_k = C = λB and the items between separators k and k+1 have total size B. This holds for all K bins, and
 Σ s_i = K·B: a packing. ∎
 (Claim U and the facts (O1)–(O7) are proved in §5. The proof uses of the P-runs only: the six PHP, the links of
 the frame, the PPP inside dimer chains, and upper bounds for the two tether lengths. So it does not matter how
 long the other linkers are.)

## 8. "If": a packing yields a fold with 2N_m − 2m² contacts

Throughout: the coordinates of 5.1 and 5.6, m even, m ≥ 80, the constants of §6. The H's will be placed on all of
Oct(m); by 5.1 the fold then has exactly 2N_m − 2m² contacts. What has to be shown is that the P's can be placed.

### 8.1 Foliation, lines, columns

Put Y := y − (2m−2), Z := z − 1. They have opposite parity, so no site has Y = Z = 0. Put ρ := |Y| + |Z| (odd) and
α := |Y| − |Z|. A site with YZ ≠ 0 lies in the *open quadrant* (σ, τ) = (sgn Y, sgn Z); a site with Y = 0 or Z = 0 is a
*bend site*. A bond is a *rung* if ρ differs at its ends and a *step* otherwise.

**Lemma B (bonds).** (a) Let YZ ≠ 0 at v. Of the four bonds at v one raises ρ by 2, one lowers ρ by 2 (rungs; α is
unchanged), one raises α by 2 and one lowers α by 2 (steps; ρ is unchanged). Both rungs change X by ε(v) and both
steps by −ε(v), where ε(v) := στ if v is an A-site and −στ if v is a B-site. A neighbour of v in the same open quadrant
has the opposite ε.
(b) Let v be a bend site, X(v) = x. Two neighbours have ρ(v) + 2 and two have ρ(v); in each pair one lies on either
side of the bend plane; the two neighbours with ρ(v) have X = x − 1 and X = x + 1.
Proof. (a) As |Y| ≥ 1, |Y + ΔY| = |Y| + σΔY, likewise for Z; and (σΔY, τΔZ) runs through (1,1), (−1,−1), (1,−1), (−1,1).
The bonds (ΔX; ΔY, ΔZ) of an A-site are (1;1,1), (1;−1,−1), (−1;1,−1), (−1;−1,1): ΔX = +1 exactly when ΔYΔZ = +1; for a
B-site the signs are reversed. A rung has ΔYΔZ = στ. (b) Z = 0 forces z = 1, a B-site; Y = 0 forces an A-site. For
Z = 0, Y > 0 the neighbours with equal ρ are those with ΔY = −1: (−1;−1,−1) and (1;−1,1). For Z = 0, Y < 0: ΔY = +1:
(−1;1,1) and (1;1,−1). For Y = 0, Z > 0: ΔZ = −1: (1;−1,−1) and (−1;1,−1). For Y = 0, Z < 0: ΔZ = +1: (1;1,1), (−1;−1,1). ∎

**Lemma L (lines).** The rungs form a graph in which every site has degree 2. Its components ("lines") are
two-way infinite paths. Each line contains exactly one bend site, where ρ is minimal; its two halves ("arms") lie
in two adjacent open quadrants; along an arm ρ increases by 2 per bond, α is constant and X alternates between two
consecutive integers. Every site lies on exactly one line.
Proof. A site with YZ ≠ 0 has one rung up and one down, a bend site two rungs up (Lemma B). Going down a rung lowers
|Y| and |Z| by one, so after finitely many bonds a bend site is reached; going up never ends. X alternates because
ε does. ∎
The *arm from v into a quadrant* is the path v = v_0, v_1, v_2, … with ρ(v_{i+1}) = ρ(v_i) + 2 inside that quadrant
(the quadrant matters only if v is a bend site).

**Quadrants of the faces.** Big face k lies in the closed quadrant (sgn (t_k)_y, sgn (t_k)_z): (+,+), (−,−), (+,−),
(−,+) for k = 1, 2, 3, 4; small face k in the opposite one. So big face k and small face i(k) share a quadrant,
i(1) = 2, i(2) = 1, i(3) = 4, i(4) = 3, and we write k(i) for the inverse.

**Lemma C (columns).** Let p be a dangling site, over big face k or over small face i, and (σ, τ) the quadrant
of that face.
(i) σY(p) ≥ 1 and τZ(p) ≥ 0. The *column* of p is the arm from p into the quadrant (σ, τ).
(ii) Along the column of p over big face k the coordinate f_k takes the values 2m+1, 2m+2, 2m+5, 2m+6, …; over small
face i the coordinate f_i takes the values −(2m+2), −(2m+3), −(2m+6), −(2m+7), …. Hence the column does not meet
Oct(m) and contains no dangling site other than p.
(iii) The columns of different dangling sites are disjoint.
Proof. (i) Let p = v + t_k, v an A-site with f_k(v) = 2m−2. As |f_j| ≤ 2m−2, the numbers Y = (f_1+f_3)/2 = −(f_2+f_4)/2 and
z = (f_1+f_4)/2 = −(f_2+f_3)/2 at v are 0 or have the sign of (t_k)_y, (t_k)_z; adding t_k gives σY(p) ≥ 1, τz(p) ≥ 1, hence
τZ(p) ≥ 0. Let p = v − t_i, v a B-site with f_i(v) = −(2m−1); the other f_j are ≤ 2m−3, so |Y(v)|, |z(v)| ≥ 1 with the
signs of −(t_i)_y, −(t_i)_z, and subtracting t_i moves both one further.
(ii) The rungs up in the quadrant (σ, τ) have (ΔY, ΔZ) = (σ, τ): from an A-site this is the bond +t_k, from a B-site
the bond −t_{i(k)}. Over big face k: f_k(p) = 2m+1, and the two bonds add 1 and 3 alternately. Over small face i: the
bonds are +t_{k(i)} and −t_i, which subtract 1 and 3 from f_i, starting from f_i(p) = −(2m+2). A site of Oct(m) has
−(2m−1) ≤ f_j ≤ 2m−2. A dangling site q ≠ p has f_k(q) ≤ 2m+1 and f_i(q) ≥ −(2m+2) (it is v' ± t_j with v' ∈ Oct(m)),
while the column beyond p has f_k ≥ 2m+2 resp. f_i ≤ −(2m+3).
(iii) If two columns meet they lie on one line and on the same arm, so one of the two starting points lies on the
column of the other, beyond its start; this contradicts (ii). ∎

### 8.2 Skins and rows over the face F'

**Skins.** For j ≥ 0 let O_j be the octahedron of size m + 2j with centre c: A-sites with |f_i| ≤ 2M−2 and B-sites
with −(2M−1) ≤ f_i ≤ 2M−3, M := m + 2j. *Skin j* := O_j ∖ O_{j−1} (j ≥ 1). It consists of the sites of O_j of depth 0 or
1 below some face, and D ∖ Oct(m) is the disjoint union of the skins. Skin 1 contains all dangling sites.

**F' := small face 4**, normal (1,1,−1), in the quadrant (+,−); its sides lie along the edges e1 := E(3,4),
e2 := E(1,4), e3 := E(2,4) (notation of 5.6). For j ≥ 0 and M = m + 2j the *F'-bilayer of skin j* consists of
 surface sites: B-sites with f_4 = −(2M−1), with coordinates (a, b, c) := ((2M−3−f_1)/4, (2M−3−f_2)/4, (2M−3−f_3)/4);
 sub-surface sites: A-sites with f_4 = −(2M−2), with coordinates γ := ((2M−2−f_1)/4, (2M−2−f_2)/4, (2M−2−f_3)/4), γ_i ≥ 1.
Here a, b, c ≥ 0 are integers with a + b + c = m − 2 + 2j: the distances of the surface site from the sides along
e2, e3, e1. For j = 0 these are the sites of F' itself. All these sites have Y ≥ 1 and Z ≤ −2.

**Lemma R (rows).** (a) The sub-surface site γ is bonded to the surface sites γ − e_1, γ − e_2, γ − e_3 (and to one site of
skin j−1).
(b) Let v be the site (a, b, c) of F'. The column of its dangling site meets skin j in exactly two sites: the
sub-surface site (a+j, b+j, c+1) and the surface site (a+j, b+j, c). No column of a dangling site over another face
meets the F'-bilayers.
(c) *Rows.* For fixed c ≥ 1 the sites (·, ·, c), surface and sub-surface alternately, form a path
 … (a, b, c) – γ=(a+1, b, c) – (a+1, b−1, c) – …; for fixed b ≥ 1 a path … (a, b, c) – γ=(a, b, c+1) – (a−1, b, c+1) – …; for
fixed a ≥ 1 a path … (a, b, c) – γ=(a, b+1, c) – (a, b+1, c−1) – ….
(d) *Margins.* In skin j no site of a row b ≤ j−1 and no site of a row a ≤ j−1 lies on a column. A site of the row
c = 1 lies on the column of the dangling site of a site of F' with c = 0 (a site of e1) or c = 1.
Proof. (a) γ + t_i (i = 1, 2, 3) raises f_i by 3 and lowers the others by 1. (b) The dangling site is v − t_4, an
A-site with f_4 = −(2(m+2)−2) and f_i(v) + 1 for i ≤ 3: the sub-surface site (a+1, b+1, c+1) of skin 1. In the quadrant
(+,−) the column continues by +t_3 and −t_4 alternately (Lemma C): +t_3 leads to the surface site (a+1, b+1, c) of skin 1,
−t_4 to the sub-surface site (a+2, b+2, c+1) of skin 2, and so on. The F'-bilayers lie in the open quadrant (+,−),
which otherwise contains only columns over big face 3; on those f_3 ∈ {2M−3, 2M−2} in skin j, whereas the sites
used here have f_3 ≤ 2M−6 (sub-surface, γ_3 ≥ 1) or would need f_4(v) = −(2m+2) for a site v of Oct(m) (surface).
(c) follows from (a), (d) from (b). ∎

### 8.3 The interior: the Bulk Lemma

X_m := Oct(m) minus the twelve edge zigzags.
**Bulk Lemma [computer-assisted].** For every m ≥ 9 the set X_m is a disjoint union of lattice paths ("runs"), each
with at least 3 sites, whose end sites are surface sites; the paths are given by the following rules.

**Construction** (code: canon.py). Coordinates Y, Z, ρ, α and the rungs of §8.1; "foliation bond" = rung.
1. *Bent foliation*: join two neighbouring sites iff their ρ differ. Each site has exactly two
 partners; α is constant along a chain and ρ has no local maximum, so the chains are V-shaped lines without
 cycles; inside Oct(m) they are cut into paths whose ends have a free bond.
2. *Delete the edge zigzags.* [CHECKED] On six edges (the four in the plane Y ∈ {−1,0,1} and two of the four near
 Z = 0) the edge sites are paired by the foliation among themselves: nothing is damaged. On the four edges in the
 plane X ∈ {−1,0,1} every edge site, and on the other two edges near Z = 0 every second edge site, is the end of a
 path coming from inside; removing it leaves a *damaged end* (10m − 26 in total).
3. *Rule merges.* A damaged end d is joined to its neighbour w with (ΔY, ΔZ) = (sgn Z, −sgn Y) if Y, Z ≠ 0, and with
 (ΔY, ΔZ) = (−sgn Y, +1) if Z = 0, provided w ∈ X_m is a path end with a free bond and no other damaged end claims it.
 (10m − 37 merges; they leave 10 damaged ends and one isolated site, all next to vertices.)
4. *Vertex patches.* Six explicit lists of bonds to add (32 in all) and to remove (19), in coordinates relative to
 each vertex (Appendix B; found once, for m = 14, by a local search).

**Lemma K (locality of the cover)** [added 14 November 2026]. Rules 1–3 are applied to all sites simultaneously
(in rule 3 all claims are collected first; a damaged end d is joined to its rule-neighbour w iff w ∈ X_m is an end
with a free bond and no other damaged end has w as rule-neighbour), and they commute with every lattice
translation that preserves Oct(m), the zigzags and the signs (and zeros) of Y and Z on the sites concerned.
The bonds of the cover at a site q, and whether q is an end with a free bond, are determined by these data on the
sites within 4 bonds of q, together with the patch bonds at q; a patch bond has both ends within max-norm 8 of
its vertex (Appendix B).
Proof. Rules 1, 2 at q read the neighbours of q. For rule 3 with q = d one reads w (1 bond), the neighbours of w
(2 bonds) and, to decide which of them are damaged ends, their neighbours (3 bonds); for q = w alike. A free
bond of q is read at its neighbours. ∎ [CONFIRMED, edgeperiod.py: for m = 40, 41, 50 and all twelve edges the cover
within max-norm 6 of e[i] is the translate of that at e[i+2] for 12 ≤ i ≤ 2m−16, with the same pattern for the
three sizes.]

**Claim 1 (it is a cover by paths with good ends).** Every site of X_m gets one or two partners; sites with one
partner have a free bond; no component has fewer than 3 sites.
These are statements about the cover within two
bonds of a site, hence (Lemma K) about Oct(m), the zigzags and the signs of Y, Z within 6 bonds, and about the
patch of a vertex within 26 bonds. By the Consequence of Lemma T′ (D = 26, R = 0) they hold for every m ≥ 88, because
they hold for m = 88 and m = 89 [CHECKED, claim1.py: valid, shortest path 6 sites]. They were also checked directly
for every m = 9 … 60, for 64, 68, …, 100 and for the sizes 80, 82 of the test layouts of §8.4. All remaining sizes 61 ≤ m ≤ 87 were then checked as well [CHECKED, claim1.py, log claim1_61_87.log]. So Claim 1 holds
for every m ≥ 9, and for every m from 9 to 89 (and 92, 96, 100) the whole Bulk Lemma was validated directly: the
program decomposes the cover into paths, which excludes cycles. For larger m the lemma rests on Claims 1 and 2;
see the paragraph "Not fully proved" at the end of this section for what is missing in Claim 2.

**Claim 2 (no cycles).** Every bond of the cover that is not a foliation bond joins sites with equal ρ, hence changes
α by ±2. Cut each component into *segments* of constant α. For a segment P let X̂ = min X + max X and
 Ω(P) := (2, |X̂|, 0) if P contains a damaged end with Z = 0 ("row segment"); (1, α, X̂) if P is not a row segment
 and α > 0; (0, X̂, 0) if P is not a row segment and α < 0; these triples are ordered lexicographically.
 [Corrected 14 November 2026. The earlier version used the numbers C + |X̂|, K·α + X̂, X̂ with the fixed constants
 K = 10⁴, C = 10⁹. They give the lexicographic order only while 4m < K and K·2m + 4m < C, i.e. for m below about
 5·10⁴; beyond that the numerical version is false, see the witness after (b). All machine checks of this section
 were made for m ≤ 100, where the two orders coincide, and have been repeated with the lexicographic order.]
Two joined segments never have equal Ω. A cycle would contain a segment that is
the maximum of Ω on the cycle, i.e. a segment joined at both ends to segments of smaller Ω.
 (a) *Away from the vertices this never happens.* For a segment joined at both ends, both joints farther than 12
 from every vertex, the way it is joined depends only on (kind, sign of Y or Z, X̂, α mod 4, and α itself if
 |α| ≤ 5): a table that depends only on the parity of m: the same 39 entries for every even m = 18, …, 60, the same 39 entries
 for every odd m = 19, …, 59, 74 in the union and no clash in the union; the sizes 14, 15, 16, 17 have 10, 19, 26, 33
 entries [CHECKED, bulktable2.py 14 60. Corrected 14 November 2026: the earlier version said "74 entries, the same
 for all m = 14 … 44"; 74 is the size of the union over both parities.] In the table: a segment with
 α > 0 always has one neighbour with α+2 and one with α−2; a segment with α < 0 has its neighbours on opposite sides
 in X̂, or a neighbour with α > 0; a row segment has a row neighbour farther out. So one neighbour has larger Ω.
 (That this table is the same for every m is proved below, "Completion".)
 (b) *Near the vertices* there are exactly 10 segments that are local maxima of Ω, at the same positions relative
 to the vertices for every m. For each of them, following the path from it one meets, within 6 segments and without
 leaving the neighbourhood of the vertex, either an end of the path or a segment with larger Ω.
 [CHECKED for every m = 9 … 60 and 64, …, 100, certify.py]
 *Witness against the numerical potential* (found by an independent audit; reproduced by certify_lex.py witness).
 At the −y vertex, which is the origin for every m, the cover contains the segments P = {(0,4,0), (1,3,−1)},
 Q = {(−1,3,1)}, R = {(2,4,−2)}; P is joined to Q and to R; Q is a row segment with |X̂| = 2; α(P) = 2m−7, X̂(P) = 1;
 α(R) = 2m−9, X̂(R) = 4. With the numbers of the earlier version, Ω(P) = 10⁴(2m−7)+1 exceeds Ω(Q) = 10⁹+2 as soon as
 m ≥ 50 004 — for instance for m = 50 034, the size §6 gives for K = 1, B = 252 —, and the two walks from P (row
 segments with |X̂| = 2, 5, 9, 13, 17, 21; segments with α = 2m−9, 2m−11, …) meet no larger value within six segments.
 In the lexicographic order Ω(Q) = (2,2,0) > Ω(P) = (1, 2m−7, 1) for every m: P is not a local maximum.
 *Parts (a) and (b) for the lexicographic order, uniformly in m.*
 (i) Two joined segments differ by 2 in α. Their comparison uses only: which of them are row segments, the signs
 of their α, and the signs of the differences of their α, of their X̂ and of their |X̂|.
 (ii) Part (a) uses nothing else: for a non-row segment with α > 0 the neighbour with α+2 is a row segment or has
 class 1 and a larger α; for α < 0 the neighbour on the side of larger X̂ has class 0 and larger X̂, or a higher
 class; a row segment has a row neighbour with larger |X̂|.
 (iii) *Vertex boxes.* By Lemma K and Lemma E(a) (D = 48), for every m ≥ 50 and every vertex V the cover inside
 Box(V,44) is the translate of the cover for m = 50; hence so are the segments contained in Box(V,43), their joints,
 their being row segments, and the differences of α and of X̂ between any two of them. The signs of α do not
 depend on m either: near ±x, Y and Z are not changed; near ±y every site of the box has α ≥ 2m−91 > 0; near ±z,
 α < 0. Near ±x all X̂ have the sign of the vertex, and near the other vertices X is not changed, so the order of
 the |X̂| is preserved. So the order of Ω between any two segments inside Box(V,43) is the same for all m ≥ 50.
 (iv) By (S2) below, a segment with a joint within distance 16 of a vertex V and the six next segments along its
 path in both directions lie in Box(V,43). So the list of such segments that are local maxima, and for each of
 them the certificate "an end of the path or a larger Ω within six segments", are the same for all m ≥ 50. They
 were verified with the lexicographic order for every m from 9 to 60: no ties, exactly ten strict local maxima,
 the same ten for 14 ≤ m ≤ 60, each certified within six steps [CHECKED, certify_lex.py cert 9 60]. A segment
 joined at both ends with both joints farther than 12 from every vertex is covered by (a).
 Status: (i)–(iv) are proved, given (S2) and part (a) for all m; (a) for all m is the Completion below, which
 rests on the finite checks named there.
 So no segment can be the maximum of Ω on a cycle: there is no cycle. ∎

**Completion of the proof of Claim 2 for all m.** "Joint" = a bond of the cover that is not a
foliation bond; "segment" = a maximal piece of a path without joints (it lies on one V-shaped foliation line).
 (S1) By construction every joint is within 2 bonds of one of the six damaged edges (the four X-plane edges, two
 Z-plane edges) or inside a vertex patch.
 (S2) A segment with a joint within 2 bonds of a Z-plane edge, or within distance 16 of a vertex, has at most 30
 sites [CHECKED m = 24, 31, 40, 53, lines.py]. The configurations at a vertex (these segments and six further
 segments along their paths) lie within distance 43 of the vertex and are the same for m = 30, 40, 53 (233 segments
 in all) [CHECKED, extents.py]. These are statements about balls of radius 45 around a vertex, or of bounded radius
 around a site of a Z-plane edge; by (T-x), (T-y), (T-z) of 5.6 and translation along the edge such balls are the
 same for all m ≥ 45. So everything these segments do (their joints, their neighbours, the comparison of Ω, the ten
 local maxima of part (b) and their certificates) is the same for all m ≥ 45, and it was checked for every m ≤ 60.
 (S3) Every other segment with a joint ("long") has all its joints within 2 bonds of X-plane edges, in the slabs
 |X| ≤ 5, away from the vertices [CHECKED same runs; it follows from (S1), (S2)]. Such a segment is the whole
 intersection of a foliation line L with X_m, and each of its ends is covered by (T-r).
 (S4) *Lines.* (i) By (T-r) at both ends, the cover of Oct(m+2)° near the two ends of L is the translate (outwards
 along L) of the cover of Oct(m) near the two ends of L: the same line has the same joints for m and m+2.
 (ii) If L bends at Z = 0, on the side Y > 0 say, all of L has Y ≥ α > 0 and both ends see only faces with s_y = +1;
 (T-y) maps L to the line with α+4 and the same X-values, and both end-balls at once. With (i): inside one
 octahedron the lines α and α+4 (same X-values) have the same joints, as long as both are long. Likewise with
 (T-z) for lines bending at Y = 0.
 So for long segments the pair (joint at one end, joint at the other end), including the changes of α and of X̂
 across the joints, is a function of (bend plane and side, X-values, α mod 4) for |α| > 5, and of the line itself for
 |α| ≤ 5 where a neighbour can lie in another family; all classes of one parity of m occur from m = 18 resp. 19 on. This is the table of (a)
 [bulktable2.py: 39 entries for each parity, identical for all even m = 18 … 60 and for all odd m = 19 … 59]. Its content, which can also be read off by hand: the four
 X-plane edges have "d-lines" (ending just below an edge site) and "w-lines" (ending on the second row), the X-pair
 of a line shifts by +1 across a bend at Z = 0 and by −1 across a bend at Y = 0; therefore lines bending at Z = 0 are
 d at both ends or w at both ends and form ladders d(α) – w(α+2) – d(α+4) – … (α strictly monotone), while lines
 bending at Y = 0 form paths of at most five lines with strictly monotone X-values. [CHECKED lines.py: every long
 segment with two joints is of one of these two kinds, m = 24, 31, 40, 53.]
 With (S2)–(S4), parts (a) and (b) of Claim 2 hold for every m ≥ 45, and for 9 ≤ m ≤ 60 the cover was validated
 directly. (computer-assisted: the finite checks are those of certify_lex.py, bulktable2.py, lines.py, canon.py)

 **Proposition A (part (a) for every m)** [added 14 November 2026; it replaces the incomplete argument (S3), (S4), which
 is kept above only as a description]. Let m ≥ 81, and let m_0 ∈ {59, 60} and m_1 ∈ {79, 80} have the parity of m. Every segment P of
 the cover of X_m with two joints, both farther than 12 (max-norm) from every vertex, has the same key and the
 same value as such a segment of the cover of X_{m_0} (if P is of class X, see (A2)) or of X_{m_1} (class Z). The tables
 of the sizes 18, …, 60 and 79, 80 were computed; they depend only on the parity and have the properties A′, B′, C′
 [bulktable2.py]. So (a) holds for these sizes and for every m ≥ 81. (For every m ≤ 89 the Bulk Lemma was in addition
 validated directly, see Claim 1.)
 Notation: p = v − c, centre coordinates of each size; faces s·p ≤ b_s(m), and b_s(m) − b_s(m_0) = 2(m − m_0).
 (A1) *Rungs and bends.* At a site with Y, Z ≠ 0 in the quadrant (σ, τ) the rungs have ΔX = στ at an A-site and −στ at
 a B-site (§8.1); so on an arm the A-sites have one value x_A of X and the B-sites x_A + στ. A site with Z = 0 is a
 B-site (z = 1 is odd) and a site with Y = 0 is an A-site; at such a site the two partners are the two neighbours
 with larger ρ, on the two sides, at X − 1 and X + 1 in an order fixed by the sublattice and by σ (resp. τ). Hence
 the three values of X on a foliation line, and which arm carries which pair, are determined by the bend plane,
 the side (σ resp. τ) and x_A of one arm — not by α or m. A line with α > 0 bends at Z = 0, one with α < 0 at Y = 0.
 Inside Oct(m), ρ and |X| + ρ increase along each arm away from the bend, so the part of a line inside Oct(m) is
 connected and contains the bend.
 (A2) *P and its joints.* Patch bonds lie within 8 of the vertices, so both joints are merges (d, w) of rule 3: d is
 a neighbour of a deleted zigzag site of a damaged edge, w a neighbour of d. Each end of P carries one joint and
 P is a path of foliation bonds between its ends. Call an end of *class X* or *Z* according to the plane of that
 damaged edge. If one end is of class X then |X| ≤ 3 there and |X| ≤ 5 on all of P; a zigzag site of a Z-plane edge
 with |X| ≤ 7 has |Y| ≥ 2m − 10 and lies within 8 of a vertex ±y; so the other end is of class X too. If both ends are
 of class Z, then |Z| ≤ 4 at the ends; a line with α < 0 would have |Y| ≤ 3 there and the ends would be within 10 of a
 vertex ±x; so α > 0, the line bends at Z = 0, |Z| ≤ 4 on all of P, and P has at most 9 sites.
 (A3) *Class X, |α| ≤ 2m − 38.* Let α′ := α if |α| ≤ 2m_0 − 38, and otherwise the number of the same sign with |α′| ≡ |α| (mod 4)
 and 2m_0 − 42 < |α′| ≤ 2m_0 − 38; so α′ ≡ α (mod 4), and α′ = α if |α| ≤ 5. For a quadrant q = (σ, τ) let τ_q be the
 translation with ΔX = 0, Δ|Y| = (m − m_0) + (α − α′)/2, Δ|Z| = (m − m_0) − (α − α′)/2. Both numbers are even and their sum
 is ≡ 0 (mod 4), so τ_q is a lattice translation preserving the sublattices; it adds α − α′ to α and 2(m − m_0) to ρ,
 and s·τ_q = 2(m − m_0) for the two faces of the quadrant q. So τ_q maps the arm with (x_A, α′) in q onto the arm with
 (x_A, α), and the half-spaces of the two faces of q for the size m_0 onto those for the size m. At an end of P in
 q the other six faces have depth ≥ 2m − 7 − |α| ≥ 31 (four of them have s·p = ±X ± α, |X| ≤ 5; two have s·p ≤ 5 − ρ), and at the
 corresponding point for m_0 depth ≥ 2m_0 − 7 − |α′| ≥ 31; these depths exceed 3·10. The end has ρ ≥ 2m − 8, so |Y|, |Z| ≥ 15 there. Hence on the boxes of radius 10 around the two points Oct, the zigzag and the signs of Y, Z
 correspond under τ_q, and by Lemma K so does the cover within 6 bonds: the end of the arm, its joint, the site at
 the other side of the joint, the α and the x_A of the arm through that site. Let L′ be the foliation line of
 the size m_0 containing the arm (x_A, α′) in the quadrant of one end of P. By (A1) its other arm corresponds in
 the same way to the other arm of the line of P (if the two ends of P lie on one arm, nothing is needed). The
 piece P′ of L′ between the two corresponding ends lies in X_{m_0}, contains no patch bond (|X| ≤ 5 and its ends
 are at least 14 from the vertices ±y, ±z), and has the two translated joints: it is a segment with two joints
 farther than 12 from every vertex. Kind, sign data and X̂ of P and P′ agree by (A1), and α ≡ α′; so the keys
 agree. A neighbour Q of P has α ± 2 and |X| ≤ 6; it is the whole piece of its line in X_m (its end at the joint
 has no second foliation bond, and its line meets no patch); it contains no damaged end with Z = 0 (such a site is a
 neighbour of a Z-plane zigzag site and has |X| + |Y| ≥ 2m − 5, whereas the site of Q with Z = 0 has |Y| = |α ± 2| ≤ 2m − 36); so its kind is given by the sign of α ± 2
 and its X̂ by (A1) from the x_A of its arm at the joint. The same holds for the neighbours of P′. So the values
 agree.
 (A4) *Class X, |α| > 2m − 38.* Let V be the vertex with the sign of Y (if α > 0) resp. of Z (if α < 0). On P, |X| ≤ 5,
 ρ ≤ 2m − 1 and the smaller of |Y|, |Z| is (ρ − |α|)/2 ≤ 18, so P ⊂ Box(V, 37); its neighbours, with |α ± 2| > 2m − 40, lie in
 Box(V, 39); the cover there is determined in Box(V, 43). By Lemma E(a) (D = 43) and Lemma K the translation V ↦ V′
 carries all this to the size m_0; it keeps X, changes α by ±2(m − m_0) ≡ 0 (mod 4), and |α| > 5 on both sides. So the
 corresponding segment of size m_0 has the same key and value, and its joints are equally far from V′.
 (A5) *Class Z.* By (A2) P has at most 9 sites and lies within max-norm 10 of a zigzag site e[i] of a damaged
 Z-plane edge. Let Q be a neighbour and A* its end at the joint; A* is within 3 bonds of a zigzag site, so its
 depth below the two faces of the edge is ≤ 8, hence |X| + |Y| ≥ 2m − 10 and |Z| ≤ 5 at A*. Q has α ± 2 > 0 and bends at Z = 0;
 at its bend |X| + |Y| ≥ 2m − 17, and t steps further |X| + |Y| + |Z| ≥ 2m − 17 + 2t, which must be ≤ 2m; so t ≤ 8. Thus Q has |Z| ≤ 8
 beyond the bend, lies within 13 of A*, hence within 17 of e[i], and all the data are determined by the cover in
 Box(e[i], 17), i.e. (Lemma K) by Oct, zigzags and signs in Box(e[i], 21). If 42 ≤ i ≤ 2m − 44, choose i′ ≡ i (mod 2) with
 42 ≤ i′ ≤ 2m_1 − 44 such that the translation e[i] ↦ e′[i′] changes α by a multiple of 4 (two steps along the edge
 change α by 2, so one of two consecutive admissible i′ works); by Lemma E(b) (D = 21) and Lemma K the
 configuration is the translate of one of the size m_1. Otherwise e[i] is within 42 of a vertex V, everything
 lies in Box(V, 63), and Lemma E(a) (D = 63 ≤ m_1 − 2) with Lemma K gives the same, α being changed by 0 (near ±x) or
 ±2(m − m_1). In both cases the corresponding segment of size m_1 is a row segment [CHECKED for m_1 = 79, 80: every
 segment of class Z with two far joints is a row segment, segstruct.py]; so P is a row segment, its key ('row',
 sign of Y, sign of X̂, α mod 4) agrees (for the α-part of the key: in the interior case P lies within 10 of e[i], so |Y| ≥ i − 11 ≥ 31 and α ≥ 27 on both sides,
 and α changes by a multiple of 4; near ±y, |Y| ≥ 2m − 65 resp. 2m_1 − 65 and α changes by ±2(m − m_1) ≡ 0 (mod 4); near ±x the
 translation changes neither Y nor Z, so α itself is the same. [Corrected after the fourth audit: the previous
 version claimed |Y| ≥ 12 on P. That is false: at m = 336 the row segment {(−657,659,1), (−656,658,2)}, whose joints are
 13 and 14 from the vertex −x, has Y = −11 and α = 11. No lower bound for α is needed.] The sign of X̂ is constant
 along the edge away from ±y, and X is unchanged near ±y), and the value, which consists of differences and kinds, agrees. ∎
 [CONFIRMED, segstruct.py for m = 40, 41, 59, 60, 79, 80: the far two-joint segments are of class X (|X| ≤ 4, complete
 pieces of their lines, no row) or of class Z (rows, α > 0, at most 2 sites); none is mixed. bulktable2.py: the
 per-size tables are identical for all even m = 18 … 60 and m = 80, and for all odd m = 19 … 59 and m = 79.]
 Status of Claim 2 after this: (a) is proved for all m ≥ 81 given the tables of the sizes 59, 60, 79, 80 (machine), and checked directly for 18 ≤ m ≤ 60; (b) as in
 (i)–(iv). Proposition A was written on the day of the third audit and has not been read by anyone else.

### 8.4 The near field

**Placement of the H's.** V_a := c − (2m−2)e_z, V_b := c + (2m−2)e_y, V_c := c + (2m−2)e_x are the corners of F';
e1 runs from V_a to V_b, e2 from V_b to V_c, e3 from V_a to V_c (as in (O7)). Write e[i] for the site of zigzag index i.
* The three PHP's of the frame chain on V_a, V_b, V_c; the other three PHP's on the other three vertices; the
 first H on the corner e1[2m−3] = e2[1].
* The frame runs on the sites of e1 and e2 that are not skipped (skips as in §6), in order.
* Entry anchor of separator group k on the 2-slot (e1[6k], e1[6k+1]): first H on the a-site e1[6k].
 Exit anchor of group k on the 6-slot with number κ = K+1−k, i.e. on the sites w_0 … w_5 of e2 with indices 10κ+6 …
 10κ+11 from V_c, in the order w_1 w_0 · w_2 w_3 · w_5 w_4 (first H on the b-site w_1, last H on the a-site w_4).
* Track dimers D_0 := (e1[2], e1[1]) and D_i := (e3[2i], e3[2i+1]), i = 1 … m−2, each written (a-site, b-site). The
 left filler on D_0 … D_{J−1}; separator k on D_{j_k}, D_{j_k+1} in the order b a · a b; the items of bin k, in any order, on
 D_{j_k+2} … D_{j_k+C+1}; the right filler on D_{j_{K+1}+2} … D_{m−2}. Every chain other than a separator starts on a dimer
 of even index and visits its dimers alternately in the orders a b and b a. Since J, C and all item sizes are
 even, every end of an item and both ends of the left filler are a-sites; the right filler (R odd) ends on the
 corner e3[2m−3].
* The three rings: for each other small face the 6(m−2) boundary sites that are not vertices, taken side by side
 in the order b_0, a_1, b_1, …, a_{m−2} on each side, paired consecutively, the dimers visited alternately as b a and
 a b. (For even m the PPP at each corner joins the two consecutive b-sites b_{m−3}, b_{m−2} of a side.)
* The bulk runs on the paths of §8.3.
Every site of Oct(m) receives exactly one H.

**The P's near the surface.**
* *Caps.* Each end of an H-run that is attached to a long linker, or to a tether, has its P on the dangling site
 of that end (for a vertex: on one of its two).
* *PPP* between two consecutive dimers of a chain: the unique path of (O2). Between a-sites it runs over the big
 face of the edge, between b-sites over the small face.
* *Frame links* P^3, P^6, P^10: the explicit paths of Appendix C. The link over every 2-slot is the translate
 e1[6k−1] + Λ_2 of one path, the link over every 6-slot the translate of one path Λ_6, and the four links at V_a, V_b,
 V_c are fixed lists relative to the vertex. (No search is involved in their definition.)
* *Tethers:* the explicit routes of Lemma N (N4).
* *Columns.* A cap p that starts a long linker continues along its column, or, if the second site of that column
 is used by a frame link, along a *borrowed* column: the column of a dangling site p' whose second site is a
 neighbour of p, from that second site on.
Everything except the positions of the item chains is independent of the packing. For the item chains, both
possibilities at each place between two consecutive a-sites inside a bin (a PPP, or two caps with their columns)
are provided for in advance: nothing else uses those sites or columns.

**Layouts and the family 𝓕** [added 14 November 2026]. A *layout* ℓ = (m; K; J; C; R; cuts) consists of an even m,
K ≥ 1, even J and C, an odd R with m = J + K(C+2) + R + 3, and for every bin a division into consecutive items of even
sizes; with j_k := J + (k−1)(C+2) it determines the placement of the H's and the P's near the surface exactly as
described above. 𝓕 is the set of layouts with **m ≥ 80, m ≥ 5K + 40, J ≥ 14, R ≥ 15 and all items of size ≥ 4**.
Every layout that §6 and a packing produce lies in 𝓕: there J = C + Σ* + 8 ≥ 132, R = J + 1, every item has
λ s_i ≥ 66 dimers, and m = (K+2)(18K+48)B + 38K + 100 ≥ 336 and > 5K + 40. The test layouts used below lie in 𝓕 as well.

**Lemma N (near field) [computer-assisted; restated].** For every layout of 𝓕 — in particular for every layout of §6 — and every packing:
 (N1) the frame links exist inside skin 1 and avoid the dangling sites of the slot sites, of the corners and of
 e1[2], and the dangling sites and second column sites of all bulk run ends;
 (N2) every cap whose second column site is used by a frame link has a borrowed column whose sites are otherwise
 unused;
 (N3) no site of the second row of a face along an X-plane edge (E(1,2), E(2,1), E(3,4), E(4,3)) is a bulk run end;
 (N4) the 2(K+1) tethers exist, pairwise disjoint, disjoint from all other near-field P's and from all columns of
 linker caps, of lengths 2j_k + 3 + σ_e(k) and 2(m−2−j_k) + 3 + σ_x(k) with σ_e(k) = 10k + 2 ≤ 10k + 5 and σ_x(k) = 14K + 22 − 6k ≤ 18K + 15 (both < Σ*);
 (N5) no near-field P lies on the column of a linker cap, and the columns of different linker caps are disjoint.
Proof.
*(N4).* Entry tether k uses skin j := k+1, exit tether k uses skin j := K+2+k. Coordinates of §8.2. The b-site of the
2-slot k is the site (m−2−3k, 3k, 0) of F'; the first and second b-site of separator k are (m−2−j_k, 0, j_k) and
(m−3−j_k, 0, j_k+1); the b-site w_1 of the 6-slot κ is (0, 5κ+3, m−5−5κ).
Entry route: (1) from the tether cap of the slot's b-site up its borrowed column (Appendix C; it is the column of
the site (m−3−3k, 3k, 1) of F') to its sub-surface site (m−3−3k+j, 3k+j, 2) of skin j, and to the surface site
(m−3−3k+j, 3k+j, 1); (2) along the row c = 1
in the direction of decreasing b until the surface site with b = j−1; (3) along the row b = j−1 in the direction of
increasing c until the surface site (m−2−j_k+j, j−1, j_k+1); (4) to the sub-surface site (m−2−j_k+j, j, j_k+1), which lies
on the column of the separator's first b-site (Lemma R(a),(b)); (5) down that column to its dangling site.
Exit route: up the column of the separator's second b-site to the sub-surface site (m−3−j_k+j, j, j_k+2); to the
surface site (m−3−j_k+j, j−1, j_k+2); along the row b = j−1 with increasing c until a = j−1; along the row a = j−1 with
increasing b until the surface site (j−1, 5κ+3+j, m−4−5κ); to the sub-surface site (j, 5κ+3+j, m−4−5κ) on the column of
w_1; down that column.
These sites are free: rows b ≤ j−1 and a ≤ j−1 carry no column (Lemma R(d)). A site of the row c = 1 lies on the column of
a site of e1 or of a second-row site along e1; e1 carries no linker cap on F' (the anchors' linker caps are on
a-sites, the corner e1[1] and the b-sites of the frame have no linker), second-row sites are not run ends (N3), and
the columns used by entry tethers of slots nearer to V_a end in lower skins, while those of slots farther away
are met at larger b than the route reaches. The columns of all separator b-sites pass skin j in the row b = j, those
of the 6-slots and of the corners at V_b, V_c in the row a = j (Lemma R(b)); the routes use only rows b = j−1, a = j−1 there.
Different tethers have different skins for their rows, and all near-field P's other than tethers and columns
lie in skin 1. *The tether is this route and nothing else* (no shortest-path search). Counting its P-sites exactly — a unit
step of a row consists of two sites (Lemma R(c)) —: entry tether k has 2j−2 column sites (the cap included), the
sub-surface site, the surface site (m−3−3k+j, 3k+j, 1), 2(3k+1) sites of the row c = 1 (from b = 3k+j down to b = j−1,
ending at (m−2+j, j−1, 1)), 2j_k sites of the row b = j−1 (from c = 1 up to c = j_k+1), the sub-surface site
(m−2−j_k+j, j, j_k+1) and 2j−2 column sites; with j = k+1 this is **2j_k + 10k + 5**, so σ_e(k) = 10k + 2. Exit tether k
(j = K+2+k, κ = K+1−k): (2j−2) + 1 + 1 + 2(m−2−j_k) + 2(5κ+4) + 1 + (2j−2) = **2(m−2−j_k) + 14K + 25 − 6k**, so σ_x(k) = 14K + 22 − 6k;
its rows meet at the surface site (j−1, j−1, m). Consecutive sites of a route are bonded (Lemma R(a), (c)); both
slacks are even, depend only on k and K, and satisfy σ_e(k) ≤ 10k + 5 and σ_x(k) ≤ 14K + 16 ≤ 18K + 15 < Σ*; nothing depends
on the packing. The "only if" direction (§7) uses only σ_e, σ_x ≤ Σ* and is not affected.
[Erratum, third audit. The previous version called the tethers "the shortest paths inside these rows and columns"
and quoted σ_e(1) = 6, σ_e(k) = 10k − 2, measured with build3.py. Its search ran over a larger part of the bilayer
than the rows named here, so the word prescribed fewer P's than these rows need: for K = B = 1 (m = 336, j_1 = 132)
273 instead of 279. Text and code now use the same explicit route (tether_explicit in build3.py).]
[CHECKED, tether_local.py — written from this text, independent of the builder, no octahedron is constructed —:
for the parameters of §6 with (K,B) = (1,1), (1,2), (1,252), (2,1), (3,2), (9,1), (10,3), (12,1), i.e. m = 336 … 50 034, and
for the test layouts: every route is a self-avoiding lattice path whose sites lie in the stated skins, with the
caps bonded to the right H's; the lengths are the two formulas; all 2(K+1) tethers are pairwise disjoint; a row
site lies on a column of F' only in the row c = 1, and then on the column of a site of e1 or of the second row
that carries no tether in that skin. For m = 336, k = 1: cap (2,678,−664), borrowed second site (3,679,−663), column
site of skin 2 (4,680,−664), rows (332,5,1) → (336,1,1) → (204,1,133), target column site (266,674,−408), target cap
(266,672,−406), 279 P's — the coordinates found by the audit.]
*(N3).* Along an X-plane edge the inner neighbour d of each edge site is a damaged end of §8.3 whose two other
neighbours on the surface are second-row sites; the clockwise rule joins d to one of them, always on the same
side, so away from the vertices every second-row site is claimed exactly once and is not an end. Near the
vertices: part of the checks below.
*(N1), (N2), (N5).* [Rewritten 14 November 2026 after an independent audit. The earlier proof used base cases
m = 80, 82 with J = 8 and items of size 2, an induction "K → K+1 adds one slot and one separator", and a machine
comparison of balls of radius 5. None of this covers the layouts of §6 (m ≥ 336; C, J, R and every j_k change with K),
and balls of radius 5 cannot certify a rule that reads radius 11. The argument below has no induction over m or K
and no search rule.]
 (1) *Objects.* The P's of skin 1 are grouped into *objects*, each attached to an *owner* by an explicit rule that
 commutes with lattice translations: the cap of a run end (its dangling site); the PPP of two consecutive dimers
 (the unique path of (O2)); the second column site of a linker or tether cap (the second site of its arm; for the
 two caps of a 2-slot anchor and the cap of e1[2] the borrowed ones of Appendix C); the frame links of Appendix C. Nothing is defined
 by a search, so an object depends only on its owner and on Oct(m) and the signs of Y, Z within 4 bonds of it
 (for the explicit lists of Appendix C: on nothing).
 (1′) *Bulk caps are not objects of this classification.* A bulk run end is a site of X_m, not of an edge zigzag
 [the previous version overlooked this when it said that all owners are zigzag sites or vertices]; its cap is its
 dangling site, its column the arm of that site. Each interaction is covered as follows.
 – bulk–bulk: caps of different run ends are different dangling sites, and all columns are pairwise disjoint in
   every skin: Lemma C.
 – bulk cap or bulk second column site against an edge-owned object of skin 1 (frame link, PPP, cap, second column
   site): the clause on bulk run ends in (2), with (3b) and the test layouts of (4), (6): which surface sites near
   the object are run ends is decided by the cover in Box(u,16) resp. Box(u,9), and the tests assert that no site
   of the object is the dangling site or the second column site of such a run end.
 – borrowed columns: a borrowed column is the column of a dangling site that is not the cap of any run end
   (Appendix C; asserted in build3.py), from its second site on; by Lemma C it is disjoint from all bulk columns.
 – bulk columns against tethers, beyond skin 1: (N4) — rows b ≤ j−1, a ≤ j−1 carry no column (Lemma R(d)); the row c = 1
   meets only columns of e1-sites, which are not in X_m, and of second-row sites, which are not run ends by (N3).
 (2) *Owners, radii, and what has to hold.* The objects of this classification are the *edge-owned* ones; their
 owners are sites of an edge zigzag, or vertices:
 – the owner of a cap and of its second column site is the run end u that it caps: the cap is bonded to u, the
   second column site is within max-norm 2 of u;
 – the owner of a PPP is its first H, u. Its second H, w, lies on the same zigzag two indices further,
   |w − u|_∞ = 2, and each of the three P's is within max-norm 3 of u and of w. [The previous version said 2.
   That was false: for m = 336 the PPP between H(45,671,−625) and H(47,671,−623) of e3 is (46,672,−626), (47,673,−625),
   (48,672,−624), and no site of e3 is within 2 of all three (independent audit). The bound 3 is now asserted in
   build3.py for every PPP it builds.]
 – the owner of a frame link is its reference H of Appendix C; its sites are within max-norm 9 of it;
 – tethers are not objects (they are the subject of (N4)); their caps and second column sites are.
 (V1) For each object: its sites are outside Oct(m), consecutive sites are bonded, its ends are bonded to the H's
 they belong to. (V2) Two different objects are disjoint; no frame-link site is one of the sites excluded in
 (N1); no object contains a first or second column site of a linker cap other than its own.
 Consequences. (V1) for an object with owner u is a statement about Oct(m) in Box(u, 10) (frame link) resp.
 Box(u, 4). Two objects can meet only if their owners are within max-norm 18 (two frame links), 12 (a frame link
 and another object) or 6 (two other objects) of each other; we use the cutoffs **20, 13, 6**. A dangling site or
 second column site of a bulk run end that an object could contain belongs to a surface site within 2 of a site
 of the object, hence within 11 (frame link) resp. 5 of its owner, and whether that surface site is a run end is
 decided by the cover within 4 bonds of it (Lemma K): inside Box(u, 16) resp. Box(u, 9).
 (3) *Translation classes* (Lemma E, Lemma K; ℓ, ℓ' two layouts of 𝓕, τ the translation taking the owner u of ℓ to
 the owner u' of ℓ').
 (3a) Shapes: if u, u' are sites of the same edge with zigzag indices i ≡ i' (mod 2), both between 10 and 2m−12
 resp. 2m'−12, then τ maps the object of u onto the object of the same type of u' (Lemma E(b), D = 5: a cap, a PPP
 or a second column site lies in Box(u,3) and is determined by Oct and the signs of Y, Z in Box(u,5); for the lists
 of Appendix C nothing is needed).
 (3b) Surroundings: τ maps Oct, the zigzags, the signs of Y, Z and the bulk run ends of ℓ in Box(u,16) onto those
 of ℓ' in Box(u',16) if either u, u' have the same position relative to the same vertex V, at index ≤ 40 on an
 edge from V (then |u − V|_∞ ≤ 41; Lemma E(a), D = 61, and the patch of V), or u, u' lie on the same edge at indices
 i ≡ i' (mod 2) between 40 and 2m−42 resp. 2m'−42 (Lemma E(b), D = 20; no patch reaches Box(u,16)). For owners of
 objects other than frame links the same holds for Box(u,9), with index ≤ 25 for the vertex kind and indices
 between 26 and 2m−28 for the edge kind (Lemma E(b), D = 13). Every owner is of one of the two kinds.
 (3c) Types. Which objects exist is read off from the layout: on e1 the slots k = 1, …, K+1 at the indices 6k, 6k+1,
 on e2 the 6-slots κ = 0, …, K at 10κ+6, …, 10κ+11 from V_c — by m ≥ 5K + 40 all of them at index ≤ 2m−42, more than 60
 from V_b —; on e3 the sequence of boundaries between consecutive dimers D_i | D_{i+1}, each of one of the types *b*
 (PPP between the b-sites, over the small face; i even), *a* (PPP between the a-sites, over the big face; i odd),
 *cut* (two caps; i odd), and the three boundaries *L, s, R* of a separator (cap and tether cap; PPP; tether cap and
 cap); on the nine other edges the ring PPP's with period two dimers; at the six vertices fixed objects. In terms of
 objects: on e3 there are four types, each attached to H-sites of e3 — Acap(p), p even: cap and second column site
 of the a-site e3[p], present when that site is a run end (both sides of a cut; the left side of L; the right side
 of R; the ends of the fillers); Tcap(p), p odd: the same for a b-site (the two outer H's of a separator);
 PPPa(p), p even: the PPP between the a-sites e3[p] and e3[p+2] (boundaries a and s); PPPb(p), p odd: the PPP between
 the b-sites e3[p] and e3[p+2]. The owner is e3[p], and |e3[p] − e3[p′]|_∞ = |p − p′|. A cap is attached to its H, a PPP to
 both of its H's. Every H of e3 has exactly one chain neighbour outside its dimer, or is a run end; so **at most
 one object is attached to each H of e3**.
 In a layout of 𝓕 two boundaries of e3 that are not of type a or b and do not belong to the same separator are
 at least four boundaries apart (items have at least 4 dimers), the first 13 boundaries from V_a and the last 14
 before V_c are of types a, b only (J ≥ 14, R ≥ 15).
 (4) *Every case occurs in two test layouts.* T_8 := (m = 80; K = 8; J = 14; C = 4; R = 15; one item per bin) and
 T_cut := (m = 80; K = 2; J = 14; C = 8; R = 43; two items of 4 dimers per bin) belong to 𝓕. Let ℓ ∈ 𝓕.
 *Single owners, (V1) and bulk run ends.* Vertex kind: the owner has the same position relative to its vertex as
 an owner of the same type in T_8. For V_a these are the slots with reference index 6k−1 ≤ 40 (k ≤ 6; T_8 has k ≤ 9),
 D_0, and the boundaries of e3 with owner index ≤ 25, i.e. up to D_12 | D_13, which are of types a, b in ℓ and in T_8;
 for V_c the slots with 10κ+5 ≤ 40 (κ ≤ 3) and the last 13 boundaries of e3, of types a, b in both; at V_b and at
 the other three vertices nothing depends on the layout. Edge kind: on e1 or e2 the owner is a slot with k ≥ 7
 resp. κ ≥ 4; its reference H has odd index, as have the slots k = 7, 8, 9 and κ = 4, …, 8 of T_8, which are of edge
 kind there. On e3 it is a boundary of one of the six types; T_8 contains boundaries of the types a, b, L, s, R and
 T_cut one of type cut, all of edge kind, and boundaries of equal type differ by an even number of dimers. Ring
 owners of edge kind occur in T_8 with both parities. By (3a), (3b) the object and its surroundings in ℓ are
 translates of those in the test layout.
 *Pairs, (V2).* Let o, o' be objects of ℓ whose owners u, u' are within the cutoffs of (2). (α) If one of the
 owners has index < 10 on its edge, or the owners lie on different edges, then both lie on edges from one vertex
 V, at index ≤ 31 (frame links), ≤ 24 (a frame link and another object: the other object), ≤ 17 (two other
 objects) — because e[i] is at max-norm distance ≥ i − 1 from e[0], and sites e[i], e'[j] of two edges with
 e[0] = e'[0] are at distance ≥ max(i, j) − 1. In T_8 the same owners carry the same types: slots of e1 with
 6k−1 ≤ 31 and of e2 with 10κ+5 ≤ 31, boundaries of e3 with owner index ≤ 24 (types a, b in both), ring and vertex
 objects; so the pair occurs at the same place in T_8. (β) Otherwise u, u' lie on one edge at indices ≥ 10, and by (3a) whether the two objects meet depends only on
 their types, on the parity of the owner index and on the difference of the owner indices.
 – Slots of e1 (reference indices 6 apart per slot, so at most 3 slots apart) or of e2 (at most 2 apart): all
   these pairs occur in T_8.
 – Ring edges: their objects are the PPP's of one periodic pattern, the same in every layout; every pair occurs
   in T_8.
 – Track e3: all 50 combinations of two types with a difference δ of the owner indices, 0 ≤ δ ≤ 6 (the cutoff of
   (2)), were computed [build3.py, NCHECK "track objects", at the owner indices 40, 42, 60: the same result]. Two
   objects meet only in the six combinations (Acap, PPPa, 0), (PPPa, Acap, 2), (PPPa, PPPa, 2), (PPPb, PPPb, 2), (PPPb, Tcap, 0),
   (PPPb, Tcap, 2); in each of them both objects are attached to one common H, which by (3c) never happens in a layout.
   **Hence two objects of e3 with owner indices ≥ 10 are disjoint in every layout — for all items and all cuts;
   no enumeration of boundary sequences is used.** [This replaces the enumeration "at most three boundaries apart"
   of the previous version, which was wrong (fourth audit): owners of consecutive boundaries are 1 or 3 apart,
   not 2; a cut has two cap owners; and two cuts four boundaries apart — items 4, 4, 4 — have cap owners e3[40], e3[46]
   at distance 6. That pair is the combination (Acap, Acap, 6) of the table.]
 (γ) Objects of T_8 that are absent in ℓ at that place impose no condition: ℓ has at most the slots of T_8 inside
 the vertex boxes (if K < 8, some slot sites of T_8 are ordinary frame sites of ℓ, which carry no object).
 (5) *Beyond skin 1.* Frame links and PPP's lie in skin 1, where a column has only its first two sites; caps are
 dangling sites, which lie on no other column (Lemma C(ii)); columns are pairwise disjoint (Lemma C); tethers avoid
 columns and each other by (N4).
 (6) *Machine part* [CHECKED, sweepN.sh, logs sweepN_nochain.log, audit4_tests.log; Appendix A]. T_8 and T_cut (and, as
 a further test, T_3 := (m = 80; K = 1; J = 14; C = 12; R = 49; items 4, 4, 4)) were built in the
 assembly of §6 — every path of the bulk cover is an H-run of its own, with a cap and a column at each of its
 two ends (the option "nochain" of build3.py; T_8 has 22,993 linker caps) — and (V1), (V2), (N1), (N2), (N3), "no
 near-field P on a linker column", the radius 3 of every PPP, and the explicit tethers of (N4) with their lengths
 were asserted, together with: the frame links found by the builder's search are exactly the lists of Appendix C
 and lie in skin 1; the anchors of all slots are translates of each other; the only borrowed columns are those
 of Appendix C. As a confirmation that is not needed for the proof the same was done for every K = 1, …, 8 at
 m = 80 and m = 82, for T_cut at m = 82, and for one layout with K > 8 (m = 92, K = 10, J = 14, C = 4, R = 15).
 [Corrected 14 November 2026: the runs of the previous version used the option "chain", which joins some bulk
 paths by additional PPP's and so tested a different assembly from the one of §6.] ∎
(What is proved by hand: (1)–(5), given Lemmas E, K, C, R and (N3), (N4). What is computed: the two test layouts.
What remains an assumption of this proof: that the builder build3.py implements the placement and the object
rules stated here — it was written by the author and has not been read by anyone else — and (N3) near the
vertices, which is part of the same runs.)

### 8.5 The far field

After §8.4 there remains, for every long linker, a pair of caps whose columns are free. Let W be the set of these
caps ("wires"); write w := |W|, so there are w/2 linkers. For c ∈ W: beyond skin 1 its column is an arm in an
open quadrant q_c, with constant α =: α_c and X ∈ {x_c, x_c + 1}. Take h_0 := H := 20m + 21. Part E below verifies
that this odd number exceeds ρ of every near-field P and every site of Oct(m), and exceeds max |α_c| + 8.
Put α* := max |α_c| + 6 (odd, like every α). If W is empty there is nothing to route.

**Lemma A (avenues).** Let q be an open quadrant, ℓ odd, α_0 odd, |α_0| + 4 ≤ ℓ. The set
 A(q, ℓ, α_0) := { v in q : ρ(v) ∈ {ℓ, ℓ+2}, α(v) ∈ {α_0, α_0+2} }
is a two-way infinite path that contains exactly one site with X = x for every integer x, consecutive sites having
consecutive X. Its sites with ρ = ℓ + 2 that are reached, in the direction of increasing X, by a rung occur once in
every four consecutive values of X.
Proof. A site of A has exactly one rung inside A (up if ρ = ℓ, down if ρ = ℓ+2) and exactly one step inside A; by
Lemma B(a) they change X by ε and −ε. So every site of A has exactly two neighbours in A, at X − 1 and X + 1, and A is a
union of two-way infinite paths, one for each site of A with X = x. For fixed x the four candidates have
(|Y|, |Z|) = (y_0, z_0), (y_0+1, z_0+1), (y_0+1, z_0−1), (y_0+2, z_0), where y_0 + z_0 = ℓ, y_0 − z_0 = α_0. The parity conditions
X ≡ Y ≡ Z + 1 (mod 2) select the first and last, or the two middle ones; these two differ by 2 in exactly one
coordinate, so exactly one of them satisfies the condition x + y + z ≡ 0 or 3 (mod 4). The four sites of a period
have (ρ, α) = (ℓ, α_0), (ℓ+2, α_0), (ℓ+2, α_0+2), (ℓ, α_0+2) in cyclic order, with a rung, a step, a rung, a step between
them. ∎ [CHECKED, faru.py]

**Lemma V (level curves).** Let u ≥ 3 be odd and Λ_u := {ρ = u}. Every site of Λ_u has exactly two neighbours in
Λ_u. On a walk along Λ_u without turning back, α is strictly monotone inside each open quadrant, X stays on two
consecutive integers there, the walk leaves a quadrant through a bend site into an adjacent quadrant, and the
pair of X-values shifts by one at each bend.
Proof. Inside a quadrant the neighbours in Λ_u are the two steps (α ± 2, ΔX = −ε, and ε alternates); when |α| = u − 2
the next site is a bend site, whose two neighbours in Λ_u lie on its two sides at X ∓ 1 (Lemma B(b)). ∎

**Lemma F (far field).** For every pairing of W into linkers there are pairwise disjoint paths outside Oct(m),
one for each linker, joining its two caps, each consisting of the two columns up to certain heights and of sites
with ρ ≥ h_0, and disjoint from all near-field P's. Length here counts P-sites, including both caps: caps on the
same sublattice require odd L, and caps on opposite sublattices require even L. For the near field of §8.4 one
may take **L* := 1000(m + |W| + 1) + 6**, independently of the packing. Every linker can simultaneously be assigned
any length L ≥ L* of its required parity.
Construction and proof.
*A. Levels.* Let x^(1) > x^(2) > … be the different values of x_c. Wire c gets the level ℓ_c := h_0 + 4r if x_c = x^(r+1).
Its column is used up to its site T_c with ρ = ℓ_c; from T_c the wire follows the avenue A_c := A(q_c, ℓ_c, α_c) in the
direction of increasing X.
 Columns do not meet (Lemma C). The avenue of c lies at ρ ≥ h_0, in X ≥ X(T_c) ≥ x_c, on the levels ℓ_c, ℓ_c + 2 and in the strip
 α ∈ {α_c, α_c+2} of q_c. Let c' ≠ c. If ℓ_{c'} < ℓ_c, the column of c' ends below ℓ_c and A_{c'} uses lower levels. If ℓ_{c'} > ℓ_c,
 then x_{c'} < x_c, so the column of c' lies in X ≤ x_c; the only site of the avenue of c with X ≤ x_c is T_c, which is on
 the column of c; and A_{c'} uses higher levels. If ℓ_{c'} = ℓ_c and q_{c'} = q_c, then x_{c'} = x_c. By the condition x+y+z ≡ 0 or
 3 (mod 4), the sites of one sublattice with a given X in a given open quadrant have ρ in one class mod 4 and, for
 given ρ, α in one class mod 4. So T_c, T_{c'} are sites of the same sublattice with the same X, and α_{c'} ≡ α_c (mod 4),
 α_{c'} ≠ α_c (an arm is determined by its quadrant, α and X-values); hence the strips of A_c and
 A_{c'} are disjoint, and the column of c' has no site on the levels ℓ_c, ℓ_c+2 except T_{c'}, which is outside the strip of
 c. Different quadrants are disjoint.
*B. Slabs.* Take X_F := H, larger than every X-value on the initial columns (Part E). Order W by decreasing level
(ties arbitrarily), and give the n-th wire, 1 ≤ n ≤ w, the slab value ξ_c := X_F + 60n.
Wire c follows A_c up to its first site E_c with X ≥ ξ_c and ρ = ℓ_c + 2 that
is reached by a rung; X(E_c) ≤ ξ_c + 3 (Lemma A). From E_c it continues up the arm through E_c ("radial arm") to its site
with ρ = U_i, where 1 ≤ i ≤ w/2 is the number of its linker and U_i := U_0 + 4i. Take U_0 := H + 4w + 8,
an odd number larger than all ℓ_c + 4 and than α* + 8 (Part E).
 The radial arm of c lies in X ∈ [ξ_c − 1, ξ_c + 4], in the strip of c, on levels ≥ ℓ_c + 2. It can only meet avenues of
 wires c' in the same quadrant with ℓ_{c'} ≥ ℓ_c and overlapping strip. If ℓ_{c'} > ℓ_c, then c' comes earlier in the order and
 its avenue ends at X ≤ ξ_{c'} + 3 < ξ_c − 1. If ℓ_{c'} = ℓ_c the strips are disjoint (A). Radial arms of different wires lie
 in disjoint ranges of X. The avenue of c beyond X_F meets no radial arm: an arm in a slab before ξ_c belongs to a
 wire of level ≥ ℓ_c and lies above the levels of A_c or in another strip.
*C. Joining.* Let a, b be the two wires of linker i, u := U_i, and t_a, t_b the tops of their radial arms (ρ = u). Let
A* := A((+,+), u, α*) and A** := A((+,+), u, α*+4). From t_a walk along Λ_u in the direction in which α increases
inside the quadrant (+,+), until the first site s_a of A*; it has α = α*. This walk H_a passes at most three bends,
so it stays in X ∈ [ξ_a − 5, ξ_a + 8] (Lemma V), and it contains no site with α > α* of the quadrant (+,+). Define H_b, s_b alike.
Join s_a to s_b along A*. The linker is: column of a, avenue, radial arm, H_a, the piece of A*, H_b reversed,
radial arm, avenue and column of b reversed.
 The levels u, u+2 are used by no other linker's joining piece and by no avenue of stage A/B. Radial arms of other wires pass
 these levels inside their own slabs and strips; H_a and H_b stay within 8 of ξ_a, ξ_b in X, hence miss the other
 slabs, and miss their own radial arms except at t_a, t_b (an arm has one site per level); A* and A** lie in strips
 α ≥ α* that no wire uses. H_a ∩ A* = {s_a}, H_b ∩ A* = {s_b}, and H_a ∩ H_b = ∅ since |ξ_a − ξ_b| ≥ 60.
*D. Padding in all four parity-compatible residue classes.* Let β be the number of P-sites of the linker from
Parts A–C. Exchange its ends if necessary, and put a := X(s_a) < b := X(s_b). By Part C,
b − a ≥ 60 − 13 = 47. Write A_x and B_x for the unique sites of A* and A**, respectively, with X-coordinate x.
Both s_a = A_a and s_b = A_b have (ρ, α) = (u, α*).

**Crossing pairs.** Whenever A_p has α = α* + 2 and ε = +1, its rung neighbour is A_{p+1}, which has the same α
and ε = −1. Lemma B gives the two cross-avenue bonds
 A_p ~ B_{p−1},    A_{p+1} ~ B_{p+2}.
Such pairs occur every four X-values. In each period the other two sites of A* have α = α*.
Choose the last such p < a. Since A_a has α = α*,
 **r := a − p ∈ {2,3}**, and p+1 < a < p+4.

**The long detour.** Choose δ ∈ {0,1} and d ≥ 0, and set
 v_0 := p + δ − 4d,    v_1 := p + δ + 4,    e := 1 − 2δ.
The two crossing sites A_{v_0}, A_{v_1} both have ε = e, so they are bonded to B_{v_0−e}, B_{v_1−e}.
Replace A_a … A_b by
 A_a … A_{v_0}, B_{v_0−e} … B_{v_1−e}, A_{v_1} … A_b,
where the first interval is traversed with decreasing X and the other two with increasing X.
The A-intervals are disjoint because v_0 < a < v_1 < b; the B-interval is disjoint from A* because their α-sets
are disjoint. All consecutive sites are bonded by Lemmas A and B. Relative to the original b−a bonds this adds
 **2 + 2(a − v_0) = 2 + 2(r − δ) + 8d** sites (equivalently, bonds).

**An optional four-site detour.** Put q := p+8. The rung A_q ~ A_{q+1} in the final A-interval can be replaced by
 A_q, B_{q−1}, B_q, B_{q+1}, B_{q+2}, A_{q+1}.
This is a five-bond path replacing one bond, so it adds exactly four sites. It fits before b, since
q+1 ≤ a+7 < b. Its B-sites have X ∈ [p+7,p+10], whereas the long detour's last B-site has X = p+3 if δ=0,
and X = p+6 if δ=1. Thus the two detours are disjoint. Let η ∈ {0,1} indicate whether this detour is used.

**Exact lengths.** The total increase is
 Δ = 2 + 2(r − δ) + 4η + 8d.
For (δ,η) = (1,0), (0,0), (1,1), (0,1), its four initial values are respectively
 **2r, 2r+2, 2r+4, 2r+6**.
They represent all four even residue classes modulo eight; increasing d adds any nonnegative multiple of eight.
Consequently every even Δ ≥ 2r is attained, and **every even Δ ≥ 6 is attained for both possible phases r**.
Explicitly, for a desired even Δ ≥ 6 write t := (Δ−2r)/2 = 4d+j, 0 ≤ j ≤ 3; choose δ=1 for even j and δ=0 for
odd j, and η=⌊j/2⌋. This gives exactly Δ, with d ≥ 0.

**Avoidance.** The padded path stays in A* ∪ A**, in the quadrant (+,+), on the private levels u,u+2 and in the
strips α ∈ {α*,α*+2,α*+4,α*+6}. The entire avenue A* meets H_a and H_b only at s_a and s_b (Part C), and A** meets
neither approach, because their (+,+) portions have α ≤ α*. Initial columns and lower avenues end below these
levels. Every radial arm lies in a wire strip with α ≤ max_c |α_c|+2 = α*−4, so even the arbitrarily long backward
extension misses all radial arms. Other linkers' joining and padding pieces use different pairs of levels.
All these levels exceed h_0, hence miss the near field and Oct(m). Together with the explicit interval
separation above, this proves self-avoidance and simultaneous disjointness for arbitrary prescribed increases.

*E. A uniform bound independent of the packing.* The constants of §6 imply K ≤ m. Every near-field site of §8.4
lies in O_{2K+3}: entry tethers use skins at most K+2, exit tethers at most 2K+3, and the remaining finite pieces
lie in skin 1. For v ∈ O_j, the face inequalities give
 |X| + |Y| + |z| ≤ 2(m+2j)−1,    ρ = |Y|+|z−1| ≤ 2m+4j.
Thus near-field ρ ≤ 2m+8K+12 ≤ 10m+12 < H. The first two sites of an ordinary column, and the initial sites of
a borrowed column, lie in O_1. Hence |α_c| ≤ 2m+4 and all X-values of these arms have |X| ≤ 2m+4 < H.
This verifies the choices h_0=X_F=H and α* ≤ 2m+10. Since ℓ_c ≤ H+4(w−1), the choice U_0=H+4w+8 is valid, and
 U_i ≤ U_max := H+6w+8.

For one wire, its column portion and its radial arm together use at most U_max+2 bonds (their ρ-increases
telescope; the borrowed-column entry costs at most one extra bond). Its avenue uses at most 2H+60w+3 bonds.
Its level-curve approach uses at most 4U_max+4 bonds: there are at most four quadrant portions, each of length
at most u+1 by Lemma V. The middle avenue segment uses at most 60w+13 bonds. Including the initial cap, the
un-padded linker therefore has
 β ≤ 2[(U_max+2)+(2H+60w+3)+(4U_max+4)] + (60w+13) + 1
   = 4H+10U_max+180w+32 = 280m+240w+406 < 1000(m+w+1).
The integer w is twice the number of long linkers in the word and is fixed before choosing a packing.
For L ≥ L* := 1000(m+w+1)+6 with the required cap parity, L−β is even and at least 6; Part D supplies exactly
that increase. All choices and the construction take polynomial time for the polynomial lengths used in §9.
The formulas for H, U_0, and L* depend only on m and w, not on the packing or the positions of its item ends. ∎

[INDEPENDENT CHECK, 14 November 2026: `../research/tetrahedral/check_padding.mjs`, Node.js, standard library only.
87,880 padded paths in 1,352 endpoint/avenue geometries, covering both phases r, every even increase 6…134, and
all four choices of (δ,η), passed exact coordinate checks for lattice membership, adjacency, self-avoidance,
length, private levels/strips, and avoidance of level-curve approaches from all four quadrants.
These finite checks support the hand proof above; they do not audit Parts A–C or the Bulk/N certificates.]

[AUTHOR'S RE-CHECK of Parts D–E, 14 November 2026; own scripts, Python 3, in HP_tetrahedral_code.tar.gz.
(i) `faru2.py` reproduces the defect for a fixed start site: the original construction gives increases in a single
class modulo 8 (0 or 6). (ii) `faru3.py`: Part D re-implemented from the text above, raw coordinates, one fixed
start site per case, minimal gap b − a = 47: 28,512 padded paths, both phases r, every even increase 6…400; each
is a simple lattice path inside A* ∪ A** of exactly the stated length, and the four choices (δ,η) give the four
classes modulo 8. (iii) `build3.py`, far-field mode `text`: Parts A–E executed literally (h_0 = X_F = H = 20m+21,
slabs X_F + 60n, U_0 = H + 4w + 8) inside complete folds, with an assertion for every inequality asserted in
Parts B, C and E — near-field ρ ≤ 2m+8K+12, |α_c| ≤ 2m+4 and |X| ≤ 2m+4 on the columns, radial arms in
[ξ_c − 1, ξ_c + 4], at most three bends and X ∈ [ξ − 5, ξ + 8] on the level-curve approaches, the four piece
bounds, β ≤ 280m+240w+406 — and with pairwise disjointness of all linkers from each other, from Oct(m) and from
the near field. Runs: m = 24 (w = 112) with every linker of length L* or L*+1 (137,006 / 137,007; 7,693,861
monomers); m = 24 and m = 25 with increases 6, 8, …, 36 (all eight combinations of r, δ, η occur); m = 28, K = 2
with all lengths 280m+240w+412 (+1 by parity): three packings of items 2,2,2,2 and two packings of items 2,2,4
give the same string (2,888,336 resp. 2,814,326 letters) and different folds. Every fold passed verify_fold.py
with 2N − 2m² contacts. These runs use the small ad hoc track constants of the earlier tests; they test Parts A–E
as written on small instances, they are not a proof, and they say nothing new about the Bulk Lemma or Lemma N.
An alternative padding (g_1 the first crossing site of either sign beyond s_a; increase
2 + 2(a − v_0) + ε(v_0) − ε(v_1), every even value ≥ 4) is recorded in the working notes, §14; it is not needed.]
[CHECKED: this construction, without step D, is the "ordered" mode of build3.py; run in full on an instance in
which every bulk run is linked separately: m = 20, 1006 wires, 8 951 691 monomers, verified by the independent
 checker. These are reports from the original manuscript; they do not validate the replacement Parts D–E.
 The original `faru.py` padding claim is superseded; a simpler padding was used in the test with three packings.]

### 8.6 The fold

Given a packing, place the H's as in §8.4 and the P's as in §8.4 and §8.5, where the prescribed length of each long
linker is the one written in the word. The letters of the word then occupy pairwise different sites: the H's by
the placement; caps are dangling sites of different run ends; a PPP is determined by its two ends and two PPP's
with different ends have different middle sites; frame links, tethers and columns by Lemma N; the far parts
of the linkers by Lemma F. Consecutive letters are on adjacent sites. The H's occupy exactly Oct(m), so the fold has
e(Oct(m)) = 2N_m − 2m² contacts (5.1).

## 9. Proof of the Theorem

The problem is in NP: a fold is a list of sites. Reduce from bin packing with numbers in unary, which is strongly
NP-complete: K bins of capacity B and items s_1, …, s_n with Σ s_i = KB. Build the word of §6 (with m even and ≥ 80,
which the constants of §6 guarantee) and put k := 2N_m − 2m². The word is computed in polynomial time: the cover of
§8.3 by its local rules, the frame links as the lists of Appendix C, the tether lengths by the formulas of (N4) (the
rows of Lemma N), and each full long P-run has length L* := 1000(m+w+1)+6 from Lemma F(E), plus one where the cap
parity requires it. Here w is twice the number of long linkers; their cap parities are determined by the fixed
run orientations and the item-end sublattices in §8.4. None of this depends on a packing. (Reason: a cap is
the dangling neighbour of the end H of its run. The ends of all units other than items are fixed sites. Both ends of
an item are a-sites of the track; consecutive a-sites of the track differ by the lattice translation (2,0,2), which
preserves the sublattices; so the two caps of an item lie on one fixed sublattice wherever the item is placed.
[CHECKED by assertions in build3.py; and by the identical strings for different packings reported in §8.5.]) Lemma F(D) realizes
every resulting prescribed length, because its difference from the base route's length is even and at least 6.
If the word has a fold with at least k contacts, it has one with exactly k (Corollary 4) and then a packing exists
(§7). If a packing exists, §8.6 gives a fold with k contacts. ∎

## Appendix A. Machine checks

The original manuscript places its scripts in HP_tetrahedral_code.tar.gz (Python 3, no packages); that archive
has not been supplied in this project, so its checks below remain author-reported. Its "independent checker"
is verify_fold.py, which reads coordinates and letters without using the construction. The new padding checker
is supplied separately at `../research/tetrahedral/check_padding.mjs` and was run for this revision.

| What | Script | Range |
|---|---|---|
| Lemma 5.1 (⋆) and its equality cases | tight2.py, star_route.py | a < 260 (all t, ℓ); a < 3000 (route) |
| Lemmas 5.2–5.4 | lastparts.py, onesided2.py | x ≤ 110 with counting; x ≤ 450 |
| Claim U | pdp.cpp | m ≤ 14: maximum N_m, one optimal composition |
| Theorem 5 for m = 2 | brute10.py | all 381 250 connected 10-site clusters |
| 5.1, 5.6: description of Oct(m), (O1)–(O3) | tetcoords.py, halfspace.py | m = 3 … 14 |
| (O4) link table | adv.py | m = 8, 11 (k ≤ 11), m = 16 (k ≤ 10), all pairs of surface sites |
| (O7) | coordfacts.py | m = 6 … 20 |
| Region transfers | regiontransfer.py | D = 3, m = 17, 18 |
| Bulk Lemma: cover valid | canon.py | every m = 9 … 60 and 64, 68, …, 100 |
| Bulk Lemma: Ω-certificate, table, structure | certify.py, bulktable.py, lines.py, extents.py | m = 9 … 100; 14 … 44; 24, 31, 40, 53 |
| Columns disjoint, links vs columns | arms.py | m = 20 |
| Lemma N, base cases | sweepK.sh (build3.py) | m = 80, 82; K = 1 … 6 |
| Lemma N, induction steps | nfinduct.py, slotsig.py | (82,6) vs (80,6); (80,7) vs (80,6) |
| Lemma A; superseded original padding | faru.py (author-reported) | four quadrants, several levels and strips; does not establish the replacement padding |
| Lemma F(D), replacement padding | `../research/tetrahedral/check_padding.mjs` (independently run) | 87,880 paths; 1,352 geometries; every even increase 6…134; both phases and all four residue classes |
| Original padding: defect reproduced | faru2.py (author) | fixed start site, 32 cases: old construction reaches one class mod 8 |
| Lemma F(D), replacement padding, re-check | faru3.py (author) | 28,512 paths, both phases, every even increase 6…400, gap b − a = 47 |
| Lemma F, Parts A–E executed literally in complete folds | build3.py mode `text` + verify_fold.py (author) | m = 24 with L*, L*+1 (7,693,861 monomers); m = 24, 25 all residues; m = 28, K = 2: 3 + 2 packings, identical strings; every asserted inequality of Parts B, C, E checked |
| Lemma T: counterexample; Lemma T′: coverage and transfer | transfer_cov.py (author) | (D,R,M) = (2,0,18), (2,5,20), (3,0,21), (3,7,23), (4,0,24), both centre parities |
| Bulk Lemma, Claim 1, base cases for Lemma T′ | claim1.py 88 89 (author) | valid covers, shortest path 6 sites |
| Bulk Lemma, Claim 2 with the lexicographic Ω | certify_lex.py cert 9 60 (author) | every m = 9 … 60: no ties, ten strict local maxima (the same for m ≥ 14), each certified within 6 steps |
| Witness against the numerical Ω | certify_lex.py witness 30 47 (author) | P, Q, R at the −y vertex as reported; numerical potential fails from m = 50 004 on |
| Lemma K / Lemma E, confirmation | edgeperiod.py 40 41 50 (author) | cover 2-periodic along all twelve edges for 12 ≤ i ≤ 2m−16 |
| Lemma N: test layouts T_8, T_cut and confirmations | sweepN.sh = build3.py with NCHECK (author) | m = 80, 82; K = 1 … 8 with J = 14, C = 4, one item per bin; T_cut; Appendix C asserted; 18 runs |
| Tethers (N4), explicit routes, actual sizes | tether_local.py (author; independent of the builder) | (K,B) = (1,1) … (12,1), m = 336 … 50 034, and the test layouts; reproduces the audit's coordinates for m = 336 |
| Lemma N test layouts, unchained assembly of §6, explicit tethers, PPP radius | sweepN.sh → sweepN_nochain.log (author) | T_8, T_cut; K = 1 … 8 at m = 80, 82; m = 92, K = 10 |
| Same word for different packings, unchained assembly (word only, run-length encoded) | build3.py … nochain … word (author) | m = 28: items 2,2,2,2 in 3 packings, items 2,2,4 in 2 packings; m = 92, K = 10 in 2 assignments (audit3_words_folds.log) |
| Complete folds with the explicit tethers (chained bulk paths, far field of §8.5 literally) | build3.py … text:resid / text:bound + verify_fold.py (author) | m = 24; m = 28 in 3 packings: one string, three folds (audit3_words_folds.log) |
| Claim 1, remaining sizes | claim1.py 61 … 87 → claim1_61_87.log (author) | 20 sizes, all valid |
| Bulk table per size | bulktable2.py 14 60 → bulktable2_14_60.log (author) | 39 entries for each parity of m from 18/19 on; union 74; A′, B′, C′ hold |
| Structure of far two-joint segments (classes X, Z); tables at 79, 80 | segstruct.py 40 41 59 60 79 80; bulktable2.py 18 19 79 80 (author) | class X: \|X\| ≤ 4, complete pieces, no row; class Z: rows, α > 0, ≤ 2 sites; none mixed |
| Lemma N, pairs on the track: all type/offset combinations; test layout T_3; packing-free word | build3.py NCHECK "track objects"; `… "[4,8,8,4];none" … word` vs three packings (audit4_tests.log) | 50 combinations, 6 meet (common H); T_8, T_cut, T_3 pass; run-length encoded words byte-identical |
| Whole construction, small constants | sweep3.sh (build3.py) + independent checker | 55 instances, m = 24 … 46, K ≤ 3; m = 80, K = 4 |
| One word, three packings | build3.py (modes natural / pad) + independent checker | m = 40, items 2,4,6,2,2,2: one word of 155 900 letters, three folds, 167 440 contacts each |
| Far field in the dense case | build3.py … nochain … ordered + independent checker | m = 20, 8 951 691 monomers |

The end-to-end runs use the construction of §8 with small values of J, R, C; with the constants of §6 the word is
too long to be built here (m is in the hundreds).

## Appendix B. The six vertex patches of the bulk cover

Bonds are given by their two end sites, in coordinates relative to the vertex (the vertices are c ± (2m−2)e_i).

* Vertex −x. Add: (3,-1,1)–(4,0,0), (4,2,-2)–(5,1,-3), (5,-1,-1)–(6,0,-2). Remove: (4,0,0)–(5,-1,-1), (5,1,-3)–(6,0,-2).
* Vertex −y. Add: (-5,7,-3)–(-4,6,-2), (-4,8,4)–(-3,7,3), (-3,5,-3)–(-2,4,-2), (-2,8,2)–(-1,7,1), (-1,3,1)–(0,4,0), (0,6,2)–(1,5,1), (1,3,-1)–(2,4,-2), (3,5,-1)–(4,6,-2). Remove: (-4,6,-2)–(-3,5,-3), (-3,7,3)–(-2,8,2), (-1,7,1)–(0,6,2), (0,4,0)–(1,5,1), (2,4,-2)–(3,5,-1).
* Vertex −z. Add: (-4,2,6)–(-3,3,7), (-2,2,4)–(-1,1,3), (-2,4,6)–(-1,3,5), (2,2,4)–(3,3,5), (4,2,6)–(5,3,7). Remove: (-3,3,7)–(-2,4,6), (-2,2,4)–(-1,3,5), (3,3,5)–(4,2,6).
* Vertex +z. Add: (-4,-2,-6)–(-3,-3,-7), (-2,-4,-6)–(-1,-3,-5), (-2,-2,-4)–(-1,-1,-3), (2,-2,-4)–(3,-3,-5), (4,-2,-6)–(5,-3,-7). Remove: (-3,-3,-7)–(-2,-4,-6), (-2,-2,-4)–(-1,-3,-5), (3,-3,-5)–(4,-2,-6).
* Vertex +y. Add: (-5,-7,3)–(-4,-6,2), (-4,-6,-2)–(-3,-5,-1), (-3,-5,3)–(-2,-4,2), (-2,-6,0)–(-1,-5,1), (0,-4,0)–(1,-3,1), (1,-5,3)–(2,-6,4), (1,-3,1)–(2,-4,2), (3,-7,3)–(4,-8,4). Remove: (-4,-6,2)–(-3,-5,3), (-3,-5,-1)–(-2,-6,0), (-1,-5,1)–(0,-4,0), (2,-6,4)–(3,-7,3).
* Vertex +x. Add: (-6,0,-2)–(-5,1,-1), (-5,-1,-3)–(-4,-2,-2), (-4,0,0)–(-3,1,1). Remove: (-6,0,-2)–(-5,-1,-3), (-5,1,-1)–(-4,0,0).

## Appendix C. The frame links and the anchors of the 2-slots (explicit)

Absolute coordinates: c = (0, 2m−2, 0), V_a = c − (2m−2)e_z, V_b = c + (2m−2)e_y, V_c = c + (2m−2)e_x. Each list gives the
P-sites of a link in order, as vectors to be added to the reference site.
- Λ_a, from V_a to e1[3]; reference V_a: (−1,1,−1), (0,2,−2), (1,3,−1), (0,4,0), (1,5,1), (2,4,2).
- Λ_2, over the 2-slot k (k = 1, …, K+1), from e1[6k−1] to e1[6k+2] = e1[6k−1] + (−1,3,3); reference e1[6k−1]:
  (1,1,−1), (0,2,−2), (−1,3,−1), (0,4,0), (−1,5,1), (−2,4,2).
- At V_b; reference V_b: from e1[2m−4] to V_b: (−1,−1,−3), (−2,0,−2), (−1,1,−1); from V_b to e2[2]: (1,1,1), (2,0,2), (3,−1,1).
- Λ_6, over the 6-slot κ (κ = 0, …, K); reference the frame site w of e2 with index 10κ+5 from V_c; listed from the
  V_b side to w: (−6,8,2), (−5,9,1), (−4,8,0), (−3,7,1), (−2,6,0), (−1,5,1), (0,4,0), (1,3,1), (2,2,0), (1,1,−1).
- At V_c; reference V_c: from the last frame site to V_c: (−1,3,1), (0,2,2), (1,1,1).
- Anchor on the 2-slot k; reference its a-site a = e1[6k] (the b-site is a + (1,1,1)): linker cap a + (−1,1,−1) with
  second column site a + (−2,0,−2); tether cap a + (2,2,0) with second column site a + (3,3,1). The tether cap's
  borrowed column is the column of the second-row site (m−3−3k, 3k, 1) of F' (coordinates of §8.2).
- Borrowed columns. All caps use their own arm, with these exceptions: the two caps of every 2-slot anchor (previous
  item), and the cap of e1[2] = V_a + (0,2,2) (first cap of the left filler), which is V_a + (−1,3,1) with second column
  site V_a + (−2,4,2). The caps of the 6-slot anchors use their own arms.
[CHECKED: asserted in every run of sweepN.sh (K = 1, …, 8; m = 80, 82); all sites of the links lie in skin 1.]

## Appendix D. Change ledger (audits of 14 November 2026)

F = failed statement (false as written); I = incomplete argument; C = change of convention (no mathematical change).

| # | Where | Kind | What was wrong | Repair | Justified by |
| --- | --- | --- | --- | --- | --- |
| 1 | §8.5 Lemma F(D) | F | padding reached one class mod 8 | crossing pairs + hexagon, all even increases ≥ 6 (first audit) | hand proof; faru3.py; build3 `text` |
| 2 | §8.3 Ω | F | fixed constants 10⁴, 10⁹ fail from m = 50 004 | lexicographic Ω; (i)–(iv) | hand proof; certify_lex.py |
| 3 | §8.4 Lemma N | I | bases/induction did not cover §6 | family 𝓕, explicit links, reduction to test layouts | (1)–(6); sweepN.sh |
| 4 | §5.6 Lemma T | F | hypothesis too weak (m = 11) | m ≥ R + R′ + 5; unused; Lemma T′, E | hand proof; transfer_cov.py |
| 5 | §6, (N4) tethers | F | word had 273 P's where the stated rows need 279 | explicit routes, σ_e = 10k+2, σ_x = 14K+22−6k | count in (N4); tether_local.py |
| 6 | Lemma N (2) | F | PPP radius 2 | radius 3, cutoffs 20/13/6 | assertion in build3.py |
| 7 | Lemma N tests | I | tests used chained bulk paths | unchained assembly | sweepN_nochain.log |
| 8 | §8.3 (a) | F + I | "74 entries for every m"; coverage for all m unproved | 39 per parity; Proposition A | hand proof (A1)–(A5); bulktable2.py; segstruct.py |
| 9 | §8.3 Claim 1 | I | sizes 61–87 partly unchecked | all checked | claim1_61_87.log |
| 10 | §4 Cor. 4 | F | intermediate bound false | (4/3)m(m²−½) | one line |
| 11 | Lemma N (3c), (β) | F | owners of boundaries d apart are 2d apart; pairs "at most three boundaries apart" | object types Acap, Tcap, PPPa, PPPb; table of all 50 type/offset combinations | (3a) + NCHECK "track objects"; "one object per H" |
| 12 | Lemma N (2) | F | "owners are zigzag sites or vertices" although bulk caps are objects | bulk caps separated, (1′) | Lemma C, (N3), (N4), surroundings clause |
| 13 | Prop. A (A5) | F | "|Y| ≥ 12 on P" (false: Y = −11 at m = 336) | α-part of the key argued case by case, no bound needed | text of (A5) |
| 14 | §6 unit order, final P, L* | C | text and builder used different conventions | §6 = what build3.py writes; one L* | build3 `word` with "ITEMS;none" vs packings: identical run-length encoding |
| 15 | §8.4, §9 wording | C | leftover "shortest paths", "bounded search" | removed | — |

**Obligations that remain open** (nothing below is claimed as done):
1. Agreement of code and text is asserted where an assertion was practical (Appendix C lists, tether routes and
   lengths, PPP radius, borrowed columns, "track objects" table) and is otherwise an assumption — in particular
   the placement of the H-runs (frame, slots, track, rings) and the rules of the cover in canon.py.
2. No complete fold exists for an actual reduction instance (m ≥ 336); for those sizes there are only the local
   coordinate checks (tether_local.py and the auditors' own samples) and the proofs.
3. The direct validation of the bulk cover stops at m = 100; beyond that it rests on Claim 1 (Lemma T′) and
   Claim 2 (Proposition A), both proved by hand from finite tables.
4. Sections 6, 7, 8.1, 8.2 and Lemma F (A–C) have not been examined by the audits so far, as far as the author knows.
5. (N3) near the vertices and (V1) for vertex-kind owners are certified only by the test layouts together with
   Lemma E(a); the six vertex neighbourhoods were not analysed by hand.
