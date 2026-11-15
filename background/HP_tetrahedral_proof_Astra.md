# HP folding on the tetrahedral lattice: Astra repair manuscript

Proof document, assembled from the working notes HP_tetrahedral_notes.md (which keep the history, the superseded
designs and more detail on the experiments). Method: that of Berger and Leighton for the cubic lattice ("Protein
folding in the hydrophobic-hydrophilic (HP) model is NP-complete", RECOMB 1998), with a new extremal lemma and new
gadgets, because their cube lemma and their surface gadgets do not exist on this lattice.

## 1. Result and status

**Target theorem — not established by this revision.** The following problem is NP-complete. Given a word s ∈ {H,P}* and an integer k: is there a self-avoiding
walk on the tetrahedral lattice, carrying the letters of s in order, with at least k pairs of H's on adjacent
sites? (Pairs that are consecutive in s are counted; leaving them out changes k by a constant of s.)

**Astra revision, 14 November 2026.** This is a separate repair attempt, not a machine-checked formalization.
The earlier hand arguments in §§2–7 and the repaired far-field padding are retained. The following changes
address the three subsequent audit findings:

* Lemma T_A has strengthened hypotheses and a complete proof, including the correct backward local-transfer corollary.
* The fixed-offset bulk potential is replaced by a lexicographic rank. Its ordering is size-independent, and the
  previously found large-size counterexample is eliminated. A no-cycle conclusion still needs the universal
  segment-classification obligation B below; the rank alone does not prove that classification.
* The unsupported near-field induction is removed. Explicit frame templates, selected borrowed columns, and
  exact tether routes replace the unspecified choices. The entry tether slack is changed to 10k, still within
  the bound used in the converse reduction. Universal compatibility obligation N remains to be proved.

**Completion verdict: not yet a complete proof.** The outstanding issues are mathematical coverage obligations
B (§8.3) and N (§8.4), not merely a lack of peer review or Lean formalization. Finite checks supplied with this
revision verify concrete constructions and certificates, but do not prove those two universal statements.
Section 9 is consequently stated conditionally. Author-reported checks from the original manuscript remain
identified separately in Appendix A. The independent results of this revision are recorded in Appendix C.

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
(If C ≤ 2m²−1: |S| ≤ (4/3)(m²−½)^{3/2} ≤ (4/3)m³ − m + 1/(8m) < N_m.)
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

**Lemma T_A (corrected backward transfer).** Put Y=y−(2m−2), Z=z−1, and let d_j=2m−2−f_j and
d'_j=2m−1+f_j be the eight face depths. Let R,R' be nonnegative integers and suppose
 **4m ≥ max(4R+20, 2R+4R'+22).**
For v ∈ D with all depths at least −R, make x eligible unconditionally, y eligible if |Y|≥R'+2, and z eligible
if |Z|≥R'+2. Among eligible axes choose one maximizing the absolute coordinate of v−c=(x,Y,z); let e point along
that axis with the sign of that coordinate, choosing either sign when it is zero. Then
 τ(w)=w−2e−(0,2,0)
is a lattice translation from the size-m coordinate system to the size-(m−1) system. Each depth is unchanged
or decreases by four, and only depths initially at least R+5 decrease. The Y and Z coordinates are either
unchanged or do not cross zero and retain absolute value at least R'.

Proof. The translation vector has even coordinates and coordinate sum divisible by four, so preserves D.
The centre changes by −(0,2,0); relative to the centre the translation is −2e. Thus the depth changes are
exactly zero or −4, as in the original calculation. For each decreasing depth,
 depth ≥ 2m−2+|c_e|−|c'|−|c''|.
The depth hypotheses also imply |x|+|Y|+|z|≤2m−1+R. If all axes are eligible, the maximizing property gives
 |c'|+|c''|−|c_e| ≤ (2m−1+R)/3,
so the decreasing depth is at least (4m−5−R)/3 ≥ R+5 by 4m≥4R+20.
Otherwise an ineligible y-coordinate has absolute value less than R'+2, and an ineligible z-coordinate has
|z|≤|Z|+1<R'+3. If another eligible axis exists, its absolute coordinate is at most |c_e|; if neither other
axis is eligible, both are bounded as above. In either case
 |c'|+|c''|−|c_e| ≤ 2R'+4.
The decreasing depth is therefore at least 2m−2R'−6 ≥ R+5 by 4m≥2R+4R'+22.
An altered Y or Z has magnitude at least R'+2 before its change by two. For z, the eligible values Z≤−2 or
Z≥2 have the same sign as z=Z+1. Hence neither coordinate crosses zero, and its new magnitude is at least R'. ∎

**Local-pattern corollary.** Fix nonnegative integers r,q. Mark each D-site by its eight face depths whenever
they are 0 or 1, by membership in Oct(m), by the signs of Y,Z, and by their exact values when |Y|≤q or |Z|≤q.
For m_0≥2r+q+9, every marked radius-r ball with centre in Oct(m), m≥m_0, is a translate of such a ball at m_0.
Proof. Use R=2r+2 and R'=r+q+2. The sufficient bound is 4m≥8r+4q+34. Along r bonds a face depth changes by at
most 2r+1, so every altered depth stays at least 2 throughout the translated ball; all face marks and membership
are preserved. Altered Y,Z stay more than q away from zero throughout the ball, preserving their required marks.
Translation preserves lattice bonds and therefore entire radius-r balls. Apply T_A repeatedly from larger to
smaller sizes. The assertion covers precisely these local marks, not arbitrary gadget labels or global paths. ∎

The counterexample m=11,R=0,R'=10 fails the new bound (44<62). Independent finite checks exercised 79,465
permitted choices, including tied axes and both signs for zero coordinates; see Appendix C.

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
These individual forward identities do not by themselves prove that every ball at the larger size has a
preimage. Use the backward corollary of T_A for exactly the marks it covers, or prove the required inverse
coverage separately. In particular, frame slots, separator labels, and global bulk segments require their own
coverage arguments; local translation covariance alone is insufficient.

## 6. The word

Input: K bins of capacity B, items s_1 … s_n with Σ s_i = K·B (bin packing in unary, strongly NP-complete).
 Σ* := 18K + 40 (an upper bound for the tether slacks below), λ := Σ* + 8, C := λB; item i becomes a chain of λ·s_i
 dimers. J := C + Σ* + 8; j_k := J + (k−1)(C+2) for k = 1 … K+1; R := C + Σ* + 9; m := j_{K+1} + R + 3.
 (J, C, all j_k are even, R is odd, m is even.)
"Dimer chain of q dimers" = (HH PPP)^{q−1} HH. Units, in this order, joined by long P-linkers whose lengths are fixed
by the construction of §8.5 (Lemma F) and do not depend on the packing:

1. H — the first monomer of the chain.
2. Three times PHP.
3. Frame chain PHP · [e1] · PHP · [e2] · PHP: H-runs separated by links P^3, P^6, P^10 so that, laid along two
 edges, the links skip: on e1 (indices from V_a) {1,2}, the 2-slots {6k, 6k+1} (k = 1 … K+1) and {2m−3}; on e2
 (indices from V_c) {1}, the 6-slots {10k+6, …, 10k+11} (k = 0 … K) and {2m−3}. All frame runs have length ≥ 3.
 The link lengths add up to the maximal advance 2m−2 on each of the two parts.
4. For k = 1 … K+1 a separator group: HH · P^{2j_k+3+σ_e(k)} · HH PPP HH · P^{2(m−2−j_k)+3+σ_x(k)} · HH PPP HH PPP HH
 (entry anchor = 1 dimer, separator = 2 dimers, exit anchor = 3 dimers; the two long P-runs are the tethers).
 The Astra tether routes in §8.4 prescribe σ_e(k)=10k and σ_x(k)=14K+22−6k for every k. They are nonnegative even
 integers smaller than Σ*, depend only on k,K, and are computed directly. Shortest-path selection is unnecessary.
5. Items: dimer chains of λ·s_i dimers, in the order i = 1 … n.
6. Fillers: dimer chains of J, R, 3(m−2), 3(m−2), 3(m−2) dimers.
7. Bulk units: one run H^ℓ, ℓ ≥ 3, for each path of the cover of §8.3.

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
**Bulk Lemma target [universal certificate still required].** For every m ≥ 9 the set X_m is a disjoint union of lattice paths ("runs"), each
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

**Replacement rank.** Delete every non-foliation bond, calling it a joint. A remaining component is a segment
P of a foliation line, with constant odd α(P). Put X̂(P)=min_{v∈P} X(v)+max_{v∈P} X(v). A segment is a row segment
if it contains one of the originally damaged ends with Z=0. Order the following triples lexicographically:

 Θ(P) = (2, |X̂(P)|, 0)             for a row segment;
 Θ(P) = (1, α(P), X̂(P))            for a non-row segment with α(P)>0;
 Θ(P) = (0, X̂(P), 0)               for a non-row segment with α(P)<0.

There is no α=0 case because Y and Z have opposite parity. Row priority is now explicit and cannot be overtaken
by increasing m. In the audit witness near −y, Q has first coordinate 2 and P first coordinate 1 for every m,
so Θ(Q)>Θ(P) for all sizes. This repairs the fixed-offset defect without a numerical cutoff.

**Rank comparison lemma.** Every foliation line has X-width at most two: each arm has width one and their
X-pairs differ by one at the bend. Therefore every segment has width at most two. If P and Q share a joint,
choose its endpoints v∈P,w∈Q. Then |X̂(P)−2X(v)|≤2, |X̂(Q)−2X(w)|≤2 and |X(v)−X(w)|=1, so
 |X̂(P)−X̂(Q)|≤6.
Over a walk of at most six joints the bound is 36. For two positive-α segments in such a walk, the comparison
of 10⁴α+X̂ agrees with the lexicographic comparison of (α,X̂): distinct odd α differ by at least two, which
dominates 36. A positive-α and a negative-α segment in such a walk are likewise ordered by positive before
negative, since 10⁴>36. Thus the only previously unsafe comparison was row versus non-row, now fixed by the
first coordinate of Θ. An alternative finite scalar is
 Ω_m(P)=10⁶(m+1)+|X̂(P)| for rows, 10⁴α(P)+X̂(P) for positive non-rows, and X̂(P) for negative non-rows.
Indeed |α|≤2m and |X̂|≤4m inside Oct(m), so every row scalar exceeds every non-row scalar. For the local
comparisons above this scalar and Θ give the same ordering. ∎

**Conditional no-cycle lemma.** Suppose the displayed construction gives every site degree one or two, every
degree-one site has a dangling bond, and no component has fewer than three sites. Suppose also that every
segment joined at both ends either has a joint-neighbour of larger Θ, or has a continuation of at most six
joints to an endpoint or a segment of larger Θ. Then the cover has no cycles.
Proof. A cycle consisting only of foliation bonds is impossible by Lemma L. Any other cycle has finitely many
segments; choose one of maximum Θ. The first alternative contradicts maximality. In the second, a continuation
cannot leave the cycle because cover degrees are at most two, so it reaches neither an endpoint nor a larger
rank, again a contradiction. ∎

**What has actually been checked.** The independent Astra bulk model implements the foliation, simultaneous
merge rule, and all Appendix B patches. For every m=9,…,40 and m=60 it verifies the degree/end/size conditions,
the second-row condition needed in N3, exactly ten local maxima of Θ, and an endpoint/larger-rank witness within
six joints for each maximum. The complete m=30 witnesses are supplied in astra_rank_results.json, including
the actual coordinates of every segment on each escape. The former counterexample is also checked locally
at m=50,034 and m=1,000,000 with the corrected rank.

**Outstanding universal obligation B.** Those finite checks do not prove the hypotheses of the conditional
no-cycle lemma for all m. One sufficient completion would establish all of the following:

1. A stated radius and a complete set of marked local templates cover the degree/end/size and N3 conditions.
   Vertex-patch labels must be included explicitly; T_A transfers only the marks stated in its corollary.
2. Every segment with a joint near a vertex or a Z-plane edge lies in an explicitly bounded checked template,
   including its needed continuation. The original claims of 30-site segments and radius-43 certificates
   require a proof of coverage, rather than inference from a few measured sizes.
3. Every remaining long segment belongs to a complete classification of whole foliation lines, with both
   endpoints transferred consistently. One must show that no new segment or joint type appears as m or |α|
   increases, including the transitions between short and long cases and between α signs.
4. The resulting vertex and long-line templates satisfy the conditional no-cycle lemma with Θ.

The original proposed 74-entry table and its finite-to-unbounded coverage have not been reconstructed and
proved exhaustively here. The corrected rank resolves the actual numerical counterexample, but asserting
that it alone completes the Bulk Lemma would introduce a new gap. Obligation B is retained explicitly.

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
* *Frame links* P^3, P^6, P^10: paths in skin 1 between the dangling sites of the two run ends (Lemma N).
* *Tethers:* the explicit column-and-row paths of N_A below, with the new exact slack formulas.
* *Columns.* A cap p that starts a long linker continues along its column, or, if the second site of that column
 is used by a frame link, along a *borrowed* column: the column of a dangling site p' whose second site is a
 neighbour of p, from that second site on.
Everything except the positions of the item chains is independent of the packing. For the item chains, both
possibilities at each place between two consecutive a-sites inside a bin (a PPP, or two caps with their columns)
are provided for in advance: nothing else uses those sites or columns.

**Near-field target N_A.** For the actual Section 6 parameter family, the following explicit construction is
intended to satisfy N1–N5. Its tether arithmetic is proved below. Its remaining universal local-compatibility
obligation N is stated at the end; the finite tests are not promoted to an unproved induction.

**Domain and separation.** Let K,B≥1, C=(18K+48)B, J=C+18K+48, R_fill=J+1, and
 m=(K+2)(18K+48)B+38K+100.
Thus m≥336, C≥18K+48, J≥36K+96, and j_{k+1}−j_k=C+2. These bounds separate the separator/item region from
the two strings of anchor slots. No whole configuration of size 80 or 82 is used as an induction base.

**Explicit frame templates.** Put r_0=2m−2, and use absolute coordinates
 e1(i)=(i mod 2, r_0+i, −r_0+i),
 e2(i)=(r_0−i, r_0+i, −[i odd]),
 e3(i)=(i, r_0+[i odd], −r_0+i).
Each row below lists, in order, the P-site offsets from its first H-site h. The last P-site is adjacent to the
specified second H-site. Reverse a row when traversing e2 in the word's opposite direction.

| Link | First and second H-sites | Ordered P-offsets from the first H |
|---|---|---|
| Start of e1 | e1(0), e1(3) | (−1,1,−1), (0,2,−2), (1,3,−1), (0,4,0), (1,5,1), (2,4,2) |
| e1 two-slot k | e1(6k−1), e1(6k+2) | (1,1,−1), (0,2,−2), (−1,3,−1), (0,4,0), (−1,5,1), (−2,4,2) |
| End of e1 | e1(r_0−2), e1(r_0) | (−1,1,−1), (−2,2,0), (−1,3,1) |
| Start of e2 | e2(0), e2(2) | (1,1,1), (0,2,2), (−1,3,1) |
| e2 six-slot κ | e2(10κ+5), e2(10κ+12) | (1,1,−1), (2,2,0), (1,3,1), (0,4,0), (−1,5,1), (−2,6,0), (−3,7,1), (−4,8,0), (−5,9,1), (−6,8,2) |
| End of e2 | e2(r_0−2), e2(r_0) | (1,1,1), (0,2,2), (−1,3,1) |

The table specifies actual paths, not a search for unspecified paths. Their consecutive bond vectors, endpoints,
and placement in skin 1 are checked by substitution in D and the face inequalities. Mutual frame-link separation
also follows from the displayed coordinate intervals: successive e1 slot paths have disjoint Y-intervals
[6k,6k+4] relative to the centre; successive e2 slot paths have disjoint intervals [10κ+6,10κ+14].
The start/end paths and paths on different edges are separated by the Section 6 bounds, except at the shared
frame vertex, where the two listed P-paths use different dangling sites. Compatibility with bulk ends and all
other P-sites is a separate obligation, not a consequence of these interval checks alone.

**Selected borrowed columns.** Ordinary cap columns are used except for the following specified caps. Here h
is the H-site, p its dangling site, h' the surface H-site whose unused column is borrowed, and w the second site
of that column. The entry is p~w, after which the route follows the column of h'.

| Cap | Borrowed source h' | Entry site w |
|---|---|---|
| h=e1(6k), the entry anchor's a-site | h+(−2,−2,0) | h+(−2,0,−2) |
| h=e1(6k+1), the entry anchor's b-site | h+(2,−2,0) | h+(2,0,−2) |
| h=e1(2), the left filler's first H | h+(−2,0,2) | h+(−2,2,0) |

These are distinct sources on second rows along an X-plane edge. The N3 second-row condition excludes bulk
run ends at these sources. The left-filler choice is essential: its other adjacent candidate, h+(−2,−2,0),
can have its column occupied by a ring PPP. That collision was found during the Astra reconstruction. The
table uses the other candidate and is included in the combined checks.

For definiteness, order each of the three ring boundary cycles by starting at its lexicographically least
b-site and choosing its lexicographically smaller cycle-neighbour as the next site. Pair consecutive sites
around the cycle and traverse the dimers alternately in their forward and reverse orders. This fixes the
otherwise unspecified ring endpoint choices. All these are explicit coordinate rules independent of a packing.

**Exact tether routes and lengths.** In the face coordinates of §8.2, the entry slot's b-site is
(a_0,b_0,0)=(m−2−3k,3k,0). Its selected borrowed source is (a_0,b_0−1,1). In skin j=k+1 the borrowed column reaches
the sub-surface site (a_0+j,b_0+j−1,2), adjacent to
 S=(a_0+j,b_0+j−1,1)
on the row c=1. Starting at the original cap, reaching that sub-surface site takes 2j−2 bonds, including the
borrowed-column entry. From S follow row c=1 with decreasing b to b=j−1, then row b=j−1 with increasing c to
 (m−2−j_k+j,j−1,j_k+1).
Step to the separator's sub-surface column site (m−2−j_k+j,j,j_k+1), and descend to its first b-site's cap.
The two column portions contribute 4j−4 bonds, the two connector bonds contribute 2, and the surface-row
portions contribute 6k+2j_k. Counting P-sites rather than bonds gives
 L_e=4j−4+2+6k+2j_k+1=2j_k+3+10k.
Thus σ_e(k)=10k for every k, with no shortest-path assertion.

The exit tether uses j=K+2+k and κ=K+1−k. Ascend from the separator's second b-site to
(m−3−j_k+j,j,j_k+2), step to (m−3−j_k+j,j−1,j_k+2), follow row b=j−1 to (j−1,j−1,m), and then row a=j−1 to
(j−1,5κ+3+j,m−4−5κ). Step to the exit anchor's column at (j,5κ+3+j,m−4−5κ), and descend to its cap.
The row portions have 2(m−2−j_k) and 2(5κ+4) bonds. Therefore
 L_x=(4j−4)+2+2(m−2−j_k)+2(5κ+4)+1
    =2(m−2−j_k)+3+(14K+22−6k).
Hence σ_x(k)=14K+22−6k. For 1≤k≤K+1, both slacks are nonnegative even integers smaller than Σ*=18K+40.
The converse argument in §7 uses only that bound, so this change to the entry slack preserves it.

**Conditional avoidance argument for the tethers.** Assume the first-skin compatibility facts described below,
including N3. The row margins in Lemma R(d) exclude ordinary cap columns from b=j−1 and a=j−1. In row c=1,
only columns based on c=0 or c=1 can occur. The c=1 bulk sites are excluded as run ends by N3; the c=0 entry
anchor columns with smaller k stop in lower skins, and those with larger k lie beyond the route's starting
b-coordinate. The borrowed b-anchor source has b=3k−1,c=1 and obeys the same ordering. Separator columns have
b=j, and the exit-anchor/corner columns have a=j, so the margin rows avoid them. Distinct tether horizontal
parts lie in distinct skins; the same inequalities exclude their intersections with the other tether columns.
The remaining P-paths lie in skin 1. Thus their compatibility with the entry/exit prefixes, together with the
specified free-column conditions, proves disjointness of the entire tether family. This is an all-K argument
conditional on the first-skin facts; it does not use the invalid m=80,82 induction.

**Outstanding universal obligation N (first-skin compatibility).** It remains to prove, for every admissible
parameter choice and every allowed item subdivision, that:

* the frame templates avoid all required dangling sites and the first two sites of every bulk-end column;
* the selected borrowed entries and tails are free of frame links, ring/anchor/track PPPs, and other cap tails;
* N3 holds everywhere, including vertex patches;
* a PPP or the alternative pair of item-end caps can be used at every permitted item boundary without creating
  a collision elsewhere. A cap's own entry prefix is, of course, excluded from the other-P avoidance condition.

A local-template proof could discharge this obligation, but must give an explicit complete classification
and a valid dependence radius. The original radius-five checks do not certify a radius-eleven rule, and the
new explicit paths do not by themselves prove compatibility with every possible bulk endpoint. Merely observing
the same template in several experiments is not a proof that no new interface type occurs.

**Independent checks supplied here.** The Astra checker constructs these fixed paths, all surface PPPs, chosen
borrowed entries, all tethers, singleton/vertex caps, and reserved non-bulk linker columns. It checks actual
site collisions and tests near-field sites against bulk-end columns by evaluating the local bulk rules. It
distinguishes the two columns at a vertex and the two radial arms meeting a bend site; neither may be conflated.
The combined checks pass for (K,B)=(1,1),(1,3),(2,2),(6,1),(6,3), including both one item per bin and unit-item
subdivision at (1,3). These are actual Section 6 sizes, including m=336,732,848,1576,4072. The largest test has
180,135 near-field P-sites. This is substantial evidence for the proposed repair, but obligation N remains
explicitly open until the universal template coverage is established.


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
[CHECKED: this construction, without step D, is the "ordered" mode of build3.py; run in full on an instance in
which every bulk run is linked separately: m = 20, 1006 wires, 8 951 691 monomers, verified by the independent
 checker. These are reports from the original manuscript; they do not validate the replacement Parts D–E.
 The original `faru.py` padding claim is superseded; a simpler padding was used in the test with three packings.]

### 8.6 The fold, conditional on obligations B and N

Assume the universal obligations B and N have been established. Given a packing, place the H's as in §8.4 and the P's as in §8.4 and §8.5, where the prescribed length of each long
linker is the one written in the word. The letters of the word then occupy pairwise different sites: the H's by
the placement; caps are dangling sites of different run ends; a PPP is determined by its two ends and two PPP's
with different ends have different middle sites; frame links, tethers and columns by Lemma N; the far parts
of the linkers by Lemma F. Consecutive letters are on adjacent sites. The H's occupy exactly Oct(m), so the fold has
e(Oct(m)) = 2N_m − 2m² contacts (5.1).

## 9. Conditional reduction; the unconditional theorem remains open here

This section proves the reduction conditional on the universal obligations B and N and the earlier lemmas.
Those two obligations are explicit unproved targets in this revision, not axioms silently added to the proof.

The problem is in NP: a fold is a list of sites. Reduce from bin packing with numbers in unary, which is strongly
NP-complete: K bins of capacity B and items s_1, …, s_n with Σ s_i = KB. Build the word of §6 (with m even and ≥ 80,
which the constants of §6 guarantee) and put k := 2N_m − 2m². Under obligations B and N the word is computed in
polynomial time: the cover of §8.3 by its local rules, the frame links by the fixed coordinate templates of N_A,
and the tether lengths by σ_e(k)=10k and σ_x(k)=14K+22−6k. Each full long P-run has length L* := 1000(m+w+1)+6
from Lemma F(E), plus one where the cap
parity requires it. Here w is twice the number of long linkers; their cap parities are determined by the fixed
run orientations and the item-end sublattices in §8.4. None of this depends on a packing. Lemma F(D) realizes
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

## Appendix C. Astra repairs, evidence, and remaining obligations

The new scripts use Node.js and its standard library. They are independent reconstructions from the displayed
coordinates and patches, not reruns of the unavailable original archive. Run them from the project root.

| Repair/check | Supplied artifact | What was established |
|---|---|---|
| Strengthened transfer | [astra_transfer_check.mjs](../research/tetrahedral/astra_transfer_check.mjs), [results](../research/tetrahedral/astra_transfer_results.json) | 79,465 permitted finite cases passed; the general proof is Lemma T_A |
| Lexicographic rank | [astra_rank_check.mjs](../research/tetrahedral/astra_rank_check.mjs), [certificates/results](../research/tetrahedral/astra_rank_results.json) | Full covers at m=9…40 and 60; ten maxima, each escaping within six joints; former witness repaired at m=50,034 and 1,000,000 |
| Frame templates and candidate borrows | [astra_near_field.mjs](../research/tetrahedral/astra_near_field.mjs) | The displayed paths match independently searched N1-compatible paths in the tested configurations |
| Combined near-field construction | [astra_surface_check.mjs](../research/tetrahedral/astra_surface_check.mjs), [results](../research/tetrahedral/astra_surface_results.json) | Six actual parameter/item-subdivision cases; explicit tethers and chosen borrow prefixes; P-site and column collision checks |
| Repaired far-field padding | [check_padding.mjs](../research/tetrahedral/check_padding.mjs) | Previously run: 87,880 local padding paths; the general proof remains F(D–E) |

The rank check directly verifies whole small covers; it does not infer their acyclicity from a possibly faulty
potential. Its saved witnesses allow inspection of the proposed certificate separately from the cover itself.
The surface checker exercises both a large item and multiple unit items in a bin; it does not enumerate every
packing. The column test treats a dangling site's selected radial arm as part of the data: the other arm through
a bend is not automatically that cap's column. This avoids a spurious conflict at an exit anchor.

**What remains necessary for a gap-free mathematical proof.** Supply the complete all-size bulk-segment
classification and its coverage proof (B), and the complete all-parameter near-field interface classification
and compatibility proof (N). These could be hand classifications or genuinely finite certificates accompanied
by proved reductions to the finite cases. More sample folds, larger numerical cutoffs, or the word "locality"
do not replace those arguments. Once B and N are established, Section 9 explains how they complete this route
to NP-completeness. Until then, this file must not be cited as a completed proof.

