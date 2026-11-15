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
**Nobody other than the author of these notes has checked any of this.** Until that has happened it should be read
as a complete proof manuscript with computer-assisted parts, not as an established theorem.

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

**Lemma T (transfer between sizes) — clean form.** Depths: d_j := 2m−2−f_j (below big face j), d'_j := 2m−1+f_j
(below small face j); Oct(m) = {all d_j, d'_j ≥ 0}; r bonds change each depth by at most 2r+1.
*Claim.* Let R, R' ≥ 0 and 4m ≥ 3R + 2R' + 24. For v ∈ D with all depths ≥ −R, choose among the axes {x} ∪ {y if |Y| ≥ R'+2}
∪ {z if |Z| ≥ R'+2} the one with the largest |coordinate| of v − c, and let e be the unit vector on that axis
pointing from c towards v (any sign if the coordinate is 0). Then τ(w) := w − 2e − (0,2,0) is a lattice translation,
and relative to Oct(m−1) the site τ(v) has the same depths as v relative to Oct(m), except that depths larger than
R + 4 may have decreased by 4; Y and Z (relative to the new centre) are unchanged, or keep their sign and stay ≥ R'.
Proof. The shift by −2e relative to the centre changes each f_j by −2 (for the two j with t_j·e = 1) or +2. In the
first case d_j is unchanged (2(m−1)−2−(f_j−2) = d_j) and d'_j drops by 4; in the second d'_j is unchanged and d_j
drops by 4. The four depths that drop belong to the faces s with s·e = −1, and for those
depth = bound(s) − s·(v−c) ≥ 2m−2 + |c_e| − |c'| − |c''| (c_e the coordinate on the chosen axis, c', c'' the other
two). If both other axes were eligible, |c'|+|c''|−|c_e| ≤ (|c_e|+|c'|+|c''|)/3 ≤ (2m−1+R)/3; otherwise it is
≤ 2R'+4. In both cases the depth is ≥ R + 5 under the assumption on m. ∎
*Use.* A statement about Oct(m) that only involves, for every site v, the pattern of sites within r bonds of v
(membership of Oct(m), which faces/edges/vertices are near, signs and small values of Y, Z) is true for all m ≥ m_0
once it is true for m_0, where 4m_0 ≥ 3(2r+2) + 2R' + 24. This is used for the Bulk Lemma (8.3) only; (O1)–(O7)
above do not need it.

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
 For m ≥ 3D + 8 every site of Oct(m) satisfies at least one hypothesis (near a vertex ±x, a Y- or Z-plane edge or
 a face with |X| large: T-x; near ±y: T-y; near ±z: T-z; near an X-plane edge or a single face: T-r or T-y/T-z).
 Hence: *a statement about D-balls of a construction given by local, translation-covariant rules holds for all
 m ≥ m_0 of one parity as soon as it holds for m_0* (and for both parities if checked for m_0 and m_0+1).

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
 The slacks σ_e(k), σ_x(k) are defined in §8.4 (Lemma N, (N4)): each tether is a shortest path inside an explicitly
 given set of sites. They are even, at most Σ*, depend only on k and K, and are computed in polynomial time; for
 K ≤ 6 they are σ_e(1) = 6, σ_e(k) = 10k − 2 (k ≥ 2) and σ_x(k) = 14K + 22 − 6k.
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

**Claim 1 (it is a cover by paths with good ends).** Every site of X_m gets one or two partners; sites with one
partner have a free bond; no component has fewer than 3 sites. These are statements about bounded neighbourhoods, so
by the region transfers of 5.6 they hold for all m once they hold for small m. [CHECKED directly for every m = 9 … 60 and 64, 68, …, 100.]

**Claim 2 (no cycles).** Every bond of the cover that is not a foliation bond joins sites with equal ρ, hence changes
α by ±2. Cut each component into *segments* of constant α. For a segment P let X̂ = min X + max X and
 Ω(P) = C + |X̂| if P contains a damaged end with Z = 0 ("row segment"), K·α + X̂ if α > 0 otherwise, X̂ if α < 0,
with K, C huge (K = 10⁴, C = 10⁹). Two joined segments never have equal Ω. A cycle would contain a segment that is
the maximum of Ω on the cycle, i.e. a segment joined at both ends to segments of smaller Ω.
 (a) *Away from the vertices this never happens.* For a segment joined at both ends, both joints farther than 12
 from every vertex, the way it is joined depends only on (kind, sign of Y or Z, X̂, α mod 4, and α itself if
 |α| ≤ 5): a table of 74 entries, the same for all m = 14 … 44 [CHECKED, bulktable.py]. In the table: a segment with
 α > 0 always has one neighbour with α+2 and one with α−2; a segment with α < 0 has its neighbours on opposite sides
 in X̂, or a neighbour with α > 0; a row segment has a row neighbour farther out. So one neighbour has larger Ω.
 (That this table is the same for every m is proved below, "Completion".)
 (b) *Near the vertices* there are exactly 10 segments that are local maxima of Ω, at the same positions relative
 to the vertices for every m. For each of them, following the path from it one meets, within 6 segments and without
 leaving the neighbourhood of the vertex, either an end of the path or a segment with larger Ω.
 [CHECKED for every m = 9 … 60 and 64, …, 100, certify.py]
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
 |α| ≤ 5 where a neighbour can lie in another family; all classes occur for m ≥ 14. This is the table of (a)
 [bulktable.py, m = 14 … 44: 74 entries, no clash]. Its content, which can also be read off by hand: the four
 X-plane edges have "d-lines" (ending just below an edge site) and "w-lines" (ending on the second row), the X-pair
 of a line shifts by +1 across a bend at Z = 0 and by −1 across a bend at Y = 0; therefore lines bending at Z = 0 are
 d at both ends or w at both ends and form ladders d(α) – w(α+2) – d(α+4) – … (α strictly monotone), while lines
 bending at Y = 0 form paths of at most five lines with strictly monotone X-values. [CHECKED lines.py: every long
 segment with two joints is of one of these two kinds, m = 24, 31, 40, 53.]
 With (S2)–(S4), parts (a) and (b) of Claim 2 hold for every m ≥ 45, and for 9 ≤ m ≤ 60 the cover was validated
 directly. ∎ (computer-assisted: the finite checks are those of certify.py, bulktable.py, lines.py, canon.py)

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
* *Tethers:* the shortest paths of Lemma N (N4).
* *Columns.* A cap p that starts a long linker continues along its column, or, if the second site of that column
 is used by a frame link, along a *borrowed* column: the column of a dangling site p' whose second site is a
 neighbour of p, from that second site on.
Everything except the positions of the item chains is independent of the packing. For the item chains, both
possibilities at each place between two consecutive a-sites inside a bin (a PPP, or two caps with their columns)
are provided for in advance: nothing else uses those sites or columns.

**Lemma N (near field) [computer-assisted].** For every even m ≥ 80, every K and every packing:
 (N1) the frame links exist inside skin 1 and avoid the dangling sites of the slot sites, of the corners and of
 e1[2], and the dangling sites and second column sites of all bulk run ends;
 (N2) every cap whose second column site is used by a frame link has a borrowed column whose sites are otherwise
 unused;
 (N3) no site of the second row of a face along an X-plane edge (E(1,2), E(2,1), E(3,4), E(4,3)) is a bulk run end;
 (N4) the 2(K+1) tethers exist, pairwise disjoint, disjoint from all other near-field P's and from all columns of
 linker caps, of lengths 2j_k + 3 + σ_e(k) and 2(m−2−j_k) + 3 + σ_x(k) with σ_e(k) ≤ 10k + 5 and σ_x(k) ≤ 18K + 15 (both < Σ*);
 (N5) no near-field P lies on the column of a linker cap, and the columns of different linker caps are disjoint.
Proof.
*(N4).* Entry tether k uses skin j := k+1, exit tether k uses skin j := K+2+k. Coordinates of §8.2. The b-site of the
2-slot k is the site (m−2−3k, 3k, 0) of F'; the first and second b-site of separator k are (m−2−j_k, 0, j_k) and
(m−3−j_k, 0, j_k+1); the b-site w_1 of the 6-slot κ is (0, 5κ+3, m−5−5κ).
Entry route: (1) from the cap of the slot's b-site up its column (own or borrowed) to its sub-surface site in
skin j, which has γ_3 = 1 (own) or is bonded to a surface site of the row c = 1 (borrowed); (2) along the row c = 1
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
lie in skin 1. Counting sites: two columns of 2(j−1) sites each and two sites per step of a row give at most
2j_k + 6k + 4(k+1) + 4 for the entry route and at most 2(m−2−j_k) + 2(5κ+3) + 4(K+2+k) + 4 for the exit route; the tethers of
the word are the shortest paths inside these rows and columns, so their slacks are at most 10k + 5 and 18K + 15.
[CHECKED for K ≤ 6, m = 80, 82: the shortest ones have σ_e(1) = 6, σ_e(k) = 10k − 2 for k ≥ 2, σ_x(k) = 14K + 22 − 6k.]
*(N3).* Along an X-plane edge the inner neighbour d of each edge site is a damaged end of §8.3 whose two other
neighbours on the surface are second-row sites; the clockwise rule joins d to one of them, always on the same
side, so away from the vertices every second-row site is claimed exactly once and is not an end. Near the
vertices: part of the checks below.
*(N1), (N2), (N5).* *Locality.* The cover of §8.3 near a site is determined by a ball of bounded radius. A PPP is
a unique path. A frame link is the first path, in a fixed order, among the paths of its length inside skin 1
from the dangling site of its first H to that of its second H that avoid the sites named in (N1); it depends on
what lies within 11 bonds. A borrowed column is chosen among the neighbours of the cap. All rules commute with
lattice translations. *(N5) from the rest:* frame links and PPP's lie in skin 1, where a column has only its
first two sites; caps are dangling sites, which lie on no other column (Lemma C(ii)); the middle site of a PPP lies on
the column of one of the three surface sites of its triangle, and on that of the third one only for a PPP along
an X-plane edge, where the third site is a second-row site (N3) or, next to a vertex, a zigzag site; tethers avoid
columns by (N4).
*Induction over m and K.* By the region transfers of 5.6 the ball of radius D around a site of Oct(m+2)° is a
translate of a ball of Oct(m); the cover, the frame (positions counted from V_a, V_b, V_c), the track pattern
(period 4 zigzag steps) and the rings are carried along. Passing from K to K+1 adds one 2-slot on e1, one 6-slot on
e2 and one separator, which are translates of the previous ones along the edge once they are away from the
vertices. Hence if (N1), (N2), (N5) hold for (m, K) with m ≥ 80, K ≥ 6, they hold for (m+2, K) and (m, K+1).
*Base* [CHECKED, Appendix A]: for m = 80 and m = 82 and every K = 1, …, 6 the whole near field was constructed and
(N1), (N2), (N3), (N5) asserted; all twelve runs pass. Both induction steps were also confirmed by machine once:
every ball of radius 5 around a near-field site of the instance (m, K) = (82, 6) is a translate, by one of the ten
transfers, of such a ball of (80, 6), and every one of (80, 7) is a translate along e1, e2 or e3 of one of (80, 6). ∎
(What is computer-assisted: the base cases; and the induction is confirmed, not replaced, by the machine check of
one step in each direction.)

### 8.5 The far field

After §8.4 there remains, for every long linker, a pair of caps whose columns are free. Let W be the set of these
caps ("wires"). For c ∈ W: beyond skin 1 its column is an arm in an open quadrant q_c, with constant α =: α_c and
X ∈ {x_c, x_c + 1}. Choose an odd h_0 larger than ρ of every near-field P and of every site of Oct(m), and than
max |α_c| + 8; put α* := max |α_c| + 6 (odd, like every α).

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
with ρ ≥ h_0, and disjoint from all near-field P's. Moreover there is L*, polynomial in m and |W|, such that for
each linker every length L ≥ L* of the parity fixed by the sublattices of its two caps can be prescribed.
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
*B. Slabs.* Let X_F exceed every X occurring so far. Order W by decreasing level (ties arbitrarily) and give the
n-th wire the slab value ξ_c := X_F + 60n. Wire c follows A_c up to its first site E_c with X ≥ ξ_c and ρ = ℓ_c + 2 that
is reached by a rung; X(E_c) ≤ ξ_c + 3 (Lemma A). From E_c it continues up the arm through E_c ("radial arm") to its site
with ρ = U_i, where i is the number of its linker and U_i := U_0 + 4i with U_0 odd, larger than all ℓ_c + 4 and than α* + 8.
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
 The levels u, u+2 are used by no other linker and by no avenue of stage A/B. Radial arms of other wires pass
 these levels inside their own slabs and strips; H_a and H_b stay within 8 of ξ_a, ξ_b in X, hence miss the other
 slabs, and miss their own radial arms except at t_a, t_b (an arm has one site per level); A* and A** lie in strips
 α ≥ α* that no wire uses. H_a ∩ A* = {s_a}, H_b ∩ A* = {s_b}, and H_a ∩ H_b = ∅ since |ξ_a − ξ_b| ≥ 60.
*D. Lengths.* Let β be the number of sites of the linker just built, and suppose X(s_a) < X(s_b) (otherwise exchange
a and b). Call a site v of A* *special* if α(v) = α* + 2 and ε(v) = +1; the special sites occur once in every four
values of X, and the step from a special site v to α* + 4 leads to the site of A** with X(v) − 1 (Lemma B(a)).
Replace the piece of A* from s_a to s_b by: A* from s_a backwards to a special site v_0 with X(v_0) < X(s_a); the step to
A**; A** forwards to the site with X = X(v_1) − 1, where v_1 is the first special site with X > X(s_a); the step to v_1;
A* forwards from v_1 to s_b. This is a simple path, disjoint from H_a and H_b, with 2 + 2(X(s_a) − X(v_0)) more sites than
before; X(s_a) − X(v_0) takes every value r + 4d, d ≥ 0, for one r ∈ {1,2,3,4}. So every length β + 4, β + 6, β + 8, … is
obtained [CHECKED, faru.py]. As β is bounded by a polynomial L*−4 in m and |W| (heights ≤ U_0 + 4|W|, slabs ≤ X_F + 60|W|,
one turn of Λ_u has 4u sites), every L ≥ L* of the right parity can be prescribed. The sites added lie on A*, A**
at the private levels of the linker. ∎
[CHECKED: this construction, without step D, is the "ordered" mode of build3.py; run in full on an instance in
which every bulk run is linked separately: m = 20, 1006 wires, 8 951 691 monomers, verified by the independent
checker. Step D: faru.py; a simpler padding was used in the test with three packings.]

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
§8.3 by its local rules, the frame links by the bounded search of Lemma N, the tether lengths as shortest paths in the
rows of Lemma N, and the linker lengths as the constant L* of Lemma F (plus one where the parity requires it); none of
this depends on a packing.
If the word has a fold with at least k contacts, it has one with exactly k (Corollary 4) and then a packing exists
(§7). If a packing exists, §8.6 gives a fold with k contacts. ∎

## Appendix A. Machine checks

All scripts are in HP_tetrahedral_code.tar.gz (Python 3, no packages). "Independent checker" = verify_fold.py, which
reads a list of coordinates and letters and uses nothing from the construction.

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
| Lemma A; Lemma F, step D | faru.py | four quadrants, several levels and strips |
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
