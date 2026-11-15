# HP folding on the tetrahedral (diamond) lattice — working notes

Source paper: Berger & Leighton, "Protein Folding in the HP Model is NP-Complete" (RECOMB 1998), cubic lattice.
Goal: adapt the method (or find another) for the tetrahedral lattice.

**Status legend.** [PROVED] full argument written here. [CHECKED …] verified by computer in the stated range.
[PLAN] design, not proved. Nothing marked [PLAN] should be read as established.

_Last updated: checkpoint 21 (Sat 08:42 PST) — the proof is now written out as one document, **HP_tetrahedral_proof.md** (statement, all lemmas with proofs, the construction, appendix of machine checks). These notes keep the history and the experiments. Not independently checked._

## Bottom line

**Claim (§10.8):** HP string folding on the tetrahedral (diamond) lattice is NP-complete, by a reduction from bin
packing. Every step of the proof is now written in these notes and nothing is known to be missing. It is **not yet
an established theorem**: parts are computer-assisted, two arguments are written in short form rather than line by
line, and nobody else has checked any of it.

**Proved by hand, complete:**
* Theorem 3: sharp isoperimetric inequality on the diamond lattice, |S| ≤ (4/3)(|∂S|/4)^{3/2} (§4).
* Theorem 5: N_m = m(4m²−1)/3 sites have at most 2N_m − 2m² bonds, with equality only for the octahedron Oct(m)
 (§5). This is the analogue of the cube lemma that Berger–Leighton say fails on this lattice.
* All local facts about Oct(m), (O1)–(O7), including the P-link table for all lengths (§5.6).
* The whole "only if" direction: an optimal fold of the string yields a packing (§10.3).
* In the "if" direction: the columns of all dangling sites are pairwise disjoint, the margins are column-free, and
 the tether routes (§10.7).

**Computer-assisted (finite machine checks + transfer arguments):**
* Bulk Lemma: the interior is covered by runs given by explicit local rules, without cycles, for all m (10.4.1;
 the argument for all m was completed at checkpoint 20).
* Near-field Lemma: frame links, borrowed columns and tethers fit for all m and K (§10.7; checks at m = 80, 82 for
 K ≤ 6; the induction over m and K rests on locality and was confirmed by machine for one step each).

**By hand:** Far-field Lemma (all long linkers fit with prescribed lengths); written out in full, with an explicit
length-adjusting detour, in HP_tetrahedral_proof.md §8.5 (short form in §10.7 here). Its construction was
run in full on a dense instance (8 951 691 monomers).

**End-to-end evidence (independent verifier):** 55 complete optimal folds for m = 24 … 46; m = 80 with four bins;
and one HP string of 155 900 letters folded in three different ways for three different packings, each with
167 440 H–H bonds = the proved maximum. These tests use the construction with small constants; the constants of
§10.2 need m in the hundreds and cannot be run here.

---

## 0. Setting

Lattice **D**: sites (x,y,z) ∈ Z³, x≡y≡z (mod 2), x+y+z ≡ 0 (sublattice A) or 3 (sublattice B) mod 4.
Bond vectors t1=(1,1,1), t2=(1,−1,−1), t3=(−1,1,−1), t4=(−1,−1,1); A-site v ~ v+t_k, B-site v ~ v−t_k.
4-regular, bipartite, girth 6; two sites have at most one common neighbour.
Distance between two A-sites differing by Σ n_k t_k (Σ n_k = 0) is Σ|n_k|; the geodesic along a ⟨110⟩ direction
t_a − t_b is unique (the straight zigzag).

Fold of s ∈ {H,P}^N: injective, consecutive letters adjacent. S = H-sites, h = |S|, e(S) = bonds inside S
(B–L convention: chain bonds included), ∂S = bonds leaving S; 4h = 2e(S) + |∂S|.

## 1. Why B–L does not transfer verbatim

They use (i) uniqueness of the cube (Loomis–Whitney), (ii) faces/edges told apart by 1 vs 2 missing neighbours,
(iii) "HPPH ⇒ the two H's are adjacent" (4-cycles). On D: (i) needs a new argument (§4–5); (ii) fails — the optimal
shape has only 6 sites with two missing neighbours; (iii) is false (girth 6).

## 2. Lemma 1 (tight bound) [PROVED] — any d-regular lattice

J = number of i with {s_i,s_{i+1}} = {H,P}. Then e(S) = (d·h − |∂S|)/2 ≤ (d·h − J)/2, with equality iff every bond
between an H-site and a non-H-site is a chain bond ("tight fold"). On a Bravais lattice with d ≥ 6 no finite S is
tight (a hull vertex has ≥ 3 outside neighbours, a monomer only 2 chain neighbours); on D tight sets exist.

## 3. Lemma 2 (sublattice balance) [PROVED]

Σ_{v∈S∩A} deg_S(v) = Σ_{v∈S∩B} deg_S(v). A fold cuts S into its maximal H-runs (paths), and
|S∩A| − |S∩B| = (#odd runs with A-ends) − (#odd runs with B-ends). In a tight fold this forces |S∩A| = |S∩B|.
For Oct(m) the difference is m, so Oct(m) has no tight fold: use B–L's "perfect fold" (S = optimal shape) instead.

## 4. Theorem 3 (sharp edge-isoperimetric inequality on D) [PROVED]

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

**Corollary 4 [PROVED].** N_m := m(4m²−1)/3 = 1, 10, 35, 84, … If |S| = N_m then |∂S| ≥ 4m², i.e. e(S) ≤ 2N_m − 2m².
(If C ≤ 2m²−1: |S| ≤ (4/3)(m²−½)^{3/2} ≤ (4/3)m³ − m + 1/(8m) < N_m.)
[CHECKED] Theorem 3 on 1500 random connected clusters (largest ratio |S|/bound = 0.82).

## 5. The octahedron and its uniqueness [PROVED — checkpoint 15]

### 5.1 Definition of Oct(m) and its numbers [PROVED]

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

### 5.4 Proof of Claim U [PROVED]

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

### 5.5 Profile ⇒ shape [PROVED]

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

**Theorem 5 [PROVED].** A set S ⊂ D of N_m sites has at most 2N_m − 2m² bonds, with equality iff S is a translate of
Oct(m) or of its mirror image. Consequently (analogue of B–L Theorem 3.2) a string with N_m H's has a fold with
2N_m − 2m² H–H bonds iff it has a fold whose H's form Oct(m) (up to mirror image).

### 5.6 Tetrahedral coordinates and the local facts (O1)–(O7) [PROVED — checkpoint 15]

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
once it is true for m_0, where 4m_0 ≥ 3(2r+2) + 2R' + 24. This is used for the Bulk Lemma (10.4.1) only; (O1)–(O7)
above do not need it.

**Region transfers (the form used in §10) [PROVED; CHECKED D = 3, m = 17, 18, regiontransfer.py].** Put Oct(m+2)° :=
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
 faces that are far stay far. The foliation of 10.4.1 depends only on the signs of Y and Z (and on which sites
 have Y = 0 or Z = 0), which each transfer keeps inside the ball. ∎
 For m ≥ 3D + 8 every site of Oct(m) satisfies at least one hypothesis (near a vertex ±x, a Y- or Z-plane edge or
 a face with |X| large: T-x; near ±y: T-y; near ±z: T-z; near an X-plane edge or a single face: T-r or T-y/T-z).
 Hence: *a statement about D-balls of a construction given by local, translation-covariant rules holds for all
 m ≥ m_0 of one parity as soon as it holds for m_0* (and for both parities if checked for m_0 and m_0+1).

## 6. Local motifs on Oct(m) [CHECKED m = 3…7; follow from §5]

In a perfect fold every H–P chain bond is a dangling bond, and a dangling site has a unique neighbour in S. Hence:
* PHP ⇒ that H is one of the 6 vertices.
* HPH never occurs. HPPH never occurs (no two dangling sites are adjacent).
* H PPP H ⇒ the two H's are on the same face and are second neighbours ("T-adjacent": the surface sites of a face
 form a triangular lattice T). Every T-edge of every face is realised (192 for m = 5).
* PHHP ⇒ a bonded pair of surface sites; these exist only on the edge zigzags and next to vertices (24(m−2)+12 pairs).
* P H^k P: two surface sites at distance ≤ k−1 in S; the interior sites of the run carry no P.
Consequence: B–L's item "(PHHP)^k = connected path on a face" does not exist; surface sites of one face are never bonded.

## 7. Rigidity tools

**Projection ("taut chain") lemma [PROVED given §6].** Fix an edge direction u = t_a − t_b, π(v) = v·u/4.
A bond changes π by −1, 0 or +1; a run H^k advances ≤ k−1 with equality iff it is the straight u-zigzag; a PPP link
advances ≤ 2 (its ends are T-adjacent) with equality iff the displacement is u. The two ends of an edge differ by
2m−2 in π, the maximum over all pairs of sites of Oct(m).
⇒ A segment "PHP … PHP" made of runs and PPP links with total maximal advance exactly 2m−2 lies on one edge zigzag,
every H at a determined position (antipodal vertices are excluded by the same count).
Constraints: 6 PHP's ⇒ at most 5 framed edges; consecutive framed edges lie on different big faces; two sides of a
small face can be framed, two sides of a big face cannot.

**Forced ports [PROVED].** A PPP link in a frame skips exactly one zigzag site z; both bonded surface neighbours of z
are frame run-ends, so z must be a run-end entered from its unique inner neighbour. Any set of pairwise
non-consecutive zigzag sites can be made into ports.

**Rigid bars [PROVED].** A run P H^k P joining two pinned sites whose displacement is ((k−1)/2)(t_c − t_d) is the
straight zigzag. E.g. ports on the two framed sides of a small face are joined by straight rows of that face.

**Capacity counting [PROVED].** σ = surface site of a face, τ = sub-surface site (3 σ-neighbours + 1 inner site).
Each run meets the top bilayer of a region in pieces alternating σ/τ: σ…σ (one more σ than τ), σ…τ (equal),
τ…τ (one more τ; the bulk coming up through an uncapped σ). Hence #σ − #τ = #(σ…σ pieces) − #(τ…τ pieces).
For a strip of w rows between two straight row-walls on a face whose two sides are framed, #σ − #τ = #ports − w < 0.
If the only run-ends placed in the strip are items (3-runs σ–τ–σ', i.e. units of strings (PPP HHH)^s), then the
number x of item units satisfies x ≤ (#σ − (w − #ports))/3: an area-type capacity, attained iff every other σ is
a one-site excursion of a bulk run. T-walk strings cannot cross a wall (wall sites carry no P), so an item lies in
one strip. This is the tetrahedral replacement for B–L's bins.

## 8. Bar decomposition and explicit optimal folds [CHECKED m ≤ 6]

The t1/t2 zigzag chains partition Oct(m) into straight bars: exactly (2a−1) bars of length (2a−1) for a = 1..m
(Σ(2a−1)² = N_m); both ends of every bar are surface sites. Visiting bars in snake order with P-linkers routed
outside gives explicit strings with explicit folds that meet Corollary 4, so their optimum is known exactly:
* m = 2: PHHHPPPPHHHPPPHHHPPPHP — optimal fold has 12 H–H bonds (6 beyond the chain bonds).
* m = 3: PHHHPPPHHHHHPPPHHHHHPPPPPPHHHHHPPPHHHHHPPPHHHHHPPPPPPPHHHPPPHHHPPPPPHP — 52 H–H bonds.
(m = 7 not built: my naive linker router got stuck; this is a limitation of the script, not of the construction.)

## 9. Routing of P-linkers

Contracting all t1-bonds of D gives Z³, so vertex-disjoint path systems in Z³ lift to D; B–L's 3-D routing lemmas
carry over, lengths padded by far-away loops, parity automatic (D is bipartite). [PROVED: the contraction; rest PLAN]

## 10. The reduction (current design: "dimer anchors")

### 10.1 Facts about Oct(m) that are used

Edge zigzag: V, b_0, a_1, b_1, …, a_{m−2}, b_{m−2}, V' (zigzag index 0 … 2m−2); a-sites are Maj and have their free
bond on the big face of the edge, b-sites are Min with the free bond on the small face. b_0 and b_{m−2} are "corners":
a corner belongs to the two edges of its small face that meet there; its three neighbours are the vertex and the two
a_1's. "Dangling site" = outside site adjacent to Oct(m).

* (O1) [PROVED §5.6] Each surface site has one dangling site, the 6 vertices have two. A dangling site has exactly
 one neighbour in Oct(m); two dangling sites are never adjacent.
* (O2) [PROVED §5.6] The surface sites of a face form a triangular lattice T; a link P^3 joins two surface sites
 iff they are T-neighbours on a common face.
* (O3) [PROVED §5.6] Two surface sites are bonded only along the edge zigzags.
* (O4) Link table [PROVED §5.6 for all k ≤ 2m; also CHECKED m = 8, 11, 16, all pairs of surface sites; adv.py]. For an edge direction u, π = v·u/4. The
 largest π-advance of a link P^k between surface sites is k−1 for odd k and k−3 for even k (k = 3…11). If the link
 starts at zigzag index i of an edge with direction u and attains the maximum, it ends at index i+k−1 (k odd) or
 i+k−3 (k even) of the same edge. In particular P^3, P^6, P^10 skip exactly 1, 2, 6 zigzag sites.
* (O5) [PROVED §5.6] T-neighbours among non-vertex zigzag sites: along one edge (a_i, a_{i+1}), (b_i, b_{i+1})
 (corners count as b_0); at a vertex of a big face the two a_1's; at a corner of a small face the two b_1's.
* (O6) [PROVED] A lattice path between sites differing by Σ n_k t_k with Σ n_k = 0 has at least Σ|n_k| bonds (each
 bond changes one coefficient by 1 in the representation with Σ n_k ∈ {0, ±1} given by the path). Paths of P's are
 lattice paths, so this bounds every tether from below.

* (O7) Two "height" functions [PROVED §5.6; also CHECKED m = 6 … 20, coordfacts.py]. With e1 ∥ t_a − t_b and e3 ∥ t_a − t_c from V_a, put h(v) = v·(t_a+t_b)/2 and k(v) = v·(t_a+t_d)/2.
 Every bond changes h and k by exactly ±1. Along the track (zigzag index i from V_a) h = h_0 + i − 1 and
 k = k_0 + i − 1, where h_0, k_0 are the values at the corner at V_a. On e1: |h − h_0| ≤ 1 and k = k_0 + i − 1.
 On e2 (index i from V_c): h = h_0 + 2m − 3 − i and |k − (k_0 + 2m − 3)| ≤ 1. Every zigzag site of Oct(m) that is not
 one of the track sites a_1 … b_{m−3} of e3 has h ≤ h_0 + 1 or k ≥ k_0 + 2m − 5.

All of (O1)–(O7) are now proved by hand in §5.6 (tetrahedral coordinates).

### 10.2 The string (constants of checkpoint 18)

Input: K bins of capacity B, items s_1 … s_n with Σ s_i = K·B (bin packing in unary, strongly NP-complete).
 Σ* := 18K + 40 (an upper bound for the tether slacks below), λ := Σ* + 8, C := λB; item i becomes a chain of λ·s_i
 dimers. J := C + Σ* + 8; j_k := J + (k−1)(C+2) for k = 1 … K+1; R := C + Σ* + 9; m := j_{K+1} + R + 3.
 (J, C, all j_k are even, R is odd, m is even.)
"Dimer chain of q dimers" = (HH PPP)^{q−1} HH. Units, in this order, joined by long P-linkers whose lengths are fixed
by the construction of §10.7 and do not depend on the packing:

1. H — the first monomer of the chain.
2. Three times PHP.
3. Frame chain PHP · [e1] · PHP · [e2] · PHP: H-runs separated by links P^3, P^6, P^10 so that, laid along two
 edges, the links skip: on e1 (indices from V_a) {1,2}, the 2-slots {6k, 6k+1} (k = 1 … K+1) and {2m−3}; on e2
 (indices from V_c) {1}, the 6-slots {10k+6, …, 10k+11} (k = 0 … K) and {2m−3}. All frame runs have length ≥ 3.
 The link lengths add up to the maximal advance 2m−2 on each of the two parts.
4. For k = 1 … K+1 a separator group: HH · P^{2j_k+3+σ_e(k)} · HH PPP HH · P^{2(m−2−j_k)+3+σ_x(k)} · HH PPP HH PPP HH
 (entry anchor = 1 dimer, separator = 2 dimers, exit anchor = 3 dimers; the two long P-runs are the tethers).
 The slacks σ_e(k), σ_x(k) are even numbers in [0, Σ*] produced by the construction (margin tethers, §10.7); in all
 runs σ_e(k) = 6, 18, 28, 38, … and σ_x(k) = 16 + 8K + 6(K+1−k), independent of m, J, C.
5. Items: dimer chains of λ·s_i dimers, in the order i = 1 … n.
6. Fillers: dimer chains of J, R, 3(m−2), 3(m−2), 3(m−2) dimers.
7. Bulk units: runs H^ℓ with ℓ ≥ 3, some of them joined by PPP (from the cover of §10.4.1 and the chaining of §10.7).

The number of H's is N_m and the number of dimers is D = (m−1) + 4(K+1) + 9(m−2). Question: is there a fold with
2N_m − 2m² H–H bonds? (By Corollary 4 no fold has more.) Everything has size polynomial in K·B.
(Checkpoint 14 had taut tethers, σ = 2 and 4, and λ = 8; taut tethers cut the columns of §10.7, hence the change.)

### 10.3 "Only if": an optimal fold yields a packing

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
7. *Separators are pinned* [PROVED from (O7)]. A separator is two matched dimers joined by a P^3 (its four sites are
 within 4 bonds of each other), with a tether of L_e = 2j_k+3+σ_e P's from an H in a 2-slot of e1 (zigzag index
 ≤ 6K+7) and a tether of L_x = 2(m−2−j_k)+3+σ_x P's to an H in a 6-slot of e2 (index ≤ 10K+11 from V_c);
 0 ≤ σ_e, σ_x ≤ Σ*. h and k change by 1 per bond, so for the first H w and the last H w' of the separator:
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
 long the other linkers are, or that bulk runs are joined by PPP.)

### 10.4 "If": a packing yields an optimal fold

Construction (final form: §10.7; code/build3.py). Coordinates of 5.6; F' = small face 4, e1 = E(3,4), e2 = E(1,4),
track e3 = E(2,4). Frames on e1, e2; anchors in their slots; separator k on D_{j_k}, D_{j_k+1} (traversed b a PPP a b,
tethers at the b-sites); every other track chain starts at an even track index and is traversed a b PPP b a PPP a b …,
so all its ends are a-sites; items of bin k on the C dimers between separators k and k+1 in any order; fillers on
the rest of the track and on the rings; the first H on the corner between e1 and e2; bulk runs on the cover of
10.4.1; tethers in margins of private skins; every other linker along the column of its cap and then through the
far field. Nothing except the positions of the items depends on the packing.

Older demos (earlier designs; still valid optimal folds):

**Demo [CHECKED, one instance; build2.py, 85 s].** (Built with the earlier constants: scaling 4, J = 9.) m = 38, K = 2 bins of 4 dimers, items 4 and 4, separators on
track dimers (9,10), (15,16), (21,22) with tethers P^21/P^55, P^33/P^43, P^45/P^31; frame with four P^6 and three
P^10 links; 32 bulk runs; 46 linkers. Result: self-avoiding walk of 85 557 monomers, H-set = Oct(38),
**143 412 H–H bonds = 2N − 2m²**; confirmed by the independent checker verify_fold.py. Files demo2_fold_string.txt,
demo2_fold_coords.txt. (The earlier demo of the staple design, m = 26, is still a valid optimal fold.)

**Second demo, with the constants of checkpoint 10 (scaling 6, slack 2 on both tethers) [CHECKED; build2.py].** m = 40, K = 1, B = 1 (C = 6, J = 14): chain
of 99 565 monomers, **167 440 H–H bonds = 2N − 2m²**, confirmed by verify_fold.py (files demo3_m40_fold_*.txt).

Two lemmas turn the construction into a proof for all instances:
* **Bulk Lemma [computer-assisted proof, see 10.4.1].** For every m ≥ 15 the set X_m = Oct(m) minus the 12 edge
 zigzags is a disjoint union of lattice paths with ≥ 3 sites whose two end sites are surface sites; the paths are
 given by explicit local rules (computable in time linear in |X_m|).
* **Routing Lemma [§10.7: far field proved in outline, near field checked on instances, not proved in general].**
 All P-runs fit, with lengths that do not depend on the packing.

### 10.4.1 The Bulk Lemma: construction and proof

**(O0) Explicit description of Oct(m)** [CHECKED m = 4 … 14, halfspace.py]. With c = (0, 2m−2, 0),
Oct(m) = { v ∈ D : s·(v − c) ≤ 2m−2 for the four sign vectors s with s_x s_y s_z = +1, and ≤ 2m−1 for the other four }.
In absolute coordinates the four faces with s_y = −1 do not depend on m and the four with s_y = +1 move by 4 per
unit of m. The six vertices are (0,0,0), (0,4m−4,0), (±(2m−2), 2m−2, 0), (0, 2m−2, ±(2m−2)).

**Coordinates.** Y = y − (2m−2), Z = z − 1, X = x; ρ = |Y| + |Z|, α = |Y| − |Z|. A-sites have even, B-sites odd
coordinates, so Y and Z have opposite parity and no site has Y = Z = 0.

**Lemma T (transfer) [PROVED from (O0); also CHECKED].** Fix a radius r. For all large m, every site of Oct(m) has
the same labelled r-neighbourhood (which sites are in Oct(m), on an edge, outside; signs of Y and Z; position
relative to a vertex if one is within r) as some site of Oct(m_0), m_0 = m_0(r).
Proof. Call a face or one of the planes Y = 0, Z = 0 *active* at v if it is within distance r of v. Going from m to
m−1 the faces with s_y = +1 move by −4, the others not at all, the plane Y = 0 moves by (0,2,0), the plane Z = 0 not
at all. For large m the active faces all pass near one vertex, or near one edge, or it is a single face, or none.
In each case there is a lattice vector δ with s·δ = 4 or 0 for the active faces (according to s_y = ±1), δ_y = 2 if
Y = 0 is active and δ_z = 0 if Z = 0 is active: δ = (0,4,0) near the vertex (0,4m−4,0); δ = 0 near (0,0,0);
δ = (±2,2,0) near the vertices (±(2m−2),2m−2,0) and along the edges through them; δ = (0,2,±2) near the vertices
(0,2m−2,±(2m−2)) and along the remaining edges through them; for a single face or in the interior any of these.
Translating by −δ maps the neighbourhood of v in Oct(m) to a neighbourhood in Oct(m−1) with the same labels,
provided v − δ stays farther than r from the non-active faces; if not, first translate v along the active edge,
face or plane by a lattice vector (period ≤ 4), which is possible as soon as the edges are longer than 2r + 8. ∎
[CHECKED, sigcheck.py: with the 7×7×7 box around each site and vertex positions up to distance 12, there are exactly
1486 different neighbourhoods; all occur for m ≤ 14 and none is new for m = 15 … 40; the final bonds of the cover
below are a function of the neighbourhood.]

**Construction (code/canon.py).**
1. *Bent foliation* (as in checkpoint 11): join two neighbouring sites iff their ρ differ. Each site has exactly two
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
 each vertex (file canon_patches.py; found once, for m = 14, by a local search).

**Claim 1 (it is a cover by paths with good ends).** Every site of X_m gets one or two partners; sites with one
partner have a free bond; no component has fewer than 3 sites. These are statements about bounded neighbourhoods, so
by Lemma T they hold for all m once they hold for small m. [CHECKED directly for every m = 9 … 60 and 64, 68, …, 100.]

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

**Completion of the proof of Claim 2 for all m (checkpoint 20).** "Joint" = a bond of the cover that is not a
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

The cover has about 1.7·m² paths (the demo folds used a different cover with only m − 6 paths, found by max-flow).

### 10.5 Status of the pieces (see the table in §10.8 for the final list)

| Piece | Status |
|---|---|
| Theorem 3, Corollary 4 (upper bound) | proved (§4) |
| Theorem 5 / Claim U (only Oct(m) attains it) | proved (§5.3–5.5) |
| (O1)–(O7), region transfers | proved (§5.6) |
| Only-if (optimal fold ⇒ packing) | proved (§10.3) |
| If: Bulk Lemma | computer-assisted proof for all m, completed at checkpoint 20 (10.4.1) |
| If: Near-field Lemma | computer-assisted proof (10.7); induction steps in m and K machine-checked once each |
| If: Far-field Lemma | by hand, short form (10.7); construction run in full on a dense instance |
| If: instances | 55 complete folds (m = 24 … 46), m = 80, one string / three packings, dense test; all independently verified |

### 10.6 Route for the remaining parts

**Part 1 — Claim U.** DONE (checkpoint 15): §5.3–5.5.

**Part 2 — the facts (O0)–(O7).** DONE (checkpoint 15): §5.1 takes (O0) as the definition and derives the layer
sizes, N_m and the 4m² boundary bonds; §5.6 proves (O1)–(O7) and a clean form of Lemma T.

**Part 3 — Bulk Lemma.** Done as a computer-assisted proof (10.4.1). To tighten: derive (O0); write out in full why
the table of Claim 2(a) is m-independent (the two joints of a segment are moved by one period of their edges when α
changes by 4).

**Part 4 — Routing Lemma.** Superseded by §10.7 (checkpoints 16–19): new design, built and verified; far-field lemma; list of what the near field still needs.

**What is left (after checkpoint 20).** Nothing is known to be missing; what remains is verification and
formalisation: (1) repeat the machine check of the induction steps of the Near-field Lemma (nfinduct.py) with larger balls and
at more sizes, or formalise it; (2) write the Far-field Lemma line by line; (3) assemble one document; (4) independent check.

### 10.7 The Routing Lemma (checkpoints 16–19) [far field: proof in outline; near field: partly PROVED, rest CHECKED on instances]

(The paragraphs are in the order in which things were found; the final design is the one of checkpoints 17–19.)

**Skins.** O_j := the octahedron of size m+2j concentric with Oct(m) (in the coordinates of 5.6: A-sites with
|f_i| ≤ 2m−2+4j, B-sites with −(2m−1+4j) ≤ f_i ≤ 2m−3+4j). D ∖ Oct(m) is the disjoint union of the *skins*
O_j ∖ O_{j−1}, j ≥ 1, and skin j is exactly the top bilayer of O_j (sites of depth 0 or 1 below some face) [PROVED:
5.6]. Skin 1 contains the dangling sites ("level 1") and the middle sites of P^3 links ("level 2").

**Columns [PROVED + CHECKED m = 20, arms.py].** Pair the faces by quadrants of (Y, Z): big face k with small face
i(k), (1,2), (2,1), (3,4), (4,3); both lie in one closed quadrant, and the straight zigzag in direction t_k − t_{i(k)}
= (0, ±2, ±2) is the outward arm of the bent foliation of 10.4.1 there. The *column* of a dangling site p over big
face k or small face i(k) is the half-line from p in that direction.
 * Every dangling site lies in the closed quadrant of its face (with Z = z − 1), so its column is a foliation arm.
 * Along the column of p over big face k, f_k = 2m+1, 2m+2, 2m+5, …; a dangling site over another face has f_k ≤ 2m−2.
 Likewise over small faces. Hence a column never enters Oct(m) and contains no dangling site except its start; and
 since the foliation chains partition D, **the columns of all 4m² dangling sites are pairwise disjoint.**
 * In skin j a column over small face i occupies one bonded pair of sites; in the triangle coordinates of the face
 (g_a, g_b, g_c ≥ 0, one per side) the distance g to the side shared with big face k(i) stays the same and the
 other two grow by 1 per skin. So **in skin j the j rows next to the other two sides of a face carry no columns
 at all** ("margins"), and neither does the row over an edge whose sites carry no linker caps on that face.
 * The middle site of a P^3 link between T-neighbours v, v' on a face lies on the column of one of the three
 sites of its triangle; it is the third one (a conflict) only for links along the four edges E(k, i(k)) (the
 "X-plane edges"). [CHECKED m = 20: the third sites along these edges are never run ends of the cover of 10.4.1,
 except two sites next to the vertices, which are zigzag sites.] So no dimer-chain link blocks a bulk column.

**Consequences for the design.**
1. *Bulk caps need no stubs:* every run end of the bulk cover starts its column directly.
2. *Tethers must change* (they would cut the columns over F'): a tether leaves its slot along the slot site's own
 column up to a private skin j, runs in skin j along the row over the frame edge (e1 or e2, which carry no linker
 caps on F') and then in the margin next to e3, and comes down along the column of the separator's b-site.
 Entry tethers use skins 2 … K+2 (slots nearer V_a lower), exit tethers skins K+3 … 2K+3. All of this is
 column-free by the previous paragraph, for every m and K. [PLAN; builder to confirm]
 Price: tether k is longer than the taut length by an explicit slack σ = O(K) (≈ 2·(slot distance) + 4·(skin)).
 The only-if proof survives with these changes: in step 7 the bounds become i ≤ j_k + 3 + σ_e/2 and
 i ≥ j_k − 3 − σ_x/2; J, R and the scaling λ of the item sizes (C = λB) have to exceed 7 + Σ, Σ := max slack; then
 c_k ∈ [C − 6 − Σ, C + 6 + Σ] and λ | c_k give c_k = C as before. (To be rewritten with exact constants.)
3. *Track chains* are traversed in one global alternating pattern (D_i from a to b for even i, from b to a for odd
 i), all chain boundaries lie between D_{2t−1} and D_{2t}, so every chain end is an a-site and all packing-dependent
 caps are over the big face of e3; over F' the track carries only b–b links and the 2(K+1) tether ends.
4. *Far field.* Above the last tether skin everything is a product: the bent foliation gives coordinates
 (quadrant, α, X) that are constant along a column, so in every cylinder shell C_h = {ρ ∈ {h, h+2}} the columns are
 point obstacles at the same positions. Scheme: columns are stopped at levels decreasing in X (so the stopped
 linker can run in the +X direction inside its shell without meeting a column that is still rising), run to the
 column-free zone X > 2m+2, and are connected there in private slabs; lengths are padded in the free zone.
 Polynomial size. [PLAN: lemma to be written; a simpler variant (one private shell per linker, as in build2.py)
 is what the demos use.]


**Checkpoint 17: the design works end to end on instances [CHECKED; code/build3.py].**
Final labelling (coordinates of 5.6): F' = small face 4; e1 = E(3,4) (the X-plane edge of F', carries the 2-slots),
e2 = E(1,4) (6-slots), track e3 = E(2,4). Reasons, all found by running the builder:
 * If the track is the X-plane edge, both tethers of every separator must run in the two column-free rows along
 it, which is a single lane: entry tether k+1 and exit tether k cannot pass each other's vertical parts. With the
 track on a margin side, the tether of skin j runs in rows < j of the margin while all separator columns sit in
 row j: no conflict at all.
 * Over the X-plane edge every P^6 link uses the second column site of the caps of its slot. Those caps then take
 the column of a neighbouring second-row site instead ("borrowed column"); second-row sites along X-plane edges are
 never run ends, so these columns are free. (3–4 borrowed columns per instance.)
 * For odd m the alternation of a ring chain does not close at the corners (this is why m was taken even); the
 builder also handles odd m by one chain per ring side.
Results: for m = 24, 30, 37, 40, 52 and 1–3 bins the near field is consistent (all frame links in skin 1; tethers
in margins; **no linker column is blocked**), and complete folds were built and verified by verify_fold.py:
 m = 24 (1 bin): 39 407 monomers, 35 696 H–H bonds = 2N − 2m²; m = 40 (3 bins, items 2,4 | 6 | 2,2,2, four separators):
 155 744 monomers, **167 440 H–H bonds = 2N − 2m²**, built in 5 s. (Files demo4_m24_*, demo4_m40_*.)
These use the cover of 10.4.1, columns, margin tethers and one private cylinder shell per long linker; to keep the
chains short the bulk runs are chained by P^3 links where possible (774 runs → 43 units for m = 24), which the
only-if proof allows. They use small ad hoc values of J, R, C, not the constants needed for the only-if direction.
Measured tether slack (independent of m and J): entry tether of separator k: 6, 18, 28, 38 for k = 1…4; exit tether:
16 + 8K + 6(K+1−k). So Σ ≤ 14K + 16 in these runs.


**Checkpoint 18: one string, three packings [CHECKED; build3.py, verify_fold.py].** m = 40, three bins of capacity
6 (in dimers), items 2, 4, 6, 2, 2, 2 in this order in the string. Everything except the item chains is built
without looking at the packing; all sites an item could use are set aside first; every long linker is padded,
inside its private shell, to a prescribed length (the maximum over the three runs). For the three packings
{1,2 | 3 | 4,5,6}, {3 | 4,2 | 5,1,6} and {5,6,1 | 2,4 | 3} the builder produces **the same HP string of 155 900 letters**
and three different folds, each a self-avoiding walk with H-set Oct(40) and **167 440 H–H bonds = 2N − 2m²**
(independent checker). Files packA/B/C_fold_coords.txt, packA_fold_string.txt.
This is the "if" direction working as a reduction should, on one instance with small constants; it is not a proof
of the Routing Lemma.

**What a proof of the Routing Lemma still needs.**
 (a) *Near field, for all m, K, B and all packings:* frame links in skin 1 avoiding the caps of the slots and the
 caps and second column sites of the bulk run ends; borrowed columns for the slot caps on e1; tether corridors
 (existence and the bound σ ≤ Σ*); no near-field P on a linker column. All of these are local or periodic
 statements (the builder checks them in a second for each instance; done for m = 24, 30, 37, 40, 52, K ≤ 3), so a
 proof would go through Lemma T (5.6) plus the explicit corridor description, or be replaced by explicit formulas.
 (b) *Far field:* the product structure described above gives a routing with private shells; to write: the
 connectivity of a cylinder shell minus the columns passing through it (or the cleaner scheme with levels
 decreasing in X), and padding by hexagon moves (each replaces one site of the path by three).
 (c) *Bulk chaining* is optional (it only shortens the chain).


**Checkpoint 19: the far field, as a lemma.**
*Sweep* [CHECKED, sweep3.sh]: complete optimal folds for every m = 24 … 46 and K = 1, 2, 3 that fits (55 instances,
both parities of m): 0 failures.
*A warning from the computer:* without chaining (every bulk run linked separately) the simple router fails: with
one private shell per linker, a column that has stopped is fenced in by the columns still rising around it
(m = 20: failure at the 14th linker). The proof must therefore use the ordered scheme below; with it the same
instance works: **m = 20, all 490 bulk runs separate, 503 linkers: chain of 8 951 691 monomers, 20 520 H–H bonds
= 2N − 2m², verified by the independent checker** (build3.py … nochain … ordered; 37 s).

*Structure used* (Y, Z as in 10.4.1, ρ = |Y|+|Z|, α = |Y|−|Z|; inside one open quadrant of (Y,Z)):
 (F1) every bond changes X by ±1 and either ρ by ±2 ("rung", α unchanged) or α by ±2 ("step", ρ unchanged). At a
 site v both rungs have the same ΔX =: ε(v), both steps have ΔX = −ε(v), and ε has opposite signs on the two
 sublattices. (Check on the four bond vectors; e.g. for Y, Z > 0: t1, t2 are rungs, t3, t4 steps.)
 (F2) *Column:* rungs upward; X alternates between x and x+1, α is constant. *Avenue:* rung up, step α→α+2, rung
 down, step α+2→α, …, started so that every bond has ΔX = +1; it occupies exactly the sites of two levels
 {ℓ, ℓ+2} with α ∈ {α_0, α_0+2} (four sites per four units of X).
 (F3) *Level curve:* inside a quadrant the steps alternate ΔX = ±1, so the curve ρ = u stays on a pair of X-values;
 at each of the four bend planes the pair shifts by +1 [CHECKED u = 9, 21; the picture at a bend is the same for
 all u by a lattice translation along the bend plane]. So {ρ = u} is one infinite helix: 4u sites and ΔX = 4 per turn.
*Far-field Lemma.* Let W be a finite set of dangling sites ("caps") whose columns are free of all other P's, paired
arbitrarily into linkers. Then the linkers can be routed disjointly, and with any prescribed lengths L_i ≥ L*
of the right parity, where L* is polynomial in m and |W|.
Construction (this is exactly the "ordered" mode of build3.py):
 A. Let x_c be the smaller X-value of the column of c. Columns with larger x_c stop lower: level ℓ_c = h_0 + 4·(rank
 of x_c in decreasing order), h_0 above the near field. From its top the linker runs as an avenue in the +X
 direction, levels {ℓ_c, ℓ_c+2}, strip {α_c, α_c+2}.
 *Disjointness.* A column still rising through these levels has x < x_c, so it lives on X ≤ x_c, while the avenue
 lives on X > x_c (apart from the top of c itself). Columns with the same x have α ≡ α_c (mod 4), α ≠ α_c, so
 they and their avenues miss the strip. Different levels are 4 apart; different quadrants do not meet.
 B. Beyond X_F (right of everything) each wire gets a private slab ξ_c (spacing 20), assigned in order of
 decreasing level. In its slab the avenue stops after a rung up and continues as a column ("radial arm") to the
 private outer level U_i of its linker (U_i = U_0 + 4i, above all levels ℓ).
 *Disjointness.* The arm stays in the strip of c and in X ∈ [ξ_c−1, ξ_c+5]; it crosses only levels above ℓ_c, and
 every wire with a higher level has left its avenue in an earlier slab; wires of the same level have other strips.
 C. On level U_i the two arm tops lie on the helix {ρ = U_i}. Each walks along the helix (less than one turn, so X
 stays within its slab) to a fixed free strip (quadrant Y, Z > 0, α ∈ {α*, α*+2}, α* larger than every α_c), and the
 two are joined by an avenue along that strip on levels {U_i, U_i+2}.
 *Disjointness.* Levels {U_i, U_i+2} are private; arms of other wires pass through them only in their own slabs
 and strips, which the helix pieces (other slabs) and the free strip avoid.
 D. *Lengths.* Prolonging the strip avenue beyond the farther slab and returning on the neighbouring free strip
 {α*+4, α*+6} adds 8 sites per period; a hexagon move (one site of the path replaced by three, inside the private
 shell) adds 2. So every larger length of the right parity is reached.
*Proofs of (F1)–(F3).* (F1): in the quadrant Y, Z > 0 the bonds ±t1 = ±(1,1,1), ±t2 = ±(1,−1,−1) change ρ = Y + Z by ±2
and keep α; ±t3 = ±(−1,1,−1), ±t4 = ±(−1,−1,1) change α = Y − Z by ±2 and keep ρ. An A-site uses +t_j, a B-site −t_j, so at
an A-site both rungs have ΔX = +1 and both steps ΔX = −1, at a B-site the opposite. The other quadrants are images
under Y → −Y or Z → −Z, which permute the t_j up to the sign of the x-component. (F2) follows: a rung up from a site
with ε = +1 reaches a site with ε = −1, whose steps have ΔX = +1, and so on; the four sites of a period are the
corners of a unit square in the (ρ/2, α/2)-plane. (F3): inside a quadrant consecutive steps have ΔX = −ε, +ε, …;
at a bend site with Z = 0, Y > 0 (a B-site, X = x) the two neighbours of equal ρ are reached by −t1 (X = x−1, in Z < 0)
and −t3 (X = x+1, in Z > 0), and on the Z > 0 side the curve continues on {x, x+1}, on the Z < 0 side on {x−1, x}: a shift
by one; the other three bends are symmetric and shift in the same rotational sense [CHECKED].
Status: by hand, in short form — every step is asserted by the builder, and the m = 20 run above exercises all of them in the dense case
(1006 wires, 70 levels, 5 769 155 sites in stages A–B, pairwise disjoint).

*Larger run* [CHECKED]: m = 80, four bins (items 2,6 | 8 | 4,4 | 2,2,4), five separators: chain of 941 724 monomers,
1 352 480 H–H bonds = 2N − 2m², verified; tether slacks 6, 18, 28, 38, 48 (entry) and 72, 66, 60, 54, 48 (exit) ≤ Σ* = 112.

**Near-field Lemma (checkpoint 20) [computer-assisted].** For every even m ≥ 80, every K ≥ 1 and every packing,
with slots, separators and chains placed as in §10.2/§10.4 (in particular J, R, C ≥ 20), phase A of the construction
succeeds: (N1) the frame links P^3, P^6, P^10 exist inside skin 1 and avoid the caps of the slot sites and the caps
and second column sites of all bulk run ends; (N2) every cap whose second column site is used by a frame link has
a neighbouring unused column ("borrowed"); (N3) second-row sites along X-plane edges are not bulk run ends;
(N4) the tethers exist, in pairwise different skins, on no linker column, with slacks at most 18K + 30 < Σ* (the
shortest ones have σ_e(1) = 6, σ_e(k) = 10k − 2 for k ≥ 2, σ_x(k) = 14K + 22 − 6k [CHECKED K ≤ 6]); (N5) no near-field P lies on the column of a linker cap.
Proof.
 *Locality.* The bulk cover near a site is determined by a ball of radius 4 (radius of the patch near a vertex).
 A P^3 link is a unique path. A frame link is found by a fixed search among the paths of its length inside skin 1
 that start at the cap of its first H, so it depends on what lies within 11 bonds; a borrowed column is chosen
 among the neighbours of the cap. All rules are covariant under lattice translations.
 *Classes of places.* Up to translation along an edge (and, between sizes, the transfers of 5.6) there are finitely
 many kinds of places: the neighbourhoods of V_a, V_b, V_c with the slots that fall inside them; a generic 2-slot on
 e1 and the last one; a generic 6-slot on e2; a separator, a chain boundary and a link on the track; the ring
 corners and ring cuts. The cover and the slot pattern are periodic along e1 (period 6 zigzag steps), along e2
 (period 10) and along the track (period 4), and a neighbourhood of a vertex is the same for all m (T-x, T-y, T-z).
 [CHECKED, slotsig.py, m = 80, K = 6: within distance 9 the skin-1 picture is the same at the 2-slots 3, 4, 5, 6; at
 the 6-slots 1 … 6; at the separators 2 … 6. Slots 1, 2 and the last 2-slot, the first 6-slot, the first and the
 last separator are the special places.] So an instance with K ≥ 7 contains no kind of place that does not occur
 for K = 6, and an instance with larger even m none that does not occur for m = 80 or 82.
 *The checks.* For m = 80 and m = 82 and each K = 1, …, 6 the builder constructs the whole near field and asserts
 (N1), (N2), (N3) and (N5) [CHECKED, sweepK.sh: all twelve pass]; (N5) needs only this, because frame links and
 P^3 links stay in skin 1, where a column has just its first two sites, caps are dangling sites (never on another
 column, §10.7 "Columns"), and tethers are confined to column-free sites by construction.
 *(N3)* holds because along an X-plane edge the inner neighbour d of each edge site is a damaged end whose two
 surface neighbours are second-row sites, and the clockwise rule of 10.4.1 joins d to one of them, always on the
 same side: away from the vertices every second-row site is claimed exactly once (near the vertices: the checks).
 *(N4), explicitly.* Triangle coordinates on the F'-bilayer of skin j: a surface site is (a, b, c) with a, b, c ≥ 0
 the distances to the sides over e2, e3, e1 (a + b + c = m − 2 + 2j); a sub-surface site with coordinates γ is bonded
 to γ − e_1, γ − e_2, γ − e_3. The column of the cap of the site (a, b, c) of F' passes skin j at (a+j, b+j, c) and at
 the sub-surface site (a+j, b+j, c+1). Hence rows b ≤ j−1 and rows a ≤ j−1 carry no column at all, and rows c = 0, 1
 carry only columns of e1-sites and of second-row sites along e1, none of which is a linker column ((N3); e1 has
 no linker cap on F'). In each of these rows consecutive surface sites have a common sub-surface neighbour in the
 same row, so each row is a path.
 Entry tether k (skin j = k+1): from the cap of the slot's b-site up its (own or borrowed) column to skin j; along
 row c = 1 towards V_a until b = j−1; along row b = j−1 until next to the column of the separator's first b-site,
 which sits in row b = j; down that column. The row c = 1 is crossed only by columns of slots nearer to V_a, which
 stop in lower skins; row b = j−1 is crossed by nothing.
 Exit tether k (skin K+2+k): up the column of the separator's second b-site; along row b = j−1 towards V_c; around
 the corner into row a = j−1; along it until next to the column of the exit slot's b-site (row a = j); down.
 Counting bonds: both columns cost 2(j−1) each, the rows cost twice the number of steps, a few bonds connect; the
 entry route is at most 2·3k + 4(k+1) + 3 = 10k + 7 longer than taut, the exit route at most 2(5K+5) + 4(2K+3) + 8 =
 18K + 30. (The reduction uses the shortest path inside these rows; its length for K ≤ 6 is given in (N4).) ∎
 *The two inductive steps, checked by machine* [CHECKED, nfinduct.py; picture = which sites are H, near-field P (with
 its kind) or bulk run end; tethers excluded, they are treated explicitly]:
 – size: for K = 6, each of the 26 731 near-field sites of the instance m = 82 has a 5-ball whose picture is the
 translate, by one of the ten region transfers of 5.6, of a 5-ball of the instance m = 80: no exception;
 – number of bins: for m = 80, each of the 25 463 near-field sites of the instance K = 7 has a 5-ball that is a
 translate (along e1, e2 or the track, by the slot and separator periods) of a 5-ball of the instance K = 6: no
 exception.
 What "computer-assisted" means here: the induction over m and K rests on the locality of the rules (argued above)
 and is confirmed by machine for one step in each direction; it is not a formal proof-assistant verification.
 The finite checks themselves are complete and reproducible.

### 10.8 The theorem and what its proof rests on (checkpoint 20)

**Theorem.** The following problem is NP-complete: given a word s ∈ {H,P}* and an integer k, is there a
self-avoiding walk on the tetrahedral (diamond) lattice carrying s with at least k pairs of H's on adjacent sites?
(Counting or not counting pairs that are consecutive in s differs by a constant of s.)

*Proof.* The problem is in NP. Reduce from bin packing with unary numbers: K bins of capacity B, items s_1 … s_n,
Σ s_i = KB. Build the word of §10.2 and put k = 2N_m − 2m². Its length is polynomial in KB and it is computed in
polynomial time by running the packing-independent part of the construction (bulk cover, frame, tethers, columns,
prescribed linker lengths).
 (⇐) If some fold has k H–H bonds, there is a packing: §10.3, using Theorem 5 and (O1)–(O7) of §5.
 (⇒) If there is a packing, the fold of §10.4/§10.7 has H-set Oct(m), hence exactly k bonds (5.1): Bulk Lemma
 (10.4.1), Near-field Lemma and Far-field Lemma (10.7). ∎

| Ingredient | Kind of proof |
|---|---|
| Theorem 3, Corollary 4, Theorem 5 (bound; only the octahedron attains it) | by hand, complete (§4, §5.1–5.5) |
| (O1)–(O7), region transfers | by hand, complete (§5.6) |
| Only-if direction | by hand, complete (§10.3) |
| Columns pairwise disjoint; margins column-free; tether routes | by hand (§10.7) |
| Bulk Lemma | computer-assisted: explicit local rules; finite checks + transfers (10.4.1) |
| Near-field Lemma | computer-assisted: finite checks at m = 80, 82, K ≤ 6; induction over m and K by locality, each step confirmed by machine once (nfinduct.py) |
| Far-field Lemma | by hand, short form (three disjointness arguments from (F1)–(F3)); its construction run in full on a dense instance |
| End-to-end evidence | 55 + 12 instances; one string folded for three packings; all folds checked by an independent verifier |

**Honest status.** Every step of the proof is now written, and nothing is known to be missing. But two lemmas are
computer-assisted (the induction in the Near-field Lemma is argued from locality and confirmed by machine for one
step in each direction), the constants of §10.2 are far too large to test the complete
construction with them (the tests use the same construction with small constants), and nobody else has read any of
it. Until it has been checked independently it should be called a proof with computer-assisted parts awaiting
verification, not an established theorem.

## 11. Superseded designs (for the record)

* Staples and ports (checkpoints 5–7): separators hung on odd runs H^7/H^9 ending at single skipped sites. Gap:
 the imbalance identity fixes only the number of odd runs with Min ends, so long bulk runs can take the ports and a
 staple can sit elsewhere; the separators are then not pinned. Its demo fold (m = 26, 45 500 bonds) is valid.
 Useful by-products that are proved: imbalance identity #(odd runs with Maj ends) − #(odd runs with Min ends) = m;
 taut tethers lie in one sheet over the small face and must cross, hence the slack of 2 in the tether lengths.
* Row-walls on a face (checkpoint 4): nothing forces the walls. Dropped.

## 12. Literature check

Web searches found the cubic (Berger–Leighton) and square-lattice (Crescenzi et al.) proofs and many heuristic
papers on triangular/FCC lattices; I found no published NP-hardness proof for the HP model on the diamond or FCC
lattice and no statement of Theorem 3. The search was not exhaustive.

## 13. Code (bundle HP_tetrahedral_code.tar.gz)

To reproduce the main checks (from the directory code/; Python 3, no packages needed):
* python3 tight2.py 260 ; python3 lastparts.py 110 — the lemmas of §5.3. python3 tetcoords.py — §5.6 and Lemma T.
* python3 canon.py 20 40 — the bulk cover; python3 arms.py 20 — columns.
* python3 build3.py 40 6 "[[2,4],[6],[2,2,2]]" 8 — a complete fold (3 bins); then python3 verify_fold.py <coords file>.
* one string, three packings: see the commands in §10.7 (arguments "ITEMS;ASSIGN", mode natural, then mode pad:…).
* python3 build3.py 20 4 "[[2,2]]" 6 nochain 0 natural nochain20 ordered — every bulk run linked separately, ordered far field.
* ./sweep3.sh — 55 instances.

diamond.py, oct.py, geom.py — lattice, octahedron, faces/edges/dangling sites; relax.cpp, pdp.cpp, onesided.py,
checks1.py, checks2.py, brute10.py — §4–5; surf.py — motifs; bars.py, bars2.py — bar decomposition; adv.py — link
table (O4); coordfacts.py — (O7); pin5.py — exact pinning check; fol.py, canon.py, canon_patches.py — the canonical bulk cover (10.4.1); certify.py, bulktable.py, sigcheck.py,
halfspace.py — its proof checks; tight2.py, lastparts.py — checks of §5.3; tetcoords.py — checks of §5.6; arms.py — columns (10.7); shells.py — far-field level curves; sweep3.sh — sweep of build3.py; sweepK.sh, slotsig.py, nfinduct.py — Near-field Lemma; faru.py — avenues and the length-adjusting detour of the Far-field Lemma; regiontransfer.py — region transfers; lines.py, extents.py — structure of the cover (completion of the Bulk Lemma); star_route.py, onesided2.py, lift.py — checks for the route plan (10.6);
bent.py, bent4.py, bent_period.py — earlier greedy version; bulkscan.py, topbil.py — further evidence; bulk.py — bulk cover by max-flow and flips;
**build3.py — full fold of the final design (10.7), with packing-independent string; build2.py — earlier builder; verify_fold.py — independent verifier.**
Older: tether.py, pin.py … pin4.py, match.py, demo_check.py, build.py (staple design).

---

## 14. Checkpoint 22 (14 Nov 2026, 09:58) — ERRATUM for Lemma F(D) (padding), audit in progress

**Defect (found by external audit, confirmed).** Old step D of Lemma F (far field, proof doc §8.5) used only gates of
sign +1, so for a fixed linker the increase is 2 + 2r + 8d: ONE residue class mod 8, not "every even number ≥ 4".
My script `faru.py` "confirmed" the false claim because it pooled the increases over four positions of s_a.
Reproduced with `code/faru2.py` (fixed s_a): old construction gives only E ≡ 0 or 6 (mod 8).

**Facts on A\* = A((+,+),u,α\*), A\*\* = A((+,+),u,α\*+4)** (all machine-checked for fixed s_a, 32 cases, faru2.py):
- gate = site g of A\* with α = α\*+2; outer neighbour g⁺ = site of A\*\* with X(g⁺) = X(g) − ε(g); g ~ g⁺.
- gates come in adjacent pairs (rung): sign +1 at X = p, sign −1 at X = p+1, period 4 in X.
- s_a = A_a has α = α\*; last sign-(+1) gate p < a has a − p ∈ {2,3} (2 if ε(s_a)=+1, 3 if ε(s_a)=−1).
- detour D(g_0,g_1): A\* back from s_a to g_0, g_0⁺, A\*\* forward to g_1⁺, g_1, A\* forward to s_b; simple lattice path;
  extra sites **E = 2 + 2(X(s_a) − X(g_0)) + ε(g_0) − ε(g_1)**.

**Repair 1 (mine, verified by faru2.py):** let g_1 = first gate of either sign beyond s_a, g_0 any gate below s_a →
every even E ≥ 4 exactly once.

**Repair 2 (revised manuscript received from the user, file `astra/proof_astra.md`, "Parts D–E"):** same-sign detours
(two classes mod 8: 2r, 2r+2) plus an optional hexagon detour at q = p+8 (adds 4) → every even E ≥ 6; and an explicit
uniform bound with h_0 = X_F = H := 20m+21, U_0 := H+4w+8, β ≤ 280m+240w+406, **L\* := 1000(m+w+1)+6**, w = |W| = twice
the number of long linkers (word-determined). Hand audit of the diff (130 changed lines; base file hash identical to
my 08:42 version): arithmetic and case analysis of Part D correct; Part E bound correct given Parts A–C as written.
STILL TO DO: own script for Repair 2; end-to-end builder run that follows the text of §8.5 literally with these constants.

Status reminder: this concerns Lemma F(D)/(E) only. Bulk Lemma and Lemma N remain computer-assisted, checked only by
my own scripts; the F(D) episode shows such self-written checks can confirm a false statement.

## 15. Checkpoint 23 (14 Nov 2026, 10:08) — the revised Lemma F(D)/(E) is CORRECT; adopted as working manuscript

Working manuscript `HP_tetrahedral_proof.md` := revised file received from the user (base hash = my 08:42 version;
130 changed lines, all read) + my marked notes (status paragraph, end of §8.5, §9 parity reason, Appendix A rows).
Old version kept as `HP_tetrahedral_proof_v1_0842.md`.

**What the revision does** (Parts D–E of Lemma F):
- crossing pair p (sign +1 at X = p, sign −1 at p+1), last one below a = X(s_a); r = a − p ∈ {2,3};
- long detour between two crossing sites of the SAME sign: v_0 = p+δ−4d, v_1 = p+δ+4: adds 2 + 2(r−δ) + 8d;
- optional hexagon at q = p+8 (rung A_q A_{q+1} → A_q, B_{q−1}, B_q, B_{q+1}, B_{q+2}, A_{q+1}): adds 4;
- so Δ = 2 + 2(r−δ) + 4η + 8d: every even Δ ≥ 2r, in particular every even Δ ≥ 6;
- constants: h_0 = X_F = H = 20m+21, α* = max|α_c|+6 ≤ 2m+10, levels ≤ H+4(w−1), slabs H+60n, U_0 = H+4w+8,
  U_max = H+6w+8; β ≤ 2[(U_max+2)+(2H+60w+3)+(4U_max+4)]+(60w+13)+1 = 280m+240w+406; **L\* = 1000(m+w+1)+6**.

**My audit of it.** By hand: all arithmetic, the interval separation of the two detours, the avoidance paragraph,
and the bound of Part E are right (uses near field ⊂ O_{2K+3}, which over-estimates my skins ≤ 2K+2 — harmless).
By machine (my scripts, so same caveat as always):
- `code/faru3.py`: 28,512 padded paths, both phases, every even increase 6…400, gap 47: all pass.
- `code/build3.py ... text:resid | text:Lstar | text:bound` (new far-field mode that follows Parts A–E literally and
  asserts every inequality of Parts B, C, E):
  - m=24 (w=112): L ∈ {137006, 137007} for all 56 linkers, 7,693,861 monomers, verify_fold OK, optimal;
  - m=24 and m=25, increases 6…36: all 8 combinations (r,δ,η) occur (m even gave r=3, m=25 gave r=2);
  - m=28, K=2, lengths 280m+240w+412(+1): items 2,2,2,2 in 3 packings → one string of 2,888,336 letters; items 2,2,4
    in 2 packings → one string of 2,814,326 letters; all folds verify_fold OK, optimal.
- new assertions: item caps ⊂ potential caps; consecutive track a-sites differ by (2,0,2) (sublattice-preserving),
  so all potential item caps lie on one sublattice ⇒ linker parities do not depend on the packing (§9).

**Thin spot of MINE found on the way (now patched in §9):** the old text asserted "plus one where the parity requires
it; none of this depends on a packing" without a reason. Reason now written and asserted.

**Unchanged status:** Bulk Lemma (§8.3) and Lemma N (§8.4) are computer-assisted with my own programs only; nobody
else has run them (the reviewer did not have the code archive). Theorem 5 / Claim U: reviewer reports independent
finite checks of Lemma 5.1 (1,251,058 cases) and of Claim U for m = 1..9. Not read by me: the FCC notebook v5 that
came with the same message (not needed for this question).

## 16. Checkpoint 24 (14 Nov 2026, 10:30) — second audit: three gaps (Bulk Ω, Lemma N coverage, Lemma T). IN PROGRESS

**All three witnesses are real** (verified):
- Lemma T (clean form): m=11, R=0, R'=10, v=(0,30,10): depth below small face (−,+,+) goes 1 → −3 (`code/transfer_cov.py`).
  Error in my proof: case "no other axis eligible" needs 2m ≥ R+2R'+10, case "both eligible" needs m ≥ R+5; the
  stated 4m ≥ 3R+2R'+24 gives neither. Corrected hypothesis: **m ≥ R + R' + 5, R' ≥ 1**. The clean form is used nowhere.
- Bulk Ω: at the −y vertex (= origin) P={(0,4,0),(1,3,−1)}, Q={(−1,3,1)} (row), R={(2,4,−2)} exist for m=30,47 with
  α(P)=2m−7, X̂=1; Q row |X̂|=2; α(R)=2m−9, X̂=4 (`code/certify_lex.py witness`). With K=10^4, C=10^9, P is a local max
  for m ≥ 50004 and both walks (rows with |X̂| = 2,5,9,13,…; α = 2m−9, 2m−11, …) do not escape in 6 steps.
- Lemma N: m = (K+2)(18K+48)B + 38K + 100 ≥ 336 (correct), bases m=80,82 used ad hoc J1=8, CAP=4; "K → K+1 adds one
  slot" false for §6 constants; frame links are found by a DFS that also avoids EARLIER links → not a radius-5 rule.

**Repairs designed**
1. Ω lexicographic: (2,|X̂|,0) row; (1,α,X̂) α>0; (0,X̂,0) α<0. For m ≤ 100 identical order to the old numbers
   (|X̂| ≤ 4m < 10^4, 10^4·2m < 10^9), so all old checks carry over; re-run with tuples: `certify_lex.py cert 9 60`.
   Uniformity: comparisons use only class, differences of α and of X̂ → invariant under the vertex-ball translations
   (near ±y: α>0 for all sites within 43 if m ≥ 46; near ±z: α<0; near ±x: Y,Z unchanged).
2. **Lemma T' (coverage of region transfers), proved + checked** (`transfer_cov.py`, D=2,3,4, R up to 7, both parities):
   F := 4D+12. For every lattice site p with all depths ≥ −R rel. Oct(M) (M=m+2, same centre), if 4M ≥ 12D+46+R one of
   x: τ=4sg(p_x)e_x [faces s_x=−sg far]; y: τ=4sg(Y)e_y [faces s_y=−sg(Y) far, |Y| ≥ D+5]; z alike;
   r: τ=(0,2sg Y,2sg Z) [|Y|,|Z| ≥ D+3, six other faces far] applies, and then the D-ball of p−τ in Oct(m) is the
   translate (depths of non-far faces equal; far ones ≥ 2D+3 in both; signs of Y,Z equal).
   Proof: S=2M−1+R ≥ A+B+C. x fails ⇒ B+C−A ≥ 2M−1−F. Case B ≤ D+4 ⇒ z applies; case |Z| ≤ D+4 ⇒ y applies;
   else r, and if r fails (A+|B−C| ≥ 2M−1−F) then max(B,C) ≥ 2M−1−F and y resp. z applies (needs 4M ≥ 3F+R+3).
3. Lemma N: plan = (i) elementary vertex-ball and edge-ball lemmas (no induction over m); (ii) cover locality lemma
   (patches within max-norm 8 of vertices, rule merges radius ≤ 4); (iii) slot links defined as TRANSLATES of one
   explicit path (no search), vertex links by search inside vertex windows; (iv) generalized family of layouts
   containing §6; (v) atlas of windows; tests K=1..8 at m=80,82 with J ≥ 12.

## 17. Checkpoint 25 (14 Nov 2026, 10:46) — second audit: repairs WRITTEN into the proof document

Manuscript `HP_tetrahedral_proof.md` (previous state kept as `HP_tetrahedral_proof_v2_1008.md`). Lemma F(D–E) untouched.

**Lemma T (§5.6).** Corrected hypothesis m ≥ R+R'+5 (R' ≥ 1), new 3-case proof; declared unused. New **Lemma T′**
(coverage, 4M ≥ 12D+46+R, options x/y/z/r, full proof) and **Lemma E** (vertex boxes: m ≥ D+2; edge boxes: D ≥ 3,
2D ≤ i ≤ 2m−2−2D, same parity). Checks: `transfer_cov.py` (T′ at five (D,R,M), both parities; corrected T at 6 minimal sizes).

**Bulk Lemma (§8.3).** Ω := (2,|X̂|,0) / (1,α,X̂) / (0,X̂,0) lexicographic. New **Lemma K** (cover locality: 4 bonds +
patches within max-norm 8; rule 3 is simultaneous — canon.py lines 25–26). Claim 1: all m ≥ 88 via T′ (D=26) from
m=88, 89 (`claim1.py`: valid, shortest path 6); NOT covered: 61 ≤ m ≤ 87 except 64,68,…,84 and 80, 82.
Claim 2: parts (i)–(iv): comparisons are translation-invariant in vertex boxes, m ≥ 50; ten maxima certified for
every m=9..60 with the lexicographic order (`certify_lex.py cert 9 60`: ALL OK, max 6 steps).
Still resting on old finite checks + hand argument: (S2) (extents.py, lines.py), table (a) for all m (S3, S4).

**Lemma N (§8.4).** Family 𝓕: m even ≥ 80, m ≥ 5K+40, J ≥ 14 even, R ≥ 15 odd, items ≥ 4, C even. §6 ⊂ 𝓕.
Frame links are now EXPLICIT (Appendix C): Λ_2 for every 2-slot, Λ_6 for every 6-slot, four vertex links; borrowed
columns: both caps of each 2-slot anchor + cap of e1[2]; everything else own arm. Fact found: the builder's DFS
returns exactly these for every slot (even next to the vertices), K=1..8, m=80, 82.
Proof = (1) objects explicit, (2) V1/V2 with radii 11 / 20,12,4 / 16, (3) classes by Lemma E/K, (4) coverage by
T_8 = (80; 8; 14; 4; 15; one item per bin) and T_cut = (80; 2; 14; 8; 43; items 4,4), pairs listed, monotone in the
number of slots, (5) beyond skin 1 by Lemma C and (N4), (6) machine: `sweepN.sh` → `sweepN_J14.log`, 18 runs OK.
The old radius-5 comparison (nfinduct.py) is withdrawn as a proof step.
Weak spots I know of: (N4) (tethers) not re-audited now; (3c) "types by construction" relies on build3.py doing
what the text says; (N3) near vertices only through the test runs.

**Honest overall status.** Proved by hand now: T, T′, E, K, (i)–(iv), reduction (1)–(5). Computer-assisted with my
own programs: Claim 1 bases, Claim 2 finite checks, (S2)–(S4)/table (a), T_8 and T_cut. Not independently verified.

## 18. Checkpoint 26 (14 Nov 2026, 11:20) — THIRD audit received (6 findings). Work started.

Findings (file from user, 11:17): (1) tether lengths: word uses σ_e(1)=6 (273 P's for K=B=1, m=336) but the rows stated
in Lemma N need 279 (σ_e(k)=10k+2); build3.py searches a broader corridor than the text → choose ONE definition.
(2) Lemma N(2): "non-frame objects within max-norm 2 of owner" false: a PPP needs radius 3 from any single edge site
(example boundary 22, m=336: H(45,671,−625) P(46,672,−626) P(47,673,−625) P(48,672,−624) H(47,671,−623)).
(3) sweepN.sh ran with "chain" (bulk paths joined by PPP), §6 uses unchained bulk runs. (4) bulk table: 74 entries is
the union over sizes/phases; per size: m=14: 10, m=15: 19, m ≥ 24: 39. (5) Bulk Lemma says m ≥ 9 but 61–87 partly
uncovered. (6) Corollary 4: (4/3)(m²−1/2)^{3/2} ≤ (4/3)m³−m+1/(8m) is false; use ≤ (4/3)m(m²−1/2) = (4/3)m³−(2/3)m < N_m.

Plan: (6) text fix. (5) run claim1 for all 61..87, else restrict. (3) rerun T_8, T_cut with nochain. (2) owner of a
PPP := its first H, radius 3; cutoffs 20/13/6; boxes 9; pairs up to 3 boundaries apart; recheck coverage list.
(1) define tethers as the explicit row routes of the text; code builds exactly those; formula for lengths; local
coordinate script valid at m=336. (4) per-parity table; coverage by (T-r)/Lemma E(b)+K.

### Checkpoint 27 (14 Nov 2026, 11:40) — third audit, progress
- (1) TETHERS: text's rows adopted as THE definition; `build3.py` now builds them explicitly (`tether_explicit`), old BFS
  no longer used. Exact lengths (proved by counting row steps, 2 sites per unit step):
  entry k (skin j=k+1): 2(2j−2) columns + 2 (sub-surface ends) + 1 + 2(3k+1) [row c=1] + 2j_k [row b=j−1] = **2j_k+10k+5**, σ_e(k)=10k+2;
  exit k (skin j=K+2+k, κ=K+1−k): 4j−4 + 3 + 2(m−2−j_k) + 2(5κ+4) = **2(m−2−j_k)+14K+25−6k**, σ_x(k)=14K+22−6k.
  Entry point of row c=1: surface (m−3−3k+j, 3k+j, 1) (borrowed column = column of F'-site (m−3−3k,3k,1)).
  `code/tether_local.py` (independent of builder, no octahedron): reproduces the auditor's coordinates for m=336
  (279 P's) and passes for (K,B) = (1,1),(1,2),(1,252),(2,1),(3,2),(9,1),(10,3),(12,1) and the test layouts.
- (2) PPP radius: asserted ≤ 3 from each of its two H's (and the H's are at max-norm 2). Cutoffs to become 20/13/6.
- (3) nochain: T_8 passes unchained (22,993 linker caps); `sweepN.sh` switched to nochain, running → `sweepN_nochain.log`.
- (4) `bulktable2.py 14 60` running: per-size counts 10, 19, 26, 33, 39 (m=18), 39…; union 74 from m=19.
- (5) `claim1.py` for all remaining sizes 61..87: all valid → Claim 1 holds for every m ≥ 9.
- STILL TO DO: word-only test for packings in unchained assembly; manuscript edits (Cor. 4, scope, table claim,
  Lemma N (2)–(4) with radius 3, (N4) explicit, §6 σ's); README/zip. Finding (4) "prove coverage of table (a) for all
  m" will NOT be fully proved today — to be flagged as unresolved.

### Checkpoint 28 (14 Nov 2026, 11:58) — third audit: repairs written (manuscript v4; previous kept as `…_v3_1050.md`)
Done in text + code: Cor. 4 bound; σ_e(k)=10k+2, σ_x(k)=14K+22−6k (§6, (N4) with exact count and erratum);
Lemma N (2)–(4) rewritten (owners; PPP radius 3; cutoffs 20/13/6; boxes 16/9; vertex kind ≤ 40 / ≤ 25; pairs up to
3 boundaries apart; sequences of T_8, T_cut); (6) unchained; Claim 1 all m ≥ 9; bulk table per parity (39 each).
Runs: `sweepN_nochain.log` (T_8, T_cut, K=1..8 at m=80, 82, and m=92 K=10 — unchained, explicit tethers, PPP radius);
`audit3_words_folds.log` (m=92 K=10: two assignments → same word, 114,596,622,238 letters, w=30,848; chained complete
folds m=24 and m=28 ×3 with explicit tethers: verify_fold OK, one string); word-only m=28 unchained: 3 and 2
packings → same word (631,042,941 and 629,942,691 letters); `tether_local.py`; `claim1_61_87.log`; `bulktable2_14_60.log`.
**UNRESOLVED (stated in §1 and §8.3 of the manuscript):**
 U1. Table (a) of Claim 2 for ALL m: (S3)–(S4) is an incomplete argument (line classification for all m; case split
     between transfers (r) and (y)/(z); boundary cases; X̂ of neighbours). Without it, acyclicity of the bulk cover
     for m ≥ 336 is evidence-based (validated directly only for m ≤ 89, 92, 96, 100). Concrete next steps: a compiled
     validator for m = 336, 512, 534 (evidence), and a written proof of (i)–(iii).
 U2. No complete fold of an actual reduction instance can be built here (m ≥ 336: > 5·10^7 H's; unchained far field
     ~10^11 letters already at m=92). At those sizes only local coordinate checks (tether_local.py).
 U3. Lemma N reduction (1)–(5) is a hand argument; (3c) relies on build3.py placing things as the text says.

### Checkpoint 29 (14 Nov 2026, 12:10) — plan to close U1 (table (a) for all m). WRITE-UP IN PROGRESS
Goal: for every even m ≥ 62 each segment P with two joints farther than 12 from all vertices has the same (key, value)
as a segment at size 60 (odd: 59); table(60) satisfies A′, B′, C′ (bulktable2). Steps:
(G1) far joints are rule-3 merges (d,w) within 2 bonds of a damaged-edge zigzag; P is a complete foliation piece.
(G2) rung at an A-site has ΔX = στ, at a B-site −στ; bend sites: Z = 0 ⇒ B-site, Y = 0 ⇒ A-site; so the X-range of a full
     V-piece is a function of (x_A of one arm, quadrant, bend plane) only — not of α, m.
(G3) end near X-plane edge ⇒ |X| ≤ 4 on P ⇒ other end cannot be near a Z-plane edge unless within ~6 of a ±y vertex.
(G4) both ends near a damaged Z-plane edge ⇒ α > 0, ≤ 9 sites (|Z| ≤ 4 at the ends); Y-bending would be at the ±x vertex.
(X-far) ends at index ≥ 20 from the vertices: per-end translation τ_q = (0; Δ|Y|, Δ|Z|) = (m−60+Δα/2, m−60−Δα/2), Δα ≡ 0 (4):
     sublattice-preserving, maps arm(x, α′) of size 60 to arm(x, α) of size m and the two quadrant faces onto each other
     ⇒ (Lemma K) same joint, same neighbour end data; reference α′: |α′| ≡ |α| (4), 6 ≤ |α′| ≤ 60, or α′ = α if |α| ≤ 5.
(X-near) an end at index < 20 from the vertex V it surrounds ⇒ P and neighbours ⊂ Box(V,30) ⇒ Lemma E(a).
(Z) Lemma E(b)+K with D = 16 at index ≥ 32 (choose i′ mod 4 to match α mod 4); else Box(V,44) ⇒ Lemma E(a), D = 48.
Machine sanity check of (G3),(G4) and "Z-type ⇒ row": code/segstruct.py.

### Checkpoint 30 (14 Nov 2026, 12:35) — U1 closed on paper: Proposition A in §8.3 (manuscript v5; v4 kept as `…_v4_1130.md`)
Proposition A (m ≥ 81; references m_0 ∈ {59,60} for class X, m_1 ∈ {79,80} for class Z): (A1) rungs/bends ⇒ X-values of a
line depend only on bend plane, side, x_A; (A2) classes X / Z, no mixed, class Z ⇒ α>0, ≤ 9 sites; (A3) class X,
|α| ≤ 2m−38: per-end translation τ_q; (A4) class X, |α| > 2m−38: Box(V,43), Lemma E(a); (A5) class Z: Box(e[i],21),
Lemma E(b) for 42 ≤ i ≤ 2m−44, else Box(V,63), Lemma E(a).
Self-check found one error in my first draft of (A5): a neighbour of a class-Z segment need NOT have |Z| ≤ 5
throughout; correct bound t ≤ 8 steps beyond the bend ⇒ radius 17/21, which forced the larger reference sizes 79, 80.
Machine: bulktable2 18 19 79 80 (tables of 79, 80 identical to those of 19, 18; A′B′C′ true), segstruct 40 41 59 60 79 80.
STATUS: every step now has a written proof or a named finite computation. NOT error-free by any guarantee:
Proposition A, Lemma N (rewritten), tethers (explicit) are all from today and unaudited. Sizes 61–80 of (a) are
covered by the direct validation of the whole cover (m ≤ 89), not by tables.

### Checkpoint 31 (14 Nov 2026, 12:25) — FOURTH audit received (5 items); plan
(1) Lemma N pairs: "owners of boundaries d apart are 2d apart" false (b-PPP owner e3[2i+1], a-PPP owner e3[2i]; a cut has
    two cap owners e3[2i], e3[2i+2]); cuts 4 boundaries apart (items [4,4,4]) have cap owners 6 apart. FIX PLAN: drop the
    enumeration by boundary types; objects on e3 = {Acap(p even), PPPa(p even), Tcap(p odd), PPPb(p odd)}, each attached to
    H-sites; by (3a) intersection of two objects depends only on (types, δ = p′−p); machine: universal table of ALL
    type pairs for 0 ≤ δ ≤ 6; claim: only objects sharing an attachment site intersect, and those never coexist.
(2) Bulk caps have owners in X_m: separate "bulk objects"; bulk–bulk by Lemma C; bulk vs edge-owned objects by the
    surroundings clause (cover in Box(u,16)/(u,9)); borrowed columns; tethers by (N3), Lemma R(d).
(3) (A5): "|Y| ≥ 12" false (witness Y = −11, α = 11 at m=336). FIX: no general bound needed: interior case |Y| ≥ i−11 ≥ 31;
    near ±x the translation keeps Y, Z so α is unchanged; near ±y α is huge.
(4) Word: make §6 = builder order (left filler before items), one L* = 1000(m+w+1)+6 everywhere, trailing P stated;
    packing-free generator (mode "wordspec") and exact RLE comparison with packings.
(5) Tests: T_8, T_cut, T_3 = (80; 1; 14; 12; 49; items 4,4,4), K=B=1 and K>8 (local scripts), items of different sizes.

### Checkpoint 32 (14 Nov 2026, 12:45) — fourth audit repaired (manuscript v6; v5 kept as `…_v5_1150.md`; ledger = Appendix D)
- Lemma N (β) on e3: universal table, 50 type/offset combos (δ ≤ 6), meeting only: (Acap,PPPa,0), (PPPa,Acap,2), (PPPa,PPPa,2),
  (PPPb,PPPb,2), (PPPb,Tcap,0), (PPPb,Tcap,2) — all share an H; "one object per H" ⇒ disjoint in every layout.
- (1′) bulk caps separated. (A5) bound removed. §6 = builder's word; L* everywhere; trailing P stated.
  CAUGHT WHILE WRITING: I first wrote the parity rule backwards; correct: L_i = L*+1 iff the two H's are on the SAME sublattice.
- Tests (`audit4_tests.log`): T_8, T_cut, T_3 unchained OK; items [4,8,8,4], m=80, K=2: packing-free RLE word byte-identical
  to three packings (264,787,518,214 letters, L* = 23,053,006).
- Open obligations: Appendix D, end (code–text agreement partly assumed; no complete fold at m ≥ 336; own local
  checks at actual sizes = tethers only; §6, §7, §8.1, §8.2, Lemma F(A–C) unaudited; vertex neighbourhoods by tests only).
