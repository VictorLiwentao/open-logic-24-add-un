# Scheme GS: findings (round 3)

Status (2026-11-19). Written by one AI agent (Claude). No referee has read it. No Lean check.
The problem stays open. Scheme GS is **undecided**: it is not realised in ZFC here, and it is
not refuted.

Every claim has one label.

- PROVED: a full proof is in this file. It uses only the Lean-checked results of the
  repository and standard textbook facts, which are named.
- SKETCH: an argument with gaps. Do not use it.
- FAILED: an approach that does not work, with the reason.
- CONJECTURE: a guess.

## 0. Summary

1. The reduction "GS implies add(UN) ≤ |I|" is correct. Lemma F is correct. (Section 2.)
2. Condition (b) of GS is not needed. A direct Fubini argument shows that each piece Z_i is
   universally null. Condition (b) can also always be arranged. So GS is the statement GS⁻
   of Section 3, which has no code set Y and no injectivity. (PROVED.)
3. The self-reference is not needed either. The codes may cover the initial segments of any
   fixed non-null set X⁰ in place of Z. (Lemma T, PROVED.) So GS is one instance of "a
   non-null set of size non(N) is a union of |I| universally null sets", and it has no
   advantage over the other instances.
4. GS with add(N) keys holds when non(N) = cof(N), and GS with cf(non(N)) keys always holds.
   (PROVED. Nothing new for the problem.) So ZFC does not refute GS outright.
5. GS with θ keys implies su ≤ θ and sn ≤ θ for two new cardinals su and sn (Section 4).
   These statements are formally stronger than add(UN) ≤ θ. Whether ZFC proves
   sn = add(N) is a question about null sets only. I could not decide it. If sn > add(N) is
   consistent, then GS with add(N) keys fails in ZFC. (Section 9.)
6. Obstacle O3 is the only real obstacle. Section 6 states it in an exact form: a recursion
   with keys in F can always be continued until Z is not null, and then every piece is
   universally null provided all proper initial segments were universally null. If
   add(N) < add(UN), every run passes through a null initial segment that is not
   universally null. (PROVED.)
7. Four no-go lemmas for natural ways to build Z are PROVED in Section 7.
8. No new upper bound for add(UN) by a classical invariant was found.

## 1. Notation and known results used

λ is the product measure on 2^ω. N is the null ideal. UN is the universally null ideal.
κ = non(N). "Admissible measure" means a finite Borel measure that vanishes on singletons.
"Positive compact set" means a compact set of positive λ-measure.

For a Borel set B ⊆ 2^ω × 2^ω write B^z = {x : (x,z) ∈ B} (vertical section) and
B_x = {z : (x,z) ∈ B} (horizontal section).

H is a Borel subset of 2^ω × 2^ω such that every section H_c = {x : (x,c) ∈ H} is null and
every null set lies in some H_c. (In the repository H lives on 2^ω × ω^ω. A Borel
isomorphism moves the codes to 2^ω.)

Used as known (Lean-checked in the repository):

- (K1) non(UN) = non(N). So every set of size < κ is universally null.
- (K2) add(N) ≤ add(UN). More precisely `measure_sUnion_null_of_mk_lt_add`: for every finite
  Borel measure μ on 2^ω, a union of fewer than add(N) μ-null sets is μ-null.
- (K3) Lemma 1 (a family F of size ≤ add(N) that no slalom of width h localises), for every
  width h.
- (K4) Lemma 2 (coding lemma) with its proof, and Lemma 3 (transfer).
- (K5) Grzegorek's theorem, Theorem A, Theorem B.

Standard facts used: Tonelli's theorem; a Borel map between Polish spaces is continuous on a
dense G_δ set; every null set lies in a null G_δ set; cf(non(N)) ≥ add(N).

## 2. The checks that were asked for

### 2.1 The reduction "GS implies add(UN) ≤ |I|" — PROVED (correct)

Statement of GS as in `ideas.md`. Z = {z_α : α < κ} is not null. y_α = Φ_{i_α}(z_α).
(a) {z_β : β < α} ⊆ H_{y_α}. (b) Φ_i is injective on Z_i = {z_α : i_α = i}.

Proof. Step 1: Y = {y_α : α < κ} is universally null. Let μ be admissible on the code space.
By Tonelli, ∫ μ{y : x ∈ H_y} dλ(x) = ∫ λ(H_y) dμ(y) = 0. So C = {x : μ{y : x ∈ H_y} = 0} is a
co-null Borel set. Z is not null, so some z_β is in C. For α > β, (a) gives z_β ∈ H_{y_α}. So
{y_α : α > β} is μ-null. The set {y_α : α ≤ β} has size < κ, so it is μ-null by (K1).
Step 2: each Z_i is universally null by Lemma 3, because Φ_i is Borel, injective on Z_i, and
Φ_i[Z_i] ⊆ Y. Step 3: Z = ⋃_i Z_i is not null, so it is not universally null. ∎

Remarks.

- The codes y_α need not be distinct. The points z_α need not be distinct.
- The regularity of κ is not used.
- The universality of H is not used. Only "every section H_y is null" is used.

### 2.2 Lemma F — PROVED (correct)

Let φ be Borel on a Borel set D, X ⊆ D, P ∈ UN, φ[X] ⊆ P, and every fibre X ∩ φ^{-1}(p)
universally null. Then X ∈ UN.

Proof. Let μ be admissible. Put ν(E) = μ(D ∩ φ^{-1}[E]). Let A be the countable set of atoms
of ν and ν_c(E) = ν(E ∖ A). Then ν_c is admissible. Take a Borel B ⊇ P with ν_c(B) = 0. Let
x ∈ X. Then φ(x) ∈ P ⊆ B. If φ(x) ∉ A, then x ∈ D ∩ φ^{-1}[B ∖ A], a Borel set of μ-measure
ν(B ∖ A) = ν_c(B) = 0. If φ(x) ∈ A, then x lies in one of the countably many sets
X ∩ φ^{-1}(p), p ∈ A ∩ P, and each is μ-null. So μ*(X) = 0. ∎

### 2.3 The obstacles O1–O4 of `ideas.md`

- O1 is correct when cf(κ) > |I|. For a fixed w and key i the set
  {α : Z_α ⊆ H_{Φ_i(w)}} is an initial segment of κ. If it is all of κ, then Z is null.
  PROVED.
- O2: the sentence is true, but it is not the relevant fact. Constant keys must cover the
  chain of initial segments Z_α, not every small set. Constant keys work if and only if
  |I| ≥ cf(κ) (Proposition 5.2). The conclusion "admissibility must depend on z_α" is correct
  when |I| < cf(κ).
- O3 is correct. It is the only real obstacle. See Section 6.
- O4: the initial segments can be kept null. Stop the recursion at the first stage where Z
  is not null (Proposition 6.1). The true difficulty is that these null initial segments
  have size ≥ κ and need not be universally null. The condition stated in O4 is a special
  case of Lemma R+ below. In Lemma R+ the set D need not lie inside Z.

## 3. GS without condition (b) and without self-reference

### Lemma R (relative Grzegorek–Recław lemma) — PROVED

Let B ⊆ 2^ω × 2^ω be Borel with λ(B^z) = 0 for every z. Let T ⊆ 2^ω be not null. Let
W ⊆ 2^ω. Suppose that for every t ∈ T the set W ∖ B_t is universally null. Then W ∈ UN.

Proof. Let μ be admissible. By Tonelli, ∫ μ(B_x) dλ(x) = ∫ λ(B^z) dμ(z) = 0. So
C = {x : μ(B_x) = 0} is co-null and Borel. T is not null, so there is t ∈ T ∩ C. Then
W ⊆ B_t ∪ (W ∖ B_t). The first set is μ-null. The second is universally null. ∎

### Lemma R+ — PROVED

Let B be as in Lemma R and W ⊆ 2^ω. Suppose that for every co-null Borel set C there is
D ⊆ C with |D| < add(N) such that W ∖ ⋃_{d ∈ D} B_d is universally null. Then W ∈ UN.

Proof. Let μ be admissible and C = {x : μ(B_x) = 0} as above. Take D ⊆ C as in the
hypothesis. ⋃_{d ∈ D} B_d is a union of fewer than add(N) μ-null sets, so it is μ-null by
(K2). ∎

Lemma R+ covers the "Fubini step" of obstacle O4. Sanity check: neither lemma produces a
non-null set, and neither produces a large set without a hypothesis.

### Corollary 3.1 (condition (b) is redundant) — PROVED

Assume Z = {z_α : α < κ} is not null, Φ_i (i ∈ I) are Borel maps on Borel sets D_i into the
codes, and for every α there is i_α with z_α ∈ D_{i_α} and {z_β : β < α} ⊆ H_{Φ_{i_α}(z_α)}.
Then every Z_i = {z_α : i_α = i} is universally null. Hence add(UN) ≤ |I|.

Proof. Put B_i = {(x,z) : z ∈ D_i, x ∈ H_{Φ_i(z)}}. It is Borel and B_i^z = H_{Φ_i(z)} is
null. Apply Lemma R with T = Z and W = Z_i. Let t = z_β. If z ∈ Z_i and z = z_α for some
α > β with i_α = i, then z_β ∈ H_{Φ_i(z)}, so z ∈ (B_i)_{z_β}. So W ∖ (B_i)_{z_β} ⊆
{z_α : α ≤ β}, a set of size < κ, which is universally null by (K1). ∎

Second proof. Replace Φ_i by Φ'_i(z) = (Φ_i(z), z) and H by H' = {(x,(c,z)) : (x,c) ∈ H}.
Then Φ'_i is injective, H' has null sections, every null set lies in a section of H', and
(a) still holds. So (b) can always be arranged, and the original reduction applies.

Call the statement of Corollary 3.1 **GS⁻(θ)** when |I| = θ. So GS(θ) and GS⁻(θ) are
equivalent, if GS may use any Borel set H' with null sections that contains every null set
in a section. In words: Z is not null, Z is well-ordered in type κ, and θ Borel maps
z ↦ N^i_z into the null sets are given such that every z has a key i with pred(z) ⊆ N^i_z.

The same proof gives a version of any length. Let Z = {z_α : α < θ'} be not null, with keys
as above, and assume every proper initial segment {z_α : α ≤ β} is universally null. Then
every Z_i is universally null. (PROVED, same proof.)

### Lemma T (self-reference is removable) — PROVED

Let X⁰ = {x_ξ : ξ < κ} be not null. Let Ψ be a Borel map from a Borel set D into the codes.
For z ∈ D let ρ(z) be the least ξ with x_ξ ∉ H_{Ψ(z)}. (It exists because H_{Ψ(z)} is null.)
Let W ⊆ D be such that |{z ∈ W : ρ(z) ≤ ξ}| < κ for every ξ < κ. Then W ∈ UN.

Proof. Lemma R with T = X⁰ and B = {(x,z) : z ∈ D, x ∈ H_{Ψ(z)}}. For t = x_ξ the set
W ∖ B_{x_ξ} = {z ∈ W : x_ξ ∉ H_{Ψ(z)}} is contained in {z ∈ W : ρ(z) ≤ ξ}. ∎

So the following scheme GS_X also gives add(UN) ≤ |I|: a non-null set X⁰ of size κ, a
non-null set Z, Borel maps Ψ_i, and a choice of key i(z) for z ∈ Z such that for all i and ξ
fewer than κ points z have i(z) = i and ρ_i(z) ≤ ξ. GS is the case X⁰ = Z. I see no case
where GS_X is easier or harder than GS. In both, the pieces have size ≤ κ and the difficulty
is that Z must be non-null.

## 4. What GS implies: two cardinals

Definitions.

- **su** is the least size of a family 𝒰 ⊆ UN such that ⋃𝒰 is not null and |⋃𝒰| = κ.
- **sn** is the least size of a family 𝒢 ⊆ N such that ⋃𝒢 contains a non-null set of size κ.

### Proposition 4.1 — PROVED

(1) add(N) ≤ sn ≤ su and add(UN) ≤ su.
(2) su ≤ cf(κ) and sn ≤ cov(N).
(3) su ≤ d.
(4) If non(N) = cof(N), then su = add(N).
(5) GS(θ) implies su ≤ θ.

Proof. (1) A non-null union of null sets needs add(N) sets. UN ⊆ N gives sn ≤ su. A non-null
set is not universally null, so add(UN) ≤ su. (2) Let Z be non-null of size κ, enumerated in
type κ. The initial segments along a cofinal sequence of length cf(κ) have size < κ, so they
are universally null by (K1), and their union is Z. For sn ≤ cov(N), intersect Z with the
members of a cover of 2^ω by cov(N) null sets. (3) If d ≥ cf(κ) use (2). If d < cf(κ) ≤ κ,
the note's proof of Theorem A gives d universally null sets W_h, each of size κ, with
non-null union. The union has size κ. (This uses the note's proof, not the Lean proof. I
did not re-check the note's proof.) (4) The sets X_f in the proof of Theorem B have size
≤ cof(N) = κ and there are ≤ add(N) of them. (5) By Corollary 3.1 the sets Z_i are
universally null, and Z has size κ. ∎

So GS with add(N) keys would prove su = add(N). This is formally stronger than
add(UN) ≤ add(N). I do not know whether the two are equivalent. The gap is this: a non-null
union of add(N) universally null sets need not have a non-null subset of size κ.

Open (not decided here): does su ≤ θ imply GS⁻(θ)? The problem is that the map which sends
a point of a piece to a code of its set of predecessors need not be Borel on that piece.

### Lemma 4.2 (Sierpiński criterion) — PROVED

Call S κ-Sierpiński if |S| = κ and every subset of S of size κ is not null. Let θ < cf(κ).
If Z is covered by θ null sets, then Z has no κ-Sierpiński subset.

Proof. Let S ⊆ Z ⊆ ⋃_{i<θ} G_i with G_i null and S κ-Sierpiński. Each S ∩ G_i is a null
subset of S, so it has size < κ. Since θ < cf(κ), |S| < κ. Contradiction. ∎

Consequences (PROVED, immediate).

- If θ < cf(κ) and GS(θ) holds, there is a non-null set of size κ with no κ-Sierpiński
  subset.
- If X⁰ is κ-Sierpiński, no GS(θ)-witness with θ < cf(κ) is a subset of X⁰. More generally,
  if e_j (j < θ') are Borel injections and θ·θ' < cf(κ), no witness lies inside
  ⋃_j e_j[X⁰]. (By Lemma 3, e_j^{-1}[Z_i] ∩ X⁰ is universally null, so it has size < κ.)
- So GS cannot be realised "inside an arbitrary given non-null set". The set Z must be
  built, and its non-nullness cannot come from an injective non-singular transfer of a
  Sierpiński-type set.

## 5. Where GS holds

### Proposition 5.1 — PROVED

If non(N) = cof(N), then GS holds with |I| ≤ add(N), with the keys φ_f of the coding lemma.

Proof. Let F be as in Lemma 1 for the width h of Lemma 2. Let (K_α)_{α<κ} list positive
compact sets such that every set that meets all K_α is not null (as in the proof of
Theorem B; here cof(N) = κ). Recursion on α < κ. The set {z_β : β < α} has size < κ, so it
is null. Choose a code c_α with {z_β : β < α} ⊆ H_{c_α}. Lemma 2 for (K_α, c_α) gives a
slalom S. Some f_α ∈ F is not localised by S. Lemma 2 gives z_α ∈ K_α ∩ dom(φ_{f_α}) with
φ_{f_α}(z_α) = c_α. Then Z meets every K_α, so it is not null, and (a) holds. Corollary 3.1
finishes. ∎

This is Corollary (a) of the note again. It shows that GS is consistent.

### Proposition 5.2 — PROVED

GS holds with |I| = cf(κ) and constant keys. With constant keys, GS(θ) holds if and only if
θ ≥ cf(κ).

Proof. Let Z be non-null of size κ, enumerated in type κ, and (α_ξ)_{ξ<cf(κ)} cofinal in κ.
Let c_ξ be a code of a null set that contains {z_β : β < α_ξ}. For α < κ let i_α be the
least ξ with α < α_ξ and Φ_ξ ≡ c_ξ. Conversely, if θ < cf(κ) and the keys are constant, one
key is used cofinally, and then Z ⊆ H_c for one c. ∎

So a refutation of "GS with add(N) keys" needs a model of
add(N) < cf(non(N)) ≤ non(N) < cof(N). Such a model has c ≥ ℵ_3.

## 6. Obstacle O3 in exact form

### Proposition 6.1 (run the recursion until Z is not null) — PROVED

Let F and the maps φ_f be as in Proposition 5.1. There are a limit ordinal θ' < c⁺, points
z_α, functions f_α ∈ F and codes c_α (α < θ') such that, with Z_α = {z_β : β < α}:

(i) Z_α is null for α < θ' and Z_{θ'} is not null;
(ii) Z_α ⊆ H_{c_α} and z_α ∉ H_{c_α};
(iii) φ_{f_α}(z_α) = c_α.

Moreover, if every Z_α with α < θ' is universally null, then add(UN) ≤ add(N).

Proof. Recursion. If Z_α is null, choose a code c_α with Z_α ⊆ H_{c_α} and a positive
compact set K_α disjoint from H_{c_α}. As in Proposition 5.1 get f_α ∈ F and
z_α ∈ K_α ∩ dom(φ_{f_α}) with φ_{f_α}(z_α) = c_α. The points are distinct, so the recursion
stops at some θ' < c⁺ with Z_{θ'} not null. θ' is a limit ordinal, because adding one point
to a null set gives a null set. For the last sentence apply the general-length version of
Corollary 3.1: for β < θ' the set {z_α : α ≤ β} = Z_{β+1} is universally null. So each
piece {z_α : f_α = f} is universally null, and their union Z_{θ'} is not null. ∎

### Corollary 6.2 — PROVED

Assume add(N) < add(UN). Then in every run of the recursion of Proposition 6.1 there is a
least α < θ' such that Z_α is not universally null. This α is a limit ordinal with
cf(α) ≥ add(UN) and |α| ≥ κ, and Z_α is null.

Proof. If no such α exists, Proposition 6.1 gives add(UN) ≤ add(N). The least α is a limit,
and Z_α is the union of cf(α) universally null sets, so cf(α) ≥ add(UN). |α| ≥ κ by (K1). ∎

So the keys are never the problem. A key in F and a new point exist at every stage. The
scheme succeeds if some run stays universally null until it becomes non-null. If
add(N) < add(UN), no run does. GS is
the special case θ' = κ, where "stays universally null" is free because the initial
segments are small. In the open case θ' = κ would need a non-null set after κ < cof(N)
steps.

Why the Fubini argument cannot be repaired at the bad stage α of Corollary 6.2. Z_α is
λ-null and not ν-null for some admissible ν. The codes c_β code λ-null sets. Fubini for λ
needs a point of Z_α in a λ-co-null set and there may be none. Fubini for ν needs the sets
H_{c_β} to be ν-null, and ν is not known during the recursion. A code can handle countably
many measures at once (replace λ by λ + Σ 2^{-n} ν_n), but not all. FAILED.

### Lemma 6.3 (uniform coding lemma) — PROVED

Let h*(n) = 2^n·h(n) with h as in Lemma 2. For every positive compact K there is a slalom
S*_K of width h* such that for every f with f(n) ∉ S*_K(n) for infinitely many n,
φ_f maps K ∩ dom(φ_f) onto 2^ω.

Proof. In the proof of Lemma 2 the number n_0 depends only on K. The sets R_{n,k} and
W_{n,k} depend only on c|n. By induction the sets T^m(s) for m ≤ n depend only on c|(n−1),
and S(n) depends only on c|n. Write S^σ(n) for this set when σ = c|n, and put
S*_K(n) = ⋃_{σ ∈ 2^n} S^σ(n). It has at most 2^n·h(n) elements. If f(n) ∉ S*_K(n) for
infinitely many n, then for every c, f(n) ∉ S^c(n) for infinitely many n, and Lemma 2 gives
w ∈ K ∩ dom(φ_f) with φ_f(w) = c. ∎

### Corollary 6.4 — PROVED

(1) There is F* ⊆ ω^ω with |F*| ≤ add(N) such that every positive compact set is mapped
onto 2^ω by φ_f for some f ∈ F*.
(2) Let 𝒦 be a family of fewer than cof(N) positive compact sets. There is one function f*
such that φ_{f*} maps K ∩ dom(φ_{f*}) onto 2^ω for every K ∈ 𝒦. All these points lie in the
null set dom(φ_{f*}).

Proof. (1) Lemma 1 for the width h*. (2) Suppose every f is localised by some S*_K, K ∈ 𝒦.
Put ε_n = 2^{-n}/h*(n). By Step 1 of Lemma 1 every null set G lies in limsup_n O_{f(n)} for
some f with λ(O_{f(n)}) ≤ ε_n. Take K with S*_K localising f. By Step 2 of Lemma 1,
G ⊆ G*_K = limsup_n ⋃{O_k : k ∈ S*_K(n), λ(O_k) ≤ ε_n}, a null set. So {G*_K : K ∈ 𝒦} is
cofinal in N and has size < cof(N). Contradiction. So some f* escapes every S*_K infinitely
often. dom(φ_{f*}) is null because Σ_n α_n < ∞ (Borel–Cantelli). ∎

Meaning of (2). In the open case a recursion of length κ < cof(N) asks for points
z_α ∈ K_α that decode a code c_α. All such requests, for all codes at once, can be met
inside one null set, with one Borel key f*. This key is in general not in F. So the
requests "z_α ∈ K_α and z_α decodes c_α" do not force Z to be non-null. Any proof that Z
is non-null must use the restriction to keys in F, or a transfer from a fixed non-null set.
This is O3.

(1) says that each positive compact set contains, for some f ∈ F*, a copy of any given set
of codes on which φ_f is injective. I found no use of this beyond Theorem B.

## 7. No-go lemmas for natural ways to build Z

### Lemma 7.1 (Luzin-type seeds) — PROVED

Let e_i : 2^ω → 2^ω (i ∈ I) be Borel maps with |I| < non(N). There is a null G_δ set N such
that e_i^{-1}[N] is comeager for every i.

Proof. Each e_i is continuous on a dense G_δ set C_i. Let Q_i ⊆ C_i be countable and dense.
E = ⋃_i e_i[Q_i] has size < non(N), so it is null. Take a null G_δ set N ⊇ E. The set
C_i ∩ e_i^{-1}[N] is a G_δ subset of C_i (continuous preimage), so it is G_δ in 2^ω. It
contains Q_i, so it is dense. So it is comeager. ∎

Corollary 7.2 — PROVED. Let L ⊆ 2^ω be such that |L ∖ C| < κ for every comeager C. Then
L ∈ UN. If |I| < cf(κ) and e_i (i ∈ I) are Borel maps, then ⋃_i e_i[L] is null.

Proof. Let μ be admissible. A countable dense set is μ-null, so it lies in a μ-null dense
G_δ set C. L ∖ C has size < κ, so it is μ-null, and L ∩ C is μ-null. So L ∈ UN. For the
second part take N from Lemma 7.1. Then ⋃_i e_i[L] ⊆ N ∪ ⋃_i e_i[L ∖ e_i^{-1}[N]], and the
last set has size < κ. ∎

So the universally null sets of size κ that finite support iterations give for free (sets
of Cohen reals) cannot be the pieces of a GS-witness through fewer than cf(κ) Borel maps.

### Lemma 7.3 (common carrier) — PROVED

Let σ_i (i ∈ I) be finite Borel measures on 2^ω, each singular to λ, with |I| < cov(M).
There is a λ-null G_δ set N with σ_i(2^ω ∖ N) = 0 for all i.

Here cov(M) is the least number of meager sets that cover ω^ω. Fewer than cov(M) dense open
subsets of a space homeomorphic to ω^ω have a common point.

Proof. Let 𝒪_n be the countable set of clopen O ⊆ 2^ω with λ(O) ≤ 2^{-n}. The space
𝒞 = ∏_n 𝒪_n (discrete factors) is homeomorphic to ω^ω. For c ∈ 𝒞 put
N_c = ⋂_m ⋃_{n>m} c(n). It is a G_δ set, and it is λ-null because λ(⋃_{n>m} c(n)) ≤ 2^{-m}.
For i ∈ I and m, k ∈ ω let D_{i,m,k} = {c : σ_i(⋃_{n>m} c(n)) > σ_i(2^ω) − 1/k}. It is open:
a finite part of the union already has measure > σ_i(2^ω) − 1/k. It is dense: σ_i lives on
a λ-null Borel set S. Given a finite sequence s and n > max(m, |s|), take an open U ⊇ S
with λ(U) ≤ 2^{-n} and a finite union O of cylinders inside U with
σ_i(O) > σ_i(2^ω) − 1/k. Extend s by empty sets and put O at place n. There are fewer than
cov(M) sets D_{i,m,k}, so some c lies in all of them. Then σ_i(⋃_{n>m} c(n)) = σ_i(2^ω) for
all m, so σ_i(N_c) = σ_i(2^ω). ∎

This is the dual form of "Lemma N" in `agent-logs/round2.json`.

Corollary 7.4 — PROVED. Let X ⊆ 2^ω with |X ∩ G| < κ for every null G. Let g_i (i ∈ I) be
Borel maps such that each image measure λ∘g_i^{-1} is singular to λ. If
|I| < min(cov(M), cf(κ)), then ⋃_i g_i[X] is null.

Proof. Take N from Lemma 7.3 for the image measures. g_i^{-1}[2^ω ∖ N] is null, so it meets
X in fewer than κ points. So ⋃_i g_i[X] ⊆ N ∪ (a set of size < κ). ∎

So a non-null set of size κ inside a union of add(N) null sets cannot be made from
Sierpiński-type sets (sets of random reals) by add(N) Borel maps when add(N) < cov(M). Note
also that an image g[X] of a non-null set X is never universally null unless the image
measure has atoms. So such images cannot be pieces of a GS-witness in any case.

### Lemma 7.5 (codes in a separate coordinate) — PROVED

If Y is null and Z ⊆ 2^ω × Y, then Z is null in the plane. So a point z_α cannot be a pair
(x_α, c_α) that is decoded by a projection, when the codes c_α form a universally null set.
The same holds for any Z of size κ whose projection lies in a set that has no non-null
subset of size κ.

Proof. Fubini for 2^ω × Y. For the last sentence the projection of Z has size ≤ κ, so it is
null. ∎

This is why the "graph trick" (make any assignment of codes Borel by adding the code as a
coordinate) does not help: the graph is universally null.

### Lemma 7.6 (directed devices need non(N) keys) — PROVED

Let 𝒫_i (i ∈ I) be families of non-empty subsets of 2^ω. Assume each 𝒫_i is directed
downward: any two members contain a third. Assume every positive compact set contains a
member of some 𝒫_i. Then |I| ≥ non(N).

Proof. Let 𝒦_i be the family of compact sets that contain a member of 𝒫_i. Finitely many
members of 𝒦_i have non-empty intersection, because 𝒫_i is directed. By compactness there
is x_i ∈ ⋂𝒦_i (any x_i if 𝒦_i is empty). Every positive compact set lies in some 𝒦_i, so it
contains x_i. So {x_i : i ∈ I} meets every positive compact set. So it is not null. ∎

Use. For a key i the sets P^i_α = {w : Z_α ⊆ H_{Φ_i(w)}} decrease with α. So no variant can
ask that a whole set P^i_α lies in a prescribed positive compact set, with fewer than
non(N) keys. The same holds for "cones" of a scale under a decoding map.

### Variants that were tried — FAILED

- Trees of codes, or compositions φ_g∘φ_f as keys. A point still has only add(N) codes. By
  Corollary 3.1 the code set plays no role, so a tree gives nothing that one level does not
  give.
- Length cof(N) with repeated points. This is Proposition 6.1. It needs the initial segments
  to be universally null.
- Codes for several measures. See after Corollary 6.2.
- Pairs of codes (c, p) with p in a fixed Grzegorek set P, so that every piece is
  universally null at once by Lemma 3. Then the recursion can run for |P| steps only. It
  reaches a non-null set for sure only if |P| ≥ cof(N). This is Theorem B.
- Transfer of non-nullness from a fixed non-null set X⁰ by fewer than add(N) non-singular
  Borel maps g (so that g^{-1} of a null set is null). The maps can be absorbed into the
  keys. The scheme becomes GS for X⁰ itself. Lemma 4.2 shows that this can fail for a
  given X⁰.
- Transfer by singular maps (maps into the null domains of the keys). Then the preimage of
  a null set need not be null, and nothing is transferred. Hitting every positive compact
  set by such maps is a leaf device. The round-2 results say that it needs at least cov(M)
  maps, and d for the marker leaves.

## 8. Sanity constraints

(S1) No argument here shows that fewer than add(N) universally null sets have a non-null
union. Corollary 3.1 with |I| < add(N) has a false hypothesis: the Z_i would be universally
null, their union would be universally null by (K2), and Z is not null.

(S2) No argument here gives a universally null set of size cof(N) in ZFC, or a non-meager
universally null set in ZFC. I checked the claim about Goto's paper in the text extraction
of arXiv:2607.12936v4 (file `flat.txt` in the folder `open-logic-24`, outside this
repository). The abstract and Theorem 3.3 say: in the countable support iteration of
PT_{f,g} of length ω_2 over CH, every universally null set lies in the reals of an
intermediate model and has size ≤ ℵ_1. The introduction says that this model has
d = ℵ_1 < non(M) = cof(M) = c = ℵ_2. Then non(N) = ℵ_1 by Grzegorek's theorem, and
cof(N) ≥ cof(M) = ℵ_2. So in that model every universally null set has size
< cof(N) and is meager, and add(N) = add(UN) = non(N) = ℵ_1. So the claim in the task is
right, given Theorem 3.3. I read the statement of Theorem 3.3 and the start of its proof. I
did not check the proof. The paper is a preprint and says that AI tools were used for its
proofs.

In that model GS holds trivially (Proposition 5.2). A variant of length cof(N) with
distinct codes forming a universally null set is false there. Proposition 6.1 does not
claim it.

## 9. A test question and a test model

The cardinal sn does not mention universally null sets.

**Question Q.** Does ZFC prove sn = add(N)? That is: is there always a non-null set of size
non(N) that is covered by add(N) null sets?

- Yes if cov(N) = add(N), if cf(non(N)) = add(N), or if non(N) = cof(N) (Proposition 4.1).
- If the answer is no in some model, then GS with add(N) keys fails in that model, by
  Proposition 4.1 (5). The same holds for every variant whose witness has size non(N).
  This would refute GS as a ZFC scheme. It would not decide add(UN) there.
- If the answer is yes in ZFC, the proof would give the first half of a GS-witness.

CONJECTURE. sn > add(N) is consistent. Candidate model: a finite support iteration of
random forcing of length ω_2 over a model of add(N) = ℵ_1 and cof(N) = c = ℵ_3 (for example
after adding ℵ_3 Cohen reals to a model of GCH). I expect add(N) = b = ℵ_1,
cov(N) = non(M) = cov(M) = non(N) = ℵ_2 and d = cof(N) = ℵ_3 there. These values were not
checked against a source. They are the pattern of Theorem 4 of Mejía's paper
arXiv:1211.5209 as quoted in `agent-logs/round2.json`.

SKETCH of the evidence. In such a model a set of ℵ_2 reals is non-null only if it is
unbounded in the iteration. The natural unbounded sets are Borel images of the Cohen reals
and of the random reals of the iteration. Corollary 7.2 shows that ℵ_1 Borel images of the
set of Cohen reals have a null union. Corollary 7.4 shows the same for ℵ_1 singular Borel
images of the set of random reals, since cov(M) = ℵ_2. A similar argument seems to work for
points that are random for a measure coded by a Cohen real: the set of codes d for which a
fixed null G_δ set carries the measure ν_d is a G_δ set, and it is dense if the null set
carries ν_d for a countable dense set of d. I did not find a non-null set of size ℵ_2
inside a union of ℵ_1 null sets in this model. I have no proof that there is none. A proof
must handle arbitrary names for reals, not only these three kinds.

Note on Goto's Theorem 5.18. Its witnesses are sets X_β = ⋂_α [σ_α]^∞, and the point of X_β
outside a given null set is a Cohen real inside a tree T chosen for that null set. One
point is used for each tree. There are cof(N) trees. So the proof gives add(UN) = add(N) in
such models by unions that may have size cof(N). It does not give su = add(N).

## 10. Verdict

(a) GS is undecided. It is equivalent to GS⁻ (no condition (b), no code set). It holds when
non(N) = cof(N) or cf(non(N)) = add(N). In the open case it needs a non-null set of size
non(N) that is a union of add(N) universally null sets (su = add(N)). No construction of
such a set was found, and no model without one was found.

(b) GS has no advantage over the plain statement su = add(N): by Lemma T the codes can
refer to any fixed non-null set, and by Corollary 3.1 no injectivity is needed.

(c) Most promising next step: decide Question Q in the model of Section 9. A proof of
sn > add(N) there refutes GS and all variants with witnesses of size non(N). It would also
show that any ZFC proof of add(UN) ≤ add(N) must use unions of size > non(N), as Theorem B
does.

(d) No new bound add(UN) ≤ (classical invariant) was found. The bounds su ≤ min(d, cf(non(N)))
and sn ≤ cov(N) are about the new cardinals only.

## 11. What was not checked

- No referee and no Lean check for anything in this file.
- Proposition 4.1 (3) relies on the note's written proof of Theorem A (sizes of the sets
  W_h), not on the Lean proof.
- The cardinal values in the model of Section 9 and the PT_{f,g} values are quoted, not
  verified. The proof of Goto's Theorem 3.3 was not checked.
- Whether su ≤ θ implies GS⁻(θ), and whether add(UN) = add(N) implies su = add(N), are open.
- The literature was not searched for su, sn, Lemma R or Lemma 6.3. Lemma R is close to
  Recław's theorem on sets well-ordered by a Borel relation and may be known.
- Plan Z of `ideas.md` (translates) was not studied.
