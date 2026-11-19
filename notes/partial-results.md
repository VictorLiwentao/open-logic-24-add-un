# Partial answers to Goto's Question 6.3 on add(UN)

Status (2026-11-16, evening). All results below were produced by AI agents in one session.
Each proof was checked by two independent AI referees told to assume it was wrong. Theorem B
was found twice, by two agents working separately with different codings. It passed five
referee reports in all, and the coordinating AI (Claude) also checked its proof line by line. No human expert has checked anything here. No formal proof exists.

Update (2026-11-19). The new half of Theorem B, add(UN) ≤ add(N) from a universally null set
of size cof(N), now has a Lean proof, including Lemmas 1, 2 and 3. The Lean proof changes some
steps of the proof below. See `formalisation-theorem-b.md`.

Second update (2026-11-19). Theorem A and the cited facts (F3, Grzegorek only) and (F4) now
have Lean proofs too, so Theorems A and B and Corollaries (a), (b) and the Lean form of (c)
hold with no hypothesis. The Lean proof of Theorem A changes the construction below, and the
cited facts are proved by other routes. See `formalisation-theorem-a-and-cited.md`. Recław's
theorem, (F1) and (F2) are not formalised.

Source question: T. Goto, *Forcing and cardinal invariants of universally null sets*,
arXiv:2607.12936v4, Question 6.3. Is add(N) < add(UN) consistent, or does ZFC prove
add(N) = add(UN)?

This note does **not** settle the question. It proves equality in a large class of models
and narrows where a counterexample can live.

## Results

- **Theorem A (ZFC).** add(UN) ≤ d.
- **Theorem B.** If there is a universally null set of cardinality cof(N), then
  add(UN) = add(N).
- **Corollaries of B.**
  - (a) If non(N) = cof(N), then add(UN) = add(N). This covers non(N) = c.
  - (b) If c ≤ ℵ_2, then add(UN) = add(N).
  - (c) If add(N) < add(UN), then c ≥ ℵ_3, every universally null set has size < cof(N),
    b < cof(N), and add(N) < add(UN) ≤ min(d, cf(non(N))) ≤ non(N) < cof(N).

So the question is open only when non(N) < cof(N) and c ≥ ℵ_3. Countable support iterations
that force c ≤ ℵ_2 (for example length ω_2, proper iterands of size ≤ ℵ_1, over CH) cannot
give a counterexample. The Mathias, Laver, Miller and Sacks
models all satisfy add(UN) = add(N).

Notation: `λ` is the product measure on `2^ω`, `N` the null ideal, `UN` the universally null
ideal (outer measure zero for every atomless finite Borel measure).

Facts used, all in Goto's paper (checked against the text; the original papers of Grzegorek
and Recław were not read):

- (F1) UN is invariant under Borel isomorphisms (Lemma 5.11).
- (F2) Claim 5.5.1: the graph of any function on a UN set is UN in the plane.
- (F3) Grzegorek: there is a UN set of size non(N). Recław: there is one of size b.
- (F4) add(N) ≤ add(UN) ≤ non(UN) = non(N) (Corollary 5.13, Proposition 5.4).

## Theorem B: proof

### Lemma 1 (non-localised family)

Let h : ω → ω∖{0}. A slalom of width h is a map S from ω to finite subsets of ω with |S(n)| ≤ h(n); it localises f ∈ ω^ω if f(n) ∈ S(n) for all but finitely many n. There is F ⊆ ω^ω with |F| ≤ add(N) such that no slalom of width h localises every member of F.

*Proof.* Let λ be the product measure on 2^ω. Put ε_n = 2^{-n}/h(n). Fix an enumeration (O_k)_{k∈ω} of the clopen subsets of 2^ω.

Step 1. Every null G ⊆ 2^ω is contained in limsup_n C_n for some clopen sets C_n with λ(C_n) ≤ ε_n. Proof: for each j pick an open O^j ⊇ G with λ(O^j) ≤ ε_j 2^{-j-1}, and write O^j as a disjoint union of cylinders [t^j_i], i < N_j ≤ ω. For fixed j choose 0 = i_0 < i_1 ≤ i_2 ≤ ... with i_r ≥ r and Σ_{i ≥ i_r} λ[t^j_i] ≤ ε_{j+r} 2^{-j-1} for r ≥ 1 (tails of a convergent series tend to 0). Let group r of j be {i : i_r ≤ i < i_{r+1}}; it is finite, and its cylinders have total measure ≤ ε_{j+r} 2^{-j-1} (for r = 0 this is the bound on λ(O^j)). Let C_n be the union of the cylinders in group n−j of j, over all j ≤ n. Then C_n is clopen and λ(C_n) ≤ ε_n Σ_j 2^{-j-1} ≤ ε_n. If x ∈ G then for each j, x lies in some [t^j_i], hence in C_n for some n ≥ j; so x ∈ C_n for infinitely many n.

Step 2. Let {G_ξ : ξ < add(N)} be null sets whose union is not null. By Step 1 choose f_ξ ∈ ω^ω with λ(O_{f_ξ(n)}) ≤ ε_n for all n and G_ξ ⊆ limsup_n O_{f_ξ(n)}. Let F = {f_ξ}. Suppose a slalom S of width h localises every f_ξ. Put D_n = ⋃{O_k : k ∈ S(n), λ(O_k) ≤ ε_n}. Then λ(D_n) ≤ h(n) ε_n = 2^{-n}, so G* = limsup_n D_n is null (Borel–Cantelli). Fix ξ and x ∈ G_ξ. For infinitely many n we have x ∈ O_{f_ξ(n)}, and for all large n we have f_ξ(n) ∈ S(n), hence O_{f_ξ(n)} ⊆ D_n. So x ∈ G*. Thus ⋃_ξ G_ξ ⊆ G* is null, a contradiction. ∎

### Lemma 2 (coding lemma)

Put μ_n = 4^{n+1}, α_n = 2^{-μ_n}, ρ_n = 2^{-μ_n-n}, h(n) = 2^{3μ_n+n}. Fix pairwise disjoint finite sets B_{n,k} ⊆ ω ((n,k) ∈ ω×ω) with |B_{n,k}| = μ_n + n, enumerated increasingly as b_{n,k}(0) < ... < b_{n,k}(μ_n+n−1). For w ∈ 2^ω say that w has a marker at (n,k) if w(b_{n,k}(j)) = 0 for all j < μ_n, and let msg_{n,k}(w) ∈ 2^n be i ↦ w(b_{n,k}(μ_n+i)). For f ∈ ω^ω let D(w,f) = {n : w has a marker at (n,f(n))}. Let dom(φ_f) be the set of w such that D(w,f) is infinite and for every i the bits msg_{n,f(n)}(w)(i), n ∈ D(w,f), n > i, are eventually constant; φ_f(w)(i) is that constant. Then dom(φ_f) is Borel and φ_f : dom(φ_f) → 2^ω is Borel. 

Claim: for every compact K ⊆ 2^ω with λ(K) > 0 and every c ∈ 2^ω there is a slalom S of width h such that for every f ∈ ω^ω with f(n) ∉ S(n) for infinitely many n there is w ∈ K ∩ dom(φ_f) with φ_f(w) = c.

*Proof.* Notation. A_{n,k} = {w : w has a marker at (n,k)}, R_{n,k} = A_{n,k} ∩ {w : msg_{n,k}(w) = c|n}, W_{n,k} = A_{n,k} ∖ R_{n,k}. These are clopen, λ(A_{n,k}) = α_n, λ(R_{n,k}) = ρ_n, λ(W_{n,k}) ≤ α_n, R_{n,k} ∩ W_{n,k} = ∅. Events that depend on disjoint sets of coordinates are independent. Put τ_n = Σ_{m>n} α_m (also for n = −1). Arithmetic: τ_{n−1} = τ_n + α_n; α_n ≤ τ_{n−1}; τ_n ≤ 2α_{n+1} = 2^{1−4μ_n} because μ_{m+1} ≥ μ_m + 1; hence (E) ρ_n τ_{n−1} ≥ ρ_n α_n = 2^{−2μ_n−n} ≥ 2^{2−4μ_n} ≥ 2τ_n, using 2μ_n ≥ n+2.

Definition of S. Choose n_0 ≥ 1 with 2τ_{n_0−1} ≤ λ(K). Put S(n) = ∅ for n < n_0. By recursion on n ≥ n_0 define, for every s ∈ ω^n, a closed set T^n(s) ⊆ K, and then S(n). Put T^{n_0}(s) = K. Given T^n(s') for all s' ∈ ω^n, let
 S(n) = {k : there is s' ∈ ω^n with λ(T^n(s') ∩ R_{n,k}) < (ρ_n/2) λ(T^n(s'))},
and for s = s'⌢k ∈ ω^{n+1} let T^{n+1}(s) = T^n(s') ∩ R_{n,k} if k ∉ S(n), and T^{n+1}(s) = T^n(s') ∖ W_{n,k} if k ∈ S(n). So T^n(s) = K ∩ E(s), where E(s) is a Boolean combination of events at blocks B_{m,s(m)}, m < n; E(s) depends only on coordinates in ⋃_{m<n,k} B_{m,k}.

Invariant: λ(T^n(s)) ≥ 2τ_{n−1} for all n ≥ n_0 and s ∈ ω^n. For n = n_0 this is the choice of n_0. Step: if k ∈ S(n), then λ(T^{n+1}(s)) ≥ 2τ_{n−1} − α_n = 2τ_n + α_n ≥ 2τ_n. If k ∉ S(n), then by definition of S(n), λ(T^{n+1}(s)) ≥ (ρ_n/2) λ(T^n(s')) ≥ ρ_n τ_{n−1} ≥ 2τ_n by (E).

Width: |S(n)| ≤ h(n). Fix n ≥ n_0, put ρ = ρ_n, θ = 2τ_{n−1}. Let k_1,...,k_N be distinct elements of S(n) with witnesses s_1,...,s_N; put E_j = E(s_j), T_j = K ∩ E_j, R_j = R_{n,k_j}. Then λ(T_j) ≥ θ and λ(T_j ∩ R_j) < (ρ/2)λ(T_j). Let Ξ = Σ_j 1_{E_j}·(ρ − 1_{R_j}). Then ∫_K Ξ dλ = Σ_j (ρ λ(T_j) − λ(T_j ∩ R_j)) > Σ_j (ρ/2) λ(T_j) ≥ Nρθ/2. The sets E_j depend only on coordinates in stage-m blocks, m < n; R_j depends only on B_{n,k_j}; the blocks B_{n,k_j} are pairwise disjoint and disjoint from all earlier blocks. Hence for j ≠ j' the functions 1_{E_j}1_{E_j'}, ρ − 1_{R_j}, ρ − 1_{R_j'} are independent and the last two have mean 0, so the cross terms of ∫Ξ² vanish and ∫Ξ² = Σ_j λ(E_j) ρ(1−ρ) ≤ Nρ. By Cauchy–Schwarz, ∫_K Ξ ≤ (∫Ξ²)^{1/2} ≤ (Nρ)^{1/2}. So Nρθ/2 < (Nρ)^{1/2}, i.e. N < 4/(ρθ²) = 1/(ρ_n τ_{n−1}²) ≤ 1/(ρ_n α_n²) = 2^{3μ_n+n} = h(n). So S(n) is finite with at most h(n) elements.

The point w. Let f satisfy f(n) ∉ S(n) for infinitely many n. For n ≥ n_0 put Q_n = T^n(f|n) ∖ ⋃_{m≥n} W_{m,f(m)}. Q_n is closed, and λ(Q_n) ≥ 2τ_{n−1} − Σ_{m≥n} α_m = τ_{n−1} > 0. Since R_{n,k} ∩ W_{n,k} = ∅, in both cases T^{n+1}(f|(n+1)) ⊆ T^n(f|n) ∖ W_{n,f(n)}, so Q_{n+1} ⊆ Q_n. By compactness pick w ∈ ⋂_{n≥n_0} Q_n. Then w ∈ K; w ∉ W_{m,f(m)} for all m ≥ n_0; and w ∈ R_{n,f(n)} for every n ≥ n_0 with f(n) ∉ S(n) (because w ∈ T^{n+1}(f|(n+1))). So D(w,f) is infinite. If n ∈ D(w,f) and n ≥ n_0, then w ∈ A_{n,f(n)} ∖ W_{n,f(n)} = R_{n,f(n)}, so msg_{n,f(n)}(w) = c|n. Hence for each i, every n ∈ D(w,f) with n > max(i,n_0) gives bit c(i). So w ∈ dom(φ_f) and φ_f(w) = c.

Borelness: dom(φ_f) is defined by countable quantifiers over clopen conditions, and each coordinate of φ_f is Borel on it. ∎

### Lemma 3 (transfer of universal nullness)

Let Δ ⊆ 2^ω be Borel, φ : Δ → 2^ω Borel, P ⊆ 2^ω universally null, and X ⊆ Δ such that φ[X] ⊆ P and φ is injective on X. Then X is universally null.

*Proof.* Let μ be an atomless finite Borel measure on 2^ω. Define the finite Borel measure ν(B) = μ(Δ ∩ φ^{-1}[B]). Let At = {c : ν({c}) > 0}; it is countable. ν_0(B) = ν(B ∖ At) is a finite Borel measure with no point masses, hence atomless. Since P is universally null there is a Borel B ⊇ P with ν_0(B) = 0, that is μ(Δ ∩ φ^{-1}[B ∖ At]) = 0. Now X ⊆ (Δ ∩ φ^{-1}[B ∖ At]) ∪ (X ∩ φ^{-1}[At]). The first set is μ-null. The second is countable because φ is injective on X and At is countable; it is μ-null because μ is atomless. So μ*(X) = 0. ∎

### Proof of Theorem B

add(N) ≤ add(UN) is Goto's Corollary 5.13 (in flat.txt). For the other inequality let h and (φ_f) be as in Lemma 2 and let F be given by Lemma 1 for this h; |F| ≤ add(N).

Let {G_β : β < cof(N)} be a cofinal family of null sets; we may take each G_β to be a G_δ. Its complement is an F_σ of measure 1, so it contains a compact K_β with λ(K_β) > 0. Any set X that meets every K_β is not null: if X were null, X ⊆ G_β for some β, but X ∩ K_β ≠ ∅ and K_β ∩ G_β = ∅.

Let P be universally null with |P| = cof(N) (take a subset of the given set) and let {c_β : β < cof(N)} list P without repetition. For each β let S_β be the slalom of width h given by Lemma 2 for (K_β, c_β). F is not localised by S_β, so there is f_β ∈ F with f_β(n) ∉ S_β(n) for infinitely many n. Lemma 2 gives w_β ∈ K_β ∩ dom(φ_{f_β}) with φ_{f_β}(w_β) = c_β.

For f ∈ F put X_f = {w_β : f_β = f}. Then φ_f[X_f] ⊆ P, and φ_f is injective on X_f: if w_β, w_β' ∈ X_f and φ_f(w_β) = φ_f(w_β'), then c_β = c_β', so β = β' because P is listed without repetition, so w_β = w_β'. By Lemma 3, X_f is universally null. The union of the X_f, f ∈ F, is {w_β : β < cof(N)}; it meets every K_β, so it is not Lebesgue null, hence not universally null. So |F| ≤ add(N) universally null sets have a union that is not universally null, and add(UN) ≤ add(N). ∎

### Proof of the corollaries

Facts quoted from Goto's paper (flat.txt; the original papers of Grzegorek and Recław were not checked): there is a universally null set of size non(N) (Grzegorek); there is one of size b (Recław); add(N) ≤ add(UN) ≤ non(UN) = non(N). Also non(N) ≤ cof(N) ≤ c (standard).

(a) Grzegorek's set has size non(N) = cof(N); apply the Theorem. If non(N) = c then cof(N) = c.

(c) Assume add(N) < add(UN). By the Theorem there is no universally null set of size cof(N); since subsets of universally null sets are universally null, every universally null set has size < cof(N). By Grzegorek and Recław, non(N) < cof(N) and b < cof(N). So ℵ_1 ≤ add(N) < add(UN) ≤ non(N) < cof(N) ≤ c, which forces c ≥ ℵ_3.

(b) Immediate from (c): if c ≤ ℵ_2 the chain in (c) is impossible, so add(N) = add(UN). ∎

The bound add(UN) ≤ min(d, cf(non(N))) in (c) uses Theorem A and the trivial bound
add(UN) ≤ cf(non(N)).

## Theorem A: proof

### Lemma 4 (invariant subsets)

Notation: lambda is the product measure on 2^omega. For B a subset of omega and x in 2^omega put [x]_B = {y : y(j) = x(j) for all j not in B}. Let K be a compact subset of 2^omega with lambda(K) > 0. Then there are s_0 in 2^{<omega} and a strictly increasing sequence b_0 < b_1 < ... of natural numbers such that for every set B whose k-th element (in increasing order) is >= b_k for all k, the set Good = {x in [s_0] : [x]_B is a subset of K} is closed, is a subset of K, is B-invariant (x in Good and y in [x]_B imply y in Good), and has lambda(Good) >= (1/4) 2^{-|s_0|} > 0.

*Proof.* Step 1 (density). There is s_0 with lambda(K cap [s_0]) > (1/2) 2^{-|s_0|}. Otherwise take open V containing K with lambda(V) < 2 lambda(K), write V as a disjoint union of cylinders [s_j]; then lambda(K) = sum_j lambda(K cap [s_j]) <= (1/2) lambda(V) < lambda(K), a contradiction. Put l = |s_0|.

Step 2 (levels). U = [s_0] minus K is open and lambda(U) < (1/2) 2^{-l}. Write U as the disjoint union of the cylinders [s_i], i in I, where the s_i are the inclusion-minimal strings with [s_i] a subset of U. Each s_i properly extends s_0 (because [s_i] is inside [s_0] and U is not all of [s_0]). So sum_i 2^{-|s_i|} = lambda(U). For m in omega put a_m = sum of 2^{-|s_i|} over the i with |s_i| = m, and t(n) = sum_{m > n} a_m. Then t(n) -> 0. Choose b_0 < b_1 < ... with b_0 >= l and t(b_k) <= 4^{-k-2} 2^{-l} for all k. Put N(m) = |{k : b_k < m}|. So N(m) = 0 for m <= b_0 and N(m) = k+1 for b_k < m <= b_{k+1}.

Step 3 (estimate). Let B be as in the statement. Then |B cap m| <= N(m) for every m (if the k-th element of B is < m then b_k < m), and B cap l is empty because b_0 >= l. So [x]_B is a subset of [s_0] for x in [s_0]. For x in [s_0] and i in I: [x]_B meets [s_i] if and only if x(j) = s_i(j) for all j < |s_i| with j not in B. (If the condition holds, change x on B cap |s_i| to agree with s_i; the result is in [x]_B and in [s_i]. The converse is clear.) The set E_i of all x with x(j) = s_i(j) for all j in |s_i| minus B is clopen with lambda(E_i) = 2^{-(|s_i| - |B cap |s_i||)}, and E_i is inside [s_0]. Let Bad be the union of the E_i. Then Bad is open and
lambda(Bad) <= sum_i 2^{-|s_i|} 2^{|B cap |s_i||} <= sum_m a_m 2^{N(m)} <= sum_{m <= b_0} a_m + sum_{k >= 0} 2^{k+1} t(b_k) < (1/2) 2^{-l} + sum_{k >= 0} 2^{k+1} 4^{-k-2} 2^{-l} = 2^{-l} (1/2 + 1/4).
So Good = [s_0] minus Bad is closed with lambda(Good) > (1/4) 2^{-l}. By the equivalence above, Good = {x in [s_0] : [x]_B cap U is empty} = {x in [s_0] : [x]_B is a subset of K cap [s_0]}, which is the set in the statement. Since x is in [x]_B, Good is a subset of K. If x is in Good and y is in [x]_B then y is in [s_0] and [y]_B = [x]_B, so y is in Good.

### Proof of Theorem A

Facts used, all stated in Goto, arXiv:2607.12936v4 (text checked in flat.txt). (F1) Lemma 5.11 and Fact 5.10: UN is invariant under Borel isomorphisms; below only the direct push-forward argument is used. (F2) Claim 5.5.1: if X is in UN and f : X -> 2^omega is any function, the graph {(x, f(x)) : x in X} is universally null in 2^omega x 2^omega. (F3) Grzegorek's theorem, as cited by Goto as reference [6]: there is a universally null set of cardinality non(N).

The family D. Let D_0 be a dominating family of size d. Close it under finite modifications, replace each g by n -> max_{i<=n} g(i) + n, and then replace each resulting h by n -> 2h(n) + 1. This gives a family D of size d of strictly increasing functions with odd values such that every F in omega^omega satisfies F(n) <= h(n) for all n for some h in D. For h in D, ran(h) is infinite and its complement contains all even numbers. Let g_h enumerate omega minus ran(h) increasingly.

The maps m_h. Define m_h : 2^omega x 2^omega -> 2^omega by m_h(c,u)(h(n)) = c(n) and m_h(c,u)(g_h(n)) = u(n). This is a homeomorphism induced by a bijection of coordinates, so it sends lambda x lambda to lambda.

The set Gamma. Let kappa = non(N). By (F3) fix P = {c_beta : beta < kappa} in UN, enumerated without repetition. Fix a non-null X of size kappa and put Y = X + Q, where Q is the countable group of finite-support elements. Then |Y| = kappa and Y has full outer measure: if A is Borel and contains Y, then A' = the intersection of the A + q (q in Q) is Borel, Q-invariant and contains X, so lambda(A') > 0; a Borel set invariant under all finite changes is a tail event, so lambda(A') = 1 by the Kolmogorov 0-1 law, hence lambda(A) = 1. Enumerate Y = {y_beta : beta < kappa} and put Gamma = {(c_beta, y_beta) : beta < kappa}. Gamma is the graph of a function on P, so Gamma is universally null in the plane by (F2).

Each W_h = m_h[Gamma] is in UN. Let mu be an atomless finite Borel measure on 2^omega. Its push-forward under the inverse of m_h is an atomless finite Borel measure on the plane, so Gamma has outer measure zero for it, so m_h[Gamma] has mu-outer measure zero.

The union W of the W_h (h in D) is not null. Let K be compact with lambda(K) > 0. Take s_0 and (b_k) from Lemma 4 and h in D with h(k) >= b_k for all k. Then B = ran(h) satisfies the hypothesis of Lemma 4, so Good = {x in [s_0] : [x]_B is a subset of K} is closed, B-invariant, inside K, and has positive measure. Put G = {u : m_h(c,u) is in Good for some c}. Since m_h(c,u) and m_h(c',u) differ only on B, B-invariance gives that the preimage of Good under m_h equals 2^omega x G. So G is closed and lambda(G) = (lambda x lambda)(2^omega x G) = lambda(Good) > 0. Y has full outer measure, so some y_beta is in G. Then m_h(c_beta, y_beta) is in Good, hence in K, and it is in W_h. So W meets every compact set of positive measure. If W were null, there would be an open set containing W of measure < 1, and its complement would be a compact set of positive measure disjoint from W. So W is not null, hence not universally null.

Thus D indexes d universally null sets with a union that is not universally null, so add(UN) <= d.

## Remarks

1. Second proof of Theorem B. Another agent proved g = add(N), where g is the least number
   of Borel functions `2^ω → 2^ω` whose graphs have a non-null union in the plane, and
   derived Theorem B from it. Its coding differs from Lemma 2. Two referees found no error
   in its main claims. The text is in `agent-logs/round1.json` (attack `g-versus-addN`).
2. A third agent proved: if cov(M) = cof(N), then add(UN) = add(N). This is a special case
   of Corollary (a), with a different and shorter proof. It uses the Bartoszyński–Shelah
   theorem add(E,N) = cov(M) for the ideal E generated by closed null sets
   (arXiv:math/9905123, Theorem 3.1, fetched by a referee).
3. Theorem A cannot be sharpened by its own method. Let θ_inv be the least size of a
   family of infinite co-infinite `B ⊆ ω` such that every compact set of positive measure
   contains a positive-measure `B`-invariant set. The proof gives add(UN) ≤ θ_inv ≤ d. A
   second-round agent proved θ_inv = d in ZFC (referee: correct as written), so this is
   the same bound.
4. The earlier version of this note proved add(UN) ≤ d only when a UN set of size c exists.
   Theorems A and B supersede it. The old text is in `add-UN-note-v1-superseded.md`.
5. Consistency result. In the Goldstern–Judah–Shelah model of `SN = [R]^{≤ℵ_1}` with
   c = ℵ_2 (arXiv:math/9306214, Theorem 0.14, read by two agents; the iteration is
   `ω^ω`-bounding, so d = ℵ_1), add(UN) = add(N) = ℵ_1 by Theorem A or Corollary (b), while
   add(SN) = add(SN,N) = ℵ_2. So add(UN) < add(SN,N) is consistent, and Goto's bound
   add(UN) ≤ add(SN,N) can be strict.

## Literature (what the searches found)

- No source answers Question 6.3. OpenAlex and Semantic Scholar list no citations of Goto's
  paper. The problem page (openlogicproblems.com, Problem 24) still says "Open".
- No earlier statement of Theorem A or Theorem B was found. Read in full text: Fremlin,
  *Measure Theory*, chapters 43 and 54; Miller, "Special subsets of the real line" (OCR of
  the scan) and "Special sets of reals"; Recław's 1991 and 2001/02 papers. Google Scholar
  and MathSciNet could not be queried, and arXiv full text is not searchable, so this is
  not conclusive.
- Fremlin 544L(a): add(Un) ≥ add(N) for universally negligible subsets of any metrizable
  space. So Goto's Corollary 5.13 is already there. Fremlin states no upper bound.
- Lemma 3 and (F2) are classical: Fremlin 439C(c) and 439G; Miller, Lemma 9.3.1.
- Miller, Section 7: under Martin's Axiom, unions of fewer than c universal measure zero
  sets have universal measure zero. No upper bound.
- Recław, Colloq. Math. 62 (1991) diagonalises over a universally null set of size c with
  an injective-preimage lemma. This is the closest precedent in method; its results concern
  algebraic sums, not add(UN).
- Bartoszyński, Rosłanowski, Shelah, "Adding one random real", arXiv:math/9406229,
  Theorem 1.1(3) (due to Krawczyk): after adding one random real, non(N) ≤ d and
  cov(N) ≥ b. Read from the TeX source.

## What is still open

The case non(N) < cof(N) with every universally null set of size < cof(N). The proof of
Theorem B picks one point for each member of a cofinal family of positive compact sets, so
it needs cof(N) distinct codes in one universally null set. Theorem A avoids this by using
whole "leaves" inside a compact set, hit by a fixed set of size non(N), at the cost of d.

Negative results from the second round (one referee each; verdict "fixable gaps", no false
claim found; details in `agent-logs/round2.json`):

- Any leaf device in which a fixed set is assumed only to have full outer measure for a
  fixed measure needs at least cov(M) maps. So combining Lemma 2 with the Theorem A device
  cannot give add(N) when add(N) < cov(M).
- Leaf devices built from Borel maps `2^ω × U → 2^ω` with infinite leaves need at least
  max(cov(M), min(d, cov(N))) maps. The "markers at all large levels" version of Lemma 2
  needs d functions.
- The selector cardinal (least size of a family of positive compact sets such that every
  set meeting all of them is non-null) equals cof(N). So Theorem B's hypothesis cannot be
  weakened this way.

Still undecided in ZFC: add(UN) ≤ b, add(UN) ≤ cov(M), add(UN) ≤ non(M).

Models. A model of add(N) < add(UN) needs c ≥ ℵ_3 and the constraints in Corollary (c),
and must avoid the finite support iterations covered by Goto's Theorem 5.18. A survey
agent fetched the main constructions and applied these constraints (medium confidence;
its referee repaired one argument and noted that it rests on Goto's unrefereed 5.17–5.18):

- Ruled out by Theorems A and B alone: the Fischer–Goldstern–Kellner–Shelah creature
  models (d = ℵ_1), and every model with non(N) = cof(N), including those with
  cov(M) = c or non(N) = c.
- Pass the numerical constraints, then fall to Goto's Theorem 5.18: Theorems 4 and 6 of
  Mejía's matrix iteration paper (arXiv:1211.5209) and Theorem D of Brendle–Cardona–Mejía
  (arXiv:1809.05004). Mejía's Theorems 16–19 fall the same way if their iterands are of
  the same kinds; the agent read only part of that proof.
- Not decided: Cichoń's maximum via Boolean ultrapowers (arXiv:1708.03691), the
  alternative order of Kellner–Shelah–Tanasie (arXiv:1712.00778), and Brendle's shattered
  iterations (arXiv:2302.05069).

Full agent outputs and referee reports: `agent-logs/round1.json` and
`agent-logs/round2.json`.
