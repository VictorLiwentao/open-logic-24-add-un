# Open case, round 3: Plan Z (translates of universally null sets)

Status (2026-11-19). Written by one AI agent (Claude) in one session. Nobody has checked it.
The author re-read each proof marked PROVED once, as a referee. No second reader, no Lean.

Labels: PROVED (full proof here), CITED (source named, with how it was read), SKETCH,
FAILED, CONJECTURE, UNVERIFIED.

## 0. Result in short

- Plan Z is **not carried out**. Neither (Z1) nor (Z2) is proved in ZFC. Neither is refuted.
- The cited formula add(N) = min{b, add*(N)} and Shelah's characterisation are confirmed
  (Section 2). Both b < add*(N) and add*(N) < b are consistent, so Plan Z needs both halves.
- New, PROVED: a translation form of the coding lemma (Lemma 5). It gives (Z2) whenever a
  universally null set of size cof(N) exists (Proposition 8). So (Z2) holds in the same models
  as Theorem B. It is open exactly in the open case of the main problem.
- (Z1) and (Z2) fail at the **same step** as scheme GS of `ideas.md` (obstacle O3). The keys are
  not the problem. An unbounded family (for Z1) or a set that is not N-additive (for Z2) gives
  enough keys. The problem is to make a set of only non(N) points non-null (Section 6).
- Plan Z does not make the problem easier. "add(UN) ≤ b and add(UN) ≤ add*(N)" is the same
  statement as add(UN) ≤ add(N). The extra structure of translations gives Lemma 5 and no more.

## 1. Notation

λ is the product measure on 2^ω. N is the null ideal. UN is the universally null ideal.
ν = non(N). Addition on 2^ω is coordinatewise mod 2. "Admissible measure" means a finite Borel
measure that vanishes on singletons.

- X ⊆ 2^ω is **N-additive** if X + A ∈ N for every A ∈ N. NA is the family of these sets.
- add*(N) = non(NA) = min{|X| : X + A ∉ N for some A ∈ N}.
- τ = min{|X| : X + G ∉ N for some G ∈ UN}.

Trivial facts (PROVED, one line each).

- add(N) ≤ add*(N) ≤ ν. A union of fewer than add(N) translates of a null set is null. A
  non-null X with A = {0} shows add*(N) ≤ ν.
- add*(N) ≤ τ ≤ ν. A universally null set is null. For τ ≤ ν take X ∉ N and G = {0}.
- add(UN) ≤ τ. If X + G ∉ N then the |X| translates x + G are universally null (Lemma 3 of the
  note with φ(y) = y + x) and their union is not null.

(Z2) says τ ≤ add*(N), that is τ = add*(N). (Z1) says add(UN) ≤ b.

## 2. Step 1: the cited statements

### 2.1 Shelah's characterisation. CITED, source read

Source read directly: S. Shelah, "Every null-additive set is meager-additive",
arXiv:math/9406228v1 (text extracted from the arXiv PDF; Definition 12 and Theorem 13 read in
full, the proof skimmed).

- Definition 12. A *corset* is a non-decreasing f : ω → ω∖{0} that converges to infinity. A
  tree T ⊆ 2^{<ω} is *of width f* if |T ∩ 2^n| ≤ f(n) for every n.
- Notation 4(7). A^fin = {y : y(n) = x(n) for all but finitely many n, for some x ∈ A}.
- **Theorem 13.** For X ⊆ 2^ω the following are equivalent. (a) X is null-additive. (b) For
  every corset f there is a tree S of width f with X ⊆ Lim(S)^fin. (c), (d): two variants with
  countably many trees.
- Theorem 2 of the same paper: every null-additive set is meager-additive.

The form in `ideas.md` (blocks and sets I_n with |I_n| ≤ n) is **not** the wording of Shelah's
paper. It is the wording of Theorem 1.10(1) of Cardona, Mejía, Rivera-Madrid, "Uniformity
numbers of the null-additive and meager-additive ideals", arXiv:2401.15364v3, which attributes
it to [She95, Thm. 13]. That paper was read through an automatic summary of the arXiv HTML
(two passes; the last 36 000 characters were not read). Its statement:

> **(Sh)** X ∈ NA if and only if for every partition I = (I_n) of ω into finite non-empty
> intervals there is φ with φ(n) ⊆ 2^{I_n}, |φ(n)| ≤ n for all n, and
> X ⊆ H_φ = {x : x↾I_n ∈ φ(n) for all but finitely many n}.

Theorem 2.1 of the same paper: the same holds with |φ(n)| ≤ h(n) for any fixed h that tends
to infinity (they refer to Bartoszyński–Judah, Theorem 2.7.18, for this).

The memory version in the task is correct. It is (Sh).

**Lemma 1 (PROVED). Theorem 13(b) and (Sh) are equivalent conditions on X.**

*Proof.* (b) ⇒ (Sh). Let I_n = [g(n), g(n+1)). Put f(m) = max(1, n) for g(n) < m ≤ g(n+1) and
f(0) = 1. This is a corset. Take S of width f with X ⊆ Lim(S)^fin. Put φ(0) = ∅ and
φ(n) = {s↾I_n : s ∈ S ∩ 2^{g(n+1)}} for n ≥ 1. Then |φ(n)| ≤ f(g(n+1)) = n. If x ∈ X, then x
agrees with some y ∈ Lim(S) from some point on, so x↾I_n = y↾I_n ∈ φ(n) for all large n.

(Sh) ⇒ (b). Let f be a corset. Choose g(0) = 0 < g(1) < ... with f(g(n) + 1) ≥ (n+1)! for
n ≥ 1. Take φ for I_n = [g(n), g(n+1)). Let S be the set of all s ∈ 2^{<ω} such that the part
of s in I_0 is zero and, for every n ≥ 1, the part of s in I_n is an initial part of a member
of φ(n) or of the zero string. S is a tree. For g(n) < m ≤ g(n+1) with n ≥ 1,
|S ∩ 2^m| ≤ ∏_{1≤i≤n} (i+1) = (n+1)! ≤ f(m). For m ≤ g(1), |S ∩ 2^m| = 1 ≤ f(m). If x ∈ X,
change x to zero on the finitely many blocks where x↾I_n ∉ φ(n). The result is in Lim(S). ∎

### 2.2 The formula add(N) = min{b, add*(N)}. CITED, and derived

- CITED: arXiv:2401.15364v3, Theorem 1.8(1): add(N) = min{b, non(NA)}, attributed there to
  [Paw85, Lem. 2.3] (J. Pawlikowski, "Powers of transitive bases of measure and category",
  Proc. AMS 93 (1985); only its abstract was seen, in a search result). The same theorem
  states add(M) = min{b, non(MA)}. The paper also says that [Paw85] and Kraszewski call non(NA)
  the transitive additivity and that Bartoszyński–Judah write add*(N) for it.
- UNVERIFIED: the location "Bartoszyński–Judah, Section 2.7". The book was not read. The
  summary of arXiv:2401.15364 cites BJ Theorem 2.7.18 for the characterisation of NA and BJ
  Theorem 2.7.14 for a characterisation of non(MA), not for this formula.
- Also CITED there: Theorem 1.5 ([Paw85, Lem. 2.2]): non(NA) = minLc, the least size of a
  family F ⊆ ∏b, over all b ∈ ω^ω, that no slalom S with |S(n)| ≤ n localises. Corollary 1.7:
  the same with any width h that tends to infinity.

**Lemma 2 (PROVED from (Sh), Lemma 1 of the note, and add(N) ≤ b).**
add(N) = min{b, add*(N)}.

*Proof.* add(N) ≤ add*(N) is in Section 1. add(N) ≤ b is classical (Cichoń's diagram; not
fetched). For the other direction suppose add(N) < min{b, add*(N)}. Lemma 1 of the note
(`exists_unlocalised_family`, Lean-checked) with width h(n) = n + 1 gives F ⊆ ω^ω,
|F| ≤ add(N), that no slalom of width h localises. Since |F| < b there is a strictly increasing
g with f ≤* g for all f ∈ F. Take intervals I_n with 2^{|I_n|} > g(n) and code the number
min(f(n), g(n)) as a string c_f(n) ∈ 2^{I_n}. Let x_f be the concatenation. X = {x_f : f ∈ F}
has size < add*(N), so X ∈ NA. By (Sh) there is φ with |φ(n)| ≤ n and X ⊆ H_φ. Let S(n) be
the set of numbers coded by members of φ(n). Then |S(n)| ≤ n and S localises every f ∈ F,
because f(n) = min(f(n), g(n)) for all large n. Contradiction. ∎

This uses only the direction "N-additive ⇒ captured" of (Sh), which is the hard direction of
Shelah's theorem.

### 2.3 Both halves of Plan Z are needed. CITED

- b < non(NA) is consistent. arXiv:2401.15364v3 states "it is consistent that
  b < add(NA) = non(NA)" (after its Theorem A, which proves add(NA) = non(NA) in ZFC).
- non(NA) < b is consistent. The same paper: a finite support iteration of Hechler forcing
  gives non(NA) = ℵ_1 < non(MA) = b = c = ℵ_2.

So neither of (Z1), (Z2) follows from the other through the formula.

### 2.4 Plan Z as logic. PROVED

By Lemma 2, "add(UN) ≤ b and add(UN) ≤ add*(N)" is equivalent to add(UN) ≤ add(N). So the
conclusion of Plan Z is the whole problem, split in two. (Z2) as stated in `ideas.md` (τ ≤
add*(N)) is stronger than the half that is needed (add(UN) ≤ add*(N)).

**Proposition 3 (PROVED, modulo two cited facts).** add(UN) equals the least size of a family
(m_i)_{i∈I} of Borel bijections of 2^ω such that ⋃_i m_i[Γ] ∉ N for some single Γ ∈ UN.

So τ is the same cardinal with "Borel bijection" replaced by "translation". This is the exact
sense in which (Z2) asks for more than add(UN) ≤ add*(N).

*Proof.* Cited: Borel isomorphisms preserve UN (Goto, Lemma 5.11); add(UN) = add(UN, N)
(Goto, Proposition 5.12; both read through a summary of arXiv:2607.12936v4). Lemma F of
`ideas.md` is used; its proof is short and I re-checked it (it is Fremlin 439C(c)).
≥: if Γ ∈ UN then each m_i[Γ] ∈ UN, so a non-null union needs at least add(UN) maps.
≤: let κ = add(UN) and W_i ∈ UN (i < κ) with non-null union. κ ≤ ν, so there is a universally
null set {p_i : i < κ} of size κ (any set if κ < ν; Grzegorek's set if κ = ν). Then
Γ' = ⋃_i {p_i} × W_i is universally null in the plane by Lemma F (project to the first
coordinate). Fix a Borel isomorphism e : 2^ω × 2^ω → 2^ω and put Γ = e[Γ']. Fix a null perfect
set D. Let m_i send e(p_i, w) to w for w ∉ D, and send the rest of 2^ω (an uncountable Borel
set) onto D by any Borel bijection. Then m_i[Γ] ⊇ W_i ∖ D, and ⋃_i W_i ∖ D is not null. ∎

## 3. Step 2: attack on (Z2)

### 3.1 The translation coding lemma. PROVED

Constants as in Lemma 2 of the note: μ_n = 4^{n+1}, α_n = 2^{−μ_n}, ρ_n = 2^{−μ_n−n},
h(n) = 2^{3μ_n+n}, τ_n = Σ_{m>n} α_m for n ≥ −1. Arithmetic from the note:
τ_{n−1} = τ_n + α_n, α_n ≤ τ_{n−1}, τ_n ≤ 2α_{n+1} = 2^{1−4μ_n}, and
(E) ρ_n τ_{n−1} ≥ ρ_n α_n = 2^{−2μ_n−n} ≥ 2^{2−4μ_n} ≥ 2τ_n.

**Blocks.** Fix L = (L_n) with L_n ≥ 1. Write 𝔽 = {0,1} with addition mod 2 and
⟨a,u⟩ = Σ_l a(l)u(l) mod 2 for a, u ∈ 𝔽^{L_n}. Cut ω into consecutive intervals J_n of length
L_n + (μ_n + n)(L_n + 1). Read y↾J_n as a tuple

 (a_n(y); u_{n,i}(y), v_{n,i}(y) for i < μ_n + n), a_n, u_{n,i} ∈ 𝔽^{L_n}, v_{n,i} ∈ 𝔽.

Put β_{n,i}(y) = ⟨a_n(y), u_{n,i}(y)⟩ + v_{n,i}(y).

**Decoder (one map, no key).** y *has a marker at n* if β_{n,i}(y) = 0 for all i < μ_n.
msg_n(y) ∈ 2^n is i ↦ β_{n,μ_n+i}(y). D(y) = {n : y has a marker at n}. dom(φ) is the set of y
with D(y) infinite such that for every i the bits msg_n(y)(i), n ∈ D(y), n > i, are eventually
constant. φ(y)(i) is that constant. dom(φ) is Borel and φ is Borel on it.

**Keys.** For k ∈ 𝔽^{L_n} let e_n(k) ∈ 2^{J_n} have a-part k and all other coordinates 0. For
f ∈ ∏_n 𝔽^{L_n} let x_f ∈ 2^ω be given by x_f↾J_n = e_n(f(n)). For F ⊆ ∏_n 𝔽^{L_n} put
X_F = {x_f : f ∈ F}. The map f ↦ x_f is injective.

For k ∈ 𝔽^{L_n} put β^k_{n,i}(w) = ⟨a_n(w) + k, u_{n,i}(w)⟩ + v_{n,i}(w). Then
β_{n,i}(w + x_f) = β^{f(n)}_{n,i}(w).

**Lemma 5 (translation coding lemma).** For every compact K ⊆ 2^ω with λ(K) > 0 and every
c ∈ 2^ω there is a slalom S, S(n) ⊆ 𝔽^{L_n}, |S(n)| ≤ h(n), such that for every
f ∈ ∏_n 𝔽^{L_n} with f(n) ∉ S(n) for infinitely many n there is w ∈ K with
w + x_f ∈ dom(φ) and φ(w + x_f) = c.

*Proof.* Fix K and c. For n ∈ ω and k ∈ 𝔽^{L_n} let

 A_{n,k} = {w : β^k_{n,i}(w) = 0 for all i < μ_n},
 R_{n,k} = A_{n,k} ∩ {w : β^k_{n,μ_n+i}(w) = c(i) for all i < n}, W_{n,k} = A_{n,k} ∖ R_{n,k}.

These sets are clopen and depend only on w↾J_n.

(I1) For fixed n and k the bits β^k_{n,i}, i < μ_n + n, are independent and uniform under λ.
Reason: condition on a_n and on all u_{n,i}. Then β^k_{n,i} is a constant plus v_{n,i}, and the
v_{n,i} are independent uniform bits. Hence λ(A_{n,k}) = α_n, λ(R_{n,k}) = ρ_n,
λ(W_{n,k}) ≤ α_n, and R_{n,k} ∩ W_{n,k} = ∅.

(I2) For k ≠ k' in 𝔽^{L_n}: λ(R_{n,k} ∩ R_{n,k'}) = ρ_n². Reason: put δ = k + k' ≠ 0 and
d_i = ⟨δ, u_{n,i}⟩. Then β^{k'}_{n,i} = β^k_{n,i} + d_i. Each d_i is a uniform bit, because
δ ≠ 0 and u_{n,i} is uniform. The d_i are independent, because they depend on different
u_{n,i}. Given a_n and all u_{n,i}, the bits β^k_{n,i} are still independent and uniform, by
the argument of (I1). So the 2(μ_n + n) bits β^k_{n,i}, d_i are independent and uniform.
R_{n,k} ∩ R_{n,k'} is the event that each β^k_{n,i} has its prescribed value and each d_i = 0.
Its measure is 2^{−2(μ_n+n)} = ρ_n².

(I3) An event that depends on coordinates in ⋃_{m<n} J_m is independent of an event that
depends on J_n.

*Definition of S.* Choose n_0 ≥ 1 with 2τ_{n_0−1} ≤ λ(K). Put S(n) = ∅ for n < n_0. For
n ≥ n_0 and s ∈ ∏_{m<n} 𝔽^{L_m} define closed sets T^n(s) ⊆ K and then S(n), by recursion.
T^{n_0}(s) = K.

 S(n) = {k ∈ 𝔽^{L_n} : λ(T^n(s') ∩ R_{n,k}) < (ρ_n/2) λ(T^n(s')) for some s' ∈ ∏_{m<n} 𝔽^{L_m}}.

For s = s'⌢k: T^{n+1}(s) = T^n(s') ∩ R_{n,k} if k ∉ S(n), and T^{n+1}(s) = T^n(s') ∖ W_{n,k} if
k ∈ S(n). So T^n(s) = K ∩ E(s), where E(s) is clopen and depends only on coordinates in
⋃_{n_0≤m<n} J_m.

*Invariant.* λ(T^n(s)) ≥ 2τ_{n−1}. For n = n_0 this is the choice of n_0. If k ∈ S(n), then
λ(T^{n+1}(s)) ≥ 2τ_{n−1} − α_n = 2τ_n + α_n ≥ 2τ_n. If k ∉ S(n), then
λ(T^{n+1}(s)) ≥ (ρ_n/2) λ(T^n(s')) ≥ ρ_n τ_{n−1} ≥ 2τ_n by (E).

*Width.* Fix n ≥ n_0, ρ = ρ_n, θ = 2τ_{n−1} > 0. Let k_1, ..., k_N be distinct members of
S(n) with witnesses s_1, ..., s_N. Put E_j = E(s_j), T_j = K ∩ E_j, R_j = R_{n,k_j}. Then
λ(T_j) ≥ θ and λ(T_j ∩ R_j) < (ρ/2) λ(T_j). Let Ξ = Σ_j 1_{E_j} (ρ − 1_{R_j}). Then

 ∫_K Ξ dλ = Σ_j (ρ λ(T_j) − λ(T_j ∩ R_j)) > Σ_j (ρ/2) λ(T_j) ≥ Nρθ/2.

By (I3), ∫ 1_{E_j} (ρ − 1_{R_j})² = λ(E_j) (ρ² − 2ρ·ρ + ρ) = λ(E_j) ρ(1 − ρ) ≤ ρ. For j ≠ j',
by (I3) and then (I2),

 ∫ 1_{E_j} 1_{E_j'} (ρ − 1_{R_j})(ρ − 1_{R_j'}) = λ(E_j ∩ E_j') (λ(R_j ∩ R_j') − ρ²) = 0.

So ∫ Ξ² ≤ Nρ. By Cauchy–Schwarz, ∫_K Ξ ≤ (∫ Ξ²)^{1/2} ≤ (Nρ)^{1/2}. Hence
Nρθ/2 < (Nρ)^{1/2}, so N < 4/(ρθ²) = 1/(ρ_n τ_{n−1}²) ≤ 1/(ρ_n α_n²) = h(n).

*The point w.* Let f(n) ∉ S(n) for infinitely many n. For n ≥ n_0 put
Q_n = T^n(f↾n) ∖ ⋃_{m≥n} W_{m,f(m)}. Q_n is closed and
λ(Q_n) ≥ 2τ_{n−1} − Σ_{m≥n} α_m = τ_{n−1} > 0. In both cases of the definition,
T^{n+1}(f↾(n+1)) ⊆ T^n(f↾n) ∖ W_{n,f(n)}, because R_{n,k} ∩ W_{n,k} = ∅. So Q_{n+1} ⊆ Q_n. By
compactness pick w ∈ ⋂_{n≥n_0} Q_n. Then w ∈ K, w ∉ W_{m,f(m)} for all m ≥ n_0, and
w ∈ R_{n,f(n)} for every n ≥ n_0 with f(n) ∉ S(n).

Let y = w + x_f. y has a marker at n if and only if w ∈ A_{n,f(n)}. So D(y) is infinite. If
n ∈ D(y) and n ≥ n_0, then w ∈ A_{n,f(n)} ∖ W_{n,f(n)} = R_{n,f(n)}, so msg_n(y) = c↾n. Hence
for each i every n ∈ D(y) with n > max(i, n_0) gives the bit c(i). So y ∈ dom(φ) and
φ(y) = c. ∎

Referee notes on Lemma 5. The proof is Lemma 2 of the note with two changes. The events of
level n for different key values are no longer on disjoint coordinates; they are pairwise
independent by (I2), and only pairwise independence is used. The key acts by translation, so
there is one decoder φ. The slalom is non-trivial only if 2^{L_n} > h(n).

### 3.2 Consequences. PROVED

Put G_c = φ^{-1}(c) for c ∈ 2^ω. The sets G_c are Borel and pairwise disjoint. Each is null:
G_c ⊆ {y : D(y) infinite}, and λ{y : y has a marker at n} = α_n by (I1) with k = 0, so
Borel–Cantelli applies.

**Lemma 6 (keys exist).** There are L and F ⊆ ∏_n 𝔽^{L_n} with |F| = add*(N) such that no
slalom S with S(n) ⊆ 𝔽^{L_n}, |S(n)| ≤ h(n), localises F.

*Proof.* (CITED input: (Sh); alternatively Corollary 1.7 of arXiv:2401.15364 gives the lemma
at once.) Take X ∉ NA with |X| = add*(N). By (Sh) there is an interval partition I such that
no φ with |φ(m)| ≤ m has X ⊆ H_φ. Choose m_0 = 0 < m_1 < ... with m_n ≥ h(n) for n ≥ 1. Let
I'_n = ⋃_{m_n≤m<m_{n+1}} I_m, L_n = |I'_n|, and f_x(n) = x↾I'_n ∈ 𝔽^{L_n}. F = {f_x : x ∈ X}
has size |X|. Suppose S of width h localises F. Put φ(m) = ∅ for m < m_1 and
φ(m) = {s↾I_m : s ∈ S(n)} for m_n ≤ m < m_{n+1}, n ≥ 1. Then |φ(m)| ≤ h(n) ≤ m_n ≤ m, and
X ⊆ H_φ. Contradiction. ∎

**Corollary 7.** Let F be as in Lemma 6 and X = X_F. Then |X| = add*(N), and for **every**
c ∈ 2^ω the set X + G_c meets every compact set of positive measure. So X + G_c has full outer
measure. In particular X is not N-additive, and this is witnessed by each of continuum many
pairwise disjoint Borel null sets.

*Proof.* Let K be compact with λ(K) > 0. Take S from Lemma 5 for (K, c). Some f ∈ F has
f(n) ∉ S(n) for infinitely many n. Lemma 5 gives w ∈ K with y = w + x_f ∈ G_c. Then
w = x_f + y ∈ X + G_c. ∎

**Proposition 8 ((Z2) under the hypothesis of Theorem B).** Suppose there is a universally
null set of size cof(N). Let X = X_F be as in Corollary 7. Then there is G ∈ UN with
X + G ∉ N. Hence τ = add*(N), and add(UN) ≤ add*(N).

*Proof.* As in the proof of Theorem B, fix compact sets K_β (β < cof(N)) of positive measure
such that every set that meets all K_β is not null. Let P = {c_β : β < cof(N)} be universally
null, listed without repetition. For each β take S_β from Lemma 5 for (K_β, c_β), then
f_β ∈ F with f_β(n) ∉ S_β(n) for infinitely many n, then w_β ∈ K_β with
y_β = w_β + x_{f_β} ∈ dom(φ) and φ(y_β) = c_β. Let G = {y_β : β < cof(N)}. φ is injective on
G: if φ(y_β) = φ(y_β') then c_β = c_β', so β = β'. Also φ[G] ⊆ P. By Lemma 3 of the note, G is
universally null. X + G contains x_{f_β} + y_β = w_β ∈ K_β for every β. So X + G is not null.
τ ≥ add*(N) is in Section 1. ∎

Proposition 8 gives nothing new about add(UN): under its hypothesis Theorem B already gives
add(UN) = add(N) ≤ add*(N). It is new only as a statement about translates.

**Where (Z2) stands (PROVED).**

- (Z2) holds if there is a universally null set of size cof(N). This covers non(N) = cof(N),
  by Grzegorek's theorem.
- (Z2) holds trivially if add*(N) = non(N). This covers non(N) = ℵ_1. With the first item it
  covers c ≤ ℵ_2.
- So (Z2) can fail only if add*(N) < non(N) < cof(N) and every universally null set has size
  < cof(N). This is inside the open case of the main problem.

**Sanity check.** If |X| < add(N), Lemma 5 does not apply: F is then localised by a slalom of
width h (`exists_localising_slalom`). Any G with X + G ∉ N needs |X| ≥ add*(N) ≥ add(N). The
argument does not contradict add(N) ≤ add(UN).

### 3.3 Every set that is not N-additive. SKETCH

Claim: Corollary 7 and Proposition 8 hold for every X ∉ NA, not only for X_F. So, if there is
a universally null set of size cof(N), then a set X is N-additive if and only if X + G ∈ N
for every G ∈ UN.

Sketch. Let X ∉ NA. Regroup the partition of (Sh) into intervals Q_0, Q_1, ... such that
|Q_{m+1}| ≥ (μ_m + m)(|Q_m| + 1) and X is not captured along (Q_m) with width
m ↦ h(⌊m/2⌋). Then X is not captured with width h along the even or along the odd Q_m. Let
the a-part of block n be Q_{2n+p} for that parity p. Take the u- and v-coordinates of block n
from Q_{2n+p+1}. Now a key x ∈ X also moves the u- and v-coordinates. For two key values with
different a-parts k ≠ k', the difference of the two bits of cell i is
⟨k + k', u_{n,i}⟩ plus a function of a_n; given a_n these differences are still independent
uniform bits, so (I2) holds. Key values with the same a-part are not independent. So bound the
number of *a-parts* of members of S(n) by h(n): choose one bad key value for each bad a-part
and run the second-moment argument on these. The rest of the proof is unchanged. I did not
write this at the level of detail of Lemma 5.

### 3.4 (Z2) in the open case: reduction. PROVED

Let H ⊆ 2^ω × 2^ω be Borel with every section H^c = {z : (z,c) ∈ H} null, and such that every
null set is inside some H^c (as `universalNull` in `AddUN/Grzegorek.lean`, moved to 2^ω by a
Borel isomorphism of the code space).

**Proposition 9 (towers with keys).** Let ψ_j : D_j → 2^ω (j ∈ J) be Borel maps on Borel sets
D_j ⊆ 2^ω. Let T = {t_α : α < ν} be not null. Suppose that for every α < ν there is j_α ∈ J
with t_α ∈ D_{j_α} and {t_β : β < α} ⊆ H^{ψ_{j_α}(t_α)}. Then each T_j = {t_α : j_α = j} is
universally null. Hence add(UN) ≤ |J|.

*Proof.* Fix j and an admissible μ. Let μ' be the image of μ↾D_j under ψ_j, a finite Borel
measure. By Fubini, (λ × μ')(H) = ∫ λ(H^c) dμ'(c) = 0. So E = {z : μ'(H_z) > 0} is a Borel
null set, where H_z = {c : (z,c) ∈ H}. T is not null, so there is β with t_β ∉ E. Then
μ(D_j ∩ ψ_j^{-1}[H_{t_β}]) = 0. If α > β and j_α = j, then t_β ∈ H^{ψ_j(t_α)}, so
t_α ∈ ψ_j^{-1}[H_{t_β}]. So {t_α ∈ T_j : α > β} is μ-null. {t_α : α ≤ β} has size < ν, so it
is μ-null by non(UN) = non(N). ∎

**Proposition 10 (sufficient condition for (Z2)).** Let φ be the decoder of 3.1 and X ⊆ 2^ω.
Let T = {t_α : α < ν} be not null and x_α ∈ X with t_α + x_α ∈ dom(φ) and

 (TT) {t_β : β < α} ⊆ H^{φ(t_α + x_α)} for every α < ν.

Then G = {t_α + x_α : α < ν} is universally null and X + G ⊇ T is not null.

*Proof.* Put c_α = φ(t_α + x_α) and C = {c_α : α < ν}. C is universally null: for an
admissible μ on the code space, Fubini gives t_β ∈ T with μ(H_{t_β}) = 0; then
{c_α : α > β} ⊆ H_{t_β}, and {c_α : α ≤ β} has size < ν. Fix c ∈ C. If {α : c_α = c} were
unbounded in ν, then T ⊆ H^c would be null. So it is bounded, and the fibre
G ∩ φ^{-1}(c) has size < ν, so it is universally null. By Lemma F, G is universally null. ∎

An exact but empty reformulation: (Z2) holds for X if and only if there are a non-null T of
size ν and x_t ∈ X with {t + x_t : t ∈ T} ∈ UN. (PROVED: take T ⊆ X + G; conversely
G = {t + x_t}.)

**The clean statement.** For a cardinal κ let Tow_κ be:

> There are Borel sets R_j ⊆ 2^ω × 2^ω (j < κ) with all sections R_j^t = {s : (s,t) ∈ R_j}
> null, a set T ∉ N, and a well-order ≺ of T of type non(N), such that for every t ∈ T there
> is j with {s ∈ T : s ≺ t} ⊆ R_j^t.

- PROVED: Tow_κ implies add(UN) ≤ κ (Proposition 9 with R_j = {(s,t) : s ∈ H^{ψ_j(t)}}; the
  proof only uses that R_j is Borel with null sections).
- PROVED: Tow_κ fails for κ < add(N). For each j the set B_j = {s : {t : (s,t) ∈ R_j} ∉ N} is
  null by Fubini. If κ < add(N), pick s ∈ T ∖ ⋃_j B_j. The successors of s in T lie in
  ⋃_j {t : (s,t) ∈ R_j}, a null set, and the predecessors are fewer than ν. So T ∈ N.
- PROVED: if non(N) = cof(N), then Tow_{add(N)} holds. Let (N_α)_{α<ν} be cofinal in N and
  K_α compact of positive measure, disjoint from N_α. At step α take a code c with
  {t_β : β < α} ⊆ H^c, the slalom of Lemma 2 of the note for (K_α, c), a key f in the family
  of Lemma 1 that escapes it, and t_α ∈ K_α with φ_f(t_α) = c. Use
  R_f = {(s,t) : t ∈ dom(φ_f), s ∈ H^{φ_f(t)}}. T meets every K_α, so T ∉ N. Drop repeated
  points.
- The translation form TowT(X): (TT) holds for some non-null T and some x_α ∈ X. By
  Proposition 10, TowT(X) implies (Z2) for X.
- OPEN: Tow_{add(N)}, Tow_b, and TowT(X) for |X| = add*(N), when non(N) < cof(N).
- Note: Tow_κ is not implied by "there is a universally null set of size cof(N)" in any way I
  can see. So it may be stronger than add(UN) ≤ κ.

### 3.5 Where the natural proof of TowT(X) fails. FAILED

The attempt: build T by recursion on α < ν. At step α the set of allowed points is

 D_α = X + φ^{-1}[{c : {t_β : β < α} ⊆ H^c}].

By Corollary 7, D_α ⊇ X + G_c for one such c, so D_α has full outer measure. So t_α can be
chosen in any prescribed compact set of positive measure.

**The step that fails:** T must be not null after only ν steps. With ν < cof(N) the recursion
cannot meet a family of compact sets that forces non-nullness (the selector cardinal is
cof(N), `partial-results.md`). The other known way to force non-nullness is to start from a
given non-null Z = {z_α} and take t_α = z_α (or t_α ∈ z_α + Y with Y ∈ NA; this only replaces
X by X + Y). That needs z_α ∈ D_α for a prescribed point z_α. This is false in general: for a
fixed point z the codes φ(z + x), x ∈ X, are at most |X| fixed codes. They cover the earlier
points only if the earlier points lie in one of |X| fixed null sets. So the set of earlier
points that z allows is determined by z, and T must be built so that each point fits the
earlier ones and T is still not null. I found no way to do both. This is obstacle (O3) of
`ideas.md`, unchanged.

Two remarks (PROVED, elementary).

- D_α ⊆ X + dom(φ). So T lies in a union of |X| translates of one Borel null set. A tower is a
  non-null set of size ν inside this union that meets each translate in a universally null
  set.
- If M is a transitive model that contains codes for R_j and (s,t) is random over M for
  λ × λ, then (s,t) ∉ R_j, because R_j is a λ × λ-null Borel set. So in a tower no pair
  t_β ≺ t_α is random over a model that contains the keys. A non-null set of mutually random
  reals over such a model cannot be a tower. The tower must be far from generic.

### 3.6 Can (Z2) be refuted? Not by the tools at hand

- Necessary condition tested (PROVED): if (Z2) holds for X then for every admissible μ there
  is a μ-null Borel set B with X + B ∉ N. This is true for X = X_F: all but countably many
  G_c are μ-null. So there is no obstruction at the level of single measures.
- Any ZFC lower bound τ ≥ 𝔵 with 𝔵 a cardinal that can exceed add*(N) in a model with
  non(N) = cof(N) or c ≤ ℵ_2 contradicts Proposition 8. For example τ ≥ b and τ ≥ cov(M) are
  not theorems (Hechler model: add*(N) = ℵ_1 < b = c = ℵ_2, cited in 2.3; Cohen model:
  add*(N) = ℵ_1 < cov(M) = c, from memory).
- A model where (Z2) fails must lie in the open case, or at least satisfy
  add*(N) < non(N) < cof(N) with no universally null set of size cof(N). In such a model with
  d = add(N), Theorem A gives add(UN) = add(N) while (Z2) may still fail. So (Z2) can be false
  even if the main question has a positive answer. I know no such model.

**Verdict on (Z2).** Provable in the Theorem B region (Proposition 8). Not provable by me in
the open case. Not refutable by me. It reduces to TowT(X) (sufficient) or to the empty
reformulation above (equivalent).

## 4. Step 3: attack on (Z1), add(UN) ≤ b

### 4.1 An unbounded family gives enough keys. PROVED

**Lemma 11.** In Lemma 2 of the note, for every compact K of positive measure and every c
there is g ∈ ω^ω such that every f with f(n) > g(n) for infinitely many n has
w ∈ K ∩ dom(φ_f) with φ_f(w) = c.

*Proof.* Let S be the slalom of Lemma 2 and g(n) = max(S(n) ∪ {0}). If f(n) > g(n) then
f(n) ∉ S(n). ∎

So the proof of Theorem B works with any unbounded family H ⊆ ω^ω as the set of keys. If H
is a ≤*-increasing unbounded sequence of length b, then for each (K, c) all but fewer than b
keys work. With a universally null set of size cof(N) this gives add(UN) ≤ b, which Theorem B
already gives. Recław's set of size b is not needed for this.

### 4.2 Why (Z1) is not proved. FAILED

- The keys are not the problem (Lemma 11). The points are. A union of b universally null
  sets, each of size < cof(N), must be not null. This is the same step as in 3.5.
- With Recław's set of size b as the set of codes, each piece has size ≤ b. If
  b < cf(non(N)) the union has size < non(N) and is null. So the codes must come from a set
  of size ≥ non(N), such as Grzegorek's.
- A device with whole leaves (Theorem A) needs at least cov(M) maps (`round2.json`,
  Theorem N), and b < cov(M) is consistent. So (Z1) cannot come from a leaf device.
- What remains is a tower: Tow_b with the keys φ_h, h in an unbounded family. Open.

### 4.3 The weaker targets

None of add(UN) ≤ b, add(UN) ≤ non(M), add(UN) ≤ cov(M) is proved here. Relations (PROVED
from cited facts):

- add(N) ≤ add*(N) = non(NA) ≤ non(MA) ≤ non(M). The middle step is Shelah's Theorem 2
  (read). The last is trivial: a non-meager X and the meager set {0}.
- So add(UN) ≤ add*(N) (the needed half of (Z2)) would give add(UN) ≤ non(M). The bound
  add(UN) ≤ non(M) is the weakest of the targets on the (Z2) side. It asks for a universally
  null G with X + G ∉ N, or just for |X| universally null sets with non-null union, for a
  non-meager X. I found no use of non-meagerness that avoids the step of 3.5.
- cov(M) is not bounded by add*(N): in the Cohen model add*(N) ≤ non(M) = ℵ_1 < cov(M)
  (values from memory). UNVERIFIED: add*(N) is not bounded by cov(M) either (I expect an
  ω^ω-bounding countable support iteration that localises all bounded families to give
  cov(M) ≤ d = ℵ_1 < add*(N); not checked). So add(UN) ≤ cov(M) does not follow from Plan Z.
- A proof of add(UN) ≤ cov(M) by leaves is not excluded when cov(N) ≤ cov(M) (`round2.json`,
  Claim 4). I did not find one.

## 5. Step 4: what is needed, and models

### 5.1 The missing statement

Plan Z needs exactly add(UN) ≤ add(N). Every route tried here and in `ideas.md` needs:

> **(Core)** There is a set W ∉ N with |W| < cof(N) that is the union of add(N) universally
> null sets.

PROVED: when non(N) < cof(N), (Core) is equivalent to add(UN) ≤ add(N). (Given add(N)
universally null sets with non-null union, cut them down to a non-null subset of the union of
size non(N).) So (Core) is the problem itself, stated so that the difficulty is visible: the
set W is too small to be a selector. Three ways to certify that a small set is not null are
known:

1. It meets a prescribed family of compact sets. This needs cof(N) points. (Theorem B.)
2. It contains whole leaves over a set of full outer measure. This needs at least cov(M)
   maps, and d maps for the leaves of Theorem A. (Theorem A, `round2.json`.)
3. Genericity. In a finite support iteration, sets ⋂_α [σ_α]_∞ built from Cohen reals σ_α are
   strong measure zero and catch a later Cohen real in every positive tree. (Goto,
   Theorem 5.18, read through a summary.)

A ZFC proof needs a fourth way, or a case split that covers all models. Tow_{add(N)} (3.4) is
a candidate form of a fourth way. Its status is OPEN. I do not claim that it is true.

### 5.2 Is a known model likely to violate add(UN) ≤ add(N)? SKETCH

Probably not. Reasons, none checked against the forcing papers.

- Finite support iterations: Goto's 5.18 covers iterands that are small, σ-centered, or carry
  a strictly positive finitely additive measure. The mechanism (item 3 above) seems to need
  only that Cohen reals are added cofinally over models that contain a given increasing
  function. I expect it to work for shorter iterations as well, for example length ω_2 over a
  model with c = ℵ_3 and d ≤ ℵ_2. Not written.
- Boolean ultrapowers (arXiv:1708.03691): the witness of 5.18 for regular θ is "sets X_β,
  β < θ, such that every null set contains X_β for boundedly many β". For an elementary
  embedding j with critical point κ ≠ θ, j″θ is cofinal in j(θ). The model M is closed under
  countable sequences, so M and V have the same j(P)-names for reals. Then {X_{j(β)} : β < θ}
  is a family of θ strong measure zero sets in the extension by j(P), and every null set
  contains only boundedly many. So add(SN, N) ≤ θ should survive the ultrapower. This would
  settle the first undecided model of `partial-results.md` in favour of add(UN) = add(N),
  if the first forcing of that paper satisfies the hypotheses of 5.18 with θ = add(N). I did
  not read that paper.
- A model of add(N) < add(UN) must therefore avoid: a universally null set of size cof(N)
  (in particular any ≤*-chain of length cof(N) well-ordered by a Borel relation), small d, and
  cofinal Cohen reals of the above kind. It needs c ≥ ℵ_3 and non(N) < cof(N). Finite support
  iterations and their ultrapowers seem excluded. Countable support iterations give
  c ≤ ℵ_2. I know no construction that passes all tests.

## 6. Sanity constraints

- No statement here gives fewer than add(N) universally null sets with non-null union. Lemma
  5 needs a family that is not localised, of size ≥ add*(N) ≥ add(N). Tow_κ fails for
  κ < add(N) (3.4).
- Nothing contradicts add(N) ≤ add(UN). All new inequalities are upper bounds for τ or
  add(UN) by cardinals ≥ add(N), under hypotheses.

## 7. Not checked

- Pawlikowski's 1985 paper and the book of Bartoszyński–Judah were not read. The formula rests
  on arXiv:2401.15364v3 (summary) and on Lemma 2 above.
- arXiv:2401.15364v3 and arXiv:2607.12936v4 were read through automatic summaries of the HTML,
  not line by line. Statement numbers come from these summaries.
- Shelah's proof of Theorem 13 was skimmed, not verified.
- add(N) ≤ b, the values of invariants in the Cohen and Hechler models, and all statements of
  5.2 are from memory or sketched.
- Lemma 5 and Propositions 8–10 were re-read once by their author. They are adaptations of
  Lean-checked arguments (Lemma 2, Theorem B, Grzegorek), but the adaptations are not
  Lean-checked. The points most worth a second look: (I2), and the use of pairwise
  independence only, in the width bound.
- Section 3.3 is a sketch.
- No literature search was made for Lemma 5, Corollary 7 or Tow_κ.
