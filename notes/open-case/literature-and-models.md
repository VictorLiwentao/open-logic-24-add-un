# Open case, round 3: literature and the consistency side

Status (2026-11-19). Written by one AI agent (Claude) in one session. Nobody has checked it.
Section 1 reports what was read. Section 2 contains new deductions by the agent. They are
short, but they are **not refereed**. Section 3 is an opinion, not a proof.

Notation as in `notes/partial-results.md`. SN is the strong measure zero ideal. NA is the
ideal of null-additive sets (X is in NA if X + G is null for every null G). "Theorem B" is
the note's Theorem B: a universally null set of size cof(N) gives add(UN) = add(N).

## 0. Summary

- No source settles Question 6.3. No source later than Goto's paper mentions add(UN).
- The formula add(N) = min{b, add\*(N)} used in Plan Z is correct. It is Pawlikowski's
  Lemma 2.3 (1985), as quoted in arXiv:2401.15364. Here add\*(N) = non(NA).
- New deduction (Section 2.1): after a finite support iteration of ccc forcings of
  uncountable cofinality there is a strong measure zero set of size c. So Theorem B gives
  add(UN) = add(N) in **every** such model. No goodness hypothesis is needed. The same holds
  after adding one Cohen real, in the Boolean ultrapower models, and in the shattered
  iteration models as they are stated in Brendle's paper.
- New deduction (Section 2.2): a measured extension (Larson–Zapletal) and a random extension
  keep ground model universally null sets universally null. So add(UN) cannot go up in such
  an extension.
- Consequence: the three models listed as "Not decided" in `partial-results.md` are decided
  (equality holds), if Section 2.1 is right. For shattered iterations this needs a ground
  model whose continuum is the final cof(N), as in Brendle's theorems. I know no forcing
  construction that survives.
- New separation: add(UN) = add(N) = b < non(NA) ≤ add(SN) is consistent, with c = ℵ_2
  (Pawlikowski's model) and with c large (Cardona–Mejía, Theorem 5.15).
- My guess: ZFC proves add(UN) = add(N). Confidence about 65%. See Section 3.

## 1. Literature

### 1.1 Table of sources

"full" means I read the passages that matter in the full text (TeX or extracted PDF text),
not every page. "second-hand" means I read the statement only as quoted in another paper.

| # | Source | Read | What it gives |
| --- | --- | --- | --- |
| 1 | T. Goto, *Forcing and cardinal invariants of universally null sets*, arXiv:2607.12936v4 (2026). https://arxiv.org/abs/2607.12936 | full (TeX: Sections 1, 3, 5.5, 5.6, 6) | The question. add(UN) = add(UN,N) ≤ add(SN,N). Theorem on PT_{f,g}. Theorem 5.18. |
| 2 | M. A. Cardona, D. A. Mejía, I. E. Rivera-Madrid, *Uniformity numbers of the null-additive and meager-additive ideals*, arXiv:2401.15364v3 (2024; J. Symb. Logic 2025). https://arxiv.org/abs/2401.15364 | full (TeX: introduction, Section 2 statements) | Pawlikowski's formulas. add(NA) = non(NA). non(NA) ≤ add(SN). Open questions on add(SN). |
| 3 | M. A. Cardona, *Cohen real or random real: effect on strong measure zero sets and strongly meager sets*, arXiv:2005.07912v2 (2020). https://arxiv.org/abs/2005.07912 | full (TeX: abstract, Theorem A, proof of (i)) | After one Cohen real the ground model reals have strong measure zero. |
| 4 | M. A. Cardona, D. A. Mejía, *On cardinal characteristics of Yorioka ideals*, arXiv:1703.08634v2 (2017; MLQ 65 (2019)). https://arxiv.org/abs/1703.08634 | full (TeX: last theorem of Section 5 and its proof) | A model of add(N) = b = μ < minLc = ν, d = c = λ. |
| 5 | J. Brendle, M. A. Cardona, D. A. Mejía, *Separating cardinal characteristics of the strong measure zero ideal*, arXiv:2309.01931v2 (2023; J. Math. Logic 2025). https://arxiv.org/abs/2309.01931 | full (TeX: history paragraph of the introduction, Section 8 questions) | History of add(SN). Open: add(N) < add(SN) < b and add(N) < b < add(SN). |
| 6 | J. Brendle, *Shattered Iterations*, arXiv:2302.05069v1 (2023). https://arxiv.org/abs/2302.05069 | full (TeX: abstract, Main Theorem B, Facts 1–3, the corollaries on add(N) and cof(N), the theorem on Hechler forcing) | Values in the shattered models. Cohen reals are added on top of every amalgamated stage. |
| 7 | P. Larson, J. Zapletal, *Polar forcings and measured extensions*, author copy dated 2022-02-02 (text file left by an earlier agent; Goto cites Topology Appl. 323 (2023)) | full (Definition 5.1, Propositions 5.2–5.4, statement of Theorems 5.6 and 5.12) | Definition of measured extension. Bounding. Outer measure is preserved. |
| 8 | A. W. Miller, *Special subsets of the real line*, Handbook of Set-Theoretic Topology (1984), OCR text left by an earlier agent | part (page 214) | "theorem of Baumgartner and Laver": in the random real model every universal measure zero set has size ≤ ω_1, and c can be large. |
| 9 | P. Larson, I. Neeman, S. Shelah, *Universally measurable sets in generic extensions*, arXiv:1003.2479 (2010). https://arxiv.org/abs/1003.2479 | part (introduction, Theorem 2.8, last page) | Same statement for the B(c) extension of a CH model and the iterated random model. Sacks model via CPA. |
| 10 | J. Brendle, P. Larson, *Nonmeager universally null sets*, note of 2017-06-08. https://paulblarson.github.io/umeas_ctx.pdf | full (2 pages, text left by an earlier agent) | min{d, non(N)} = cof(M) gives a universally null set of size cof(M). |
| 11 | I. Recław, *Some additive properties of special sets of reals*, Colloq. Math. 62 (1991), 221–226 | full (pages 221–223, text left by an earlier agent) | Lemma 1, Theorems 1–3 on X + Y for universally null sets. All need a universally null set of size c. |
| 12 | M. Hrušák, O. Zindulka, *Strong measure zero in Polish groups*, arXiv:1911.03832 (2019). https://arxiv.org/abs/1911.03832 | search of the TeX for "universal measure zero"; the hits were read | Only: strong measure zero implies universal measure zero (Szpilrajn); non of "not universal measure zero" is non(N). Nothing on additivity or translates of universally null sets. |
| 13 | O. Zindulka, *Null-additive sets and packing measures*, arXiv:2610.05283v1 (2026). https://arxiv.org/abs/2610.05283 | abstract; TeX searched for "universal" (no hit) | Strict measure zero is the same as null-additive in the Cantor set. Not about UN. |
| 14 | O. Zindulka, *Strong measure zero and meager-additive sets through the prism of fractal measures*, arXiv:1802.08574 (2018) | TeX searched for "universal"; hits read | Sharp measure zero sets are universally meager. Nothing on UN. |
| 15 | M. Korch, T. Weiss, *On the class of perfectly null sets and its transitive version*, arXiv:1609.04005 (2016) | abstract and first page | Consistently there is a universally null set that is not perfectly null in the transitive sense. No cardinal invariants. |
| 16 | M. Goldstern, J. Kellner, S. Shelah, *Cichoń's maximum*, arXiv:1708.03691v3 (2017; Ann. Math. 190 (2019)) | part (introduction, statement of the lemma on j(P)) | The final forcing is j(P) for a finite support ccc iteration P. |
| 17 | J. Kellner, S. Shelah, A. R. Tanasie, *Another ordering of the ten cardinal characteristics in Cichoń's diagram*, arXiv:1712.00778v2 (2017) | search of the TeX only | "P is a FS ccc iteration of length δ_5". |
| 18 | M. Goldstern, J. Kellner, D. A. Mejía, S. Shelah, *Cichoń's maximum without large cardinals*, arXiv:1906.06608v2 (2019) | search of the TeX only | P ∩ N is a complete subforcing of P; names for reals correspond. |
| 19 | J. Pawlikowski, *Powers of transitive bases of measure and category*, Proc. Amer. Math. Soc. 93 (1985) | UNFETCHED (AMS returned HTTP 403). Second-hand from 2 and 5 | Lemma 2.2, Lemma 2.3, Theorem 2.4. |
| 20 | J. Kraszewski, *Transitive properties of ideals on generalized Cantor spaces*, Bull. Pol. Acad. Sci. Math. 52 (2004) | search snippet of the abstract only | Transitive coefficients on 2^κ. No sign of UN. |
| 21 | T. Bartoszyński, H. Judah, *Set Theory: On the Structure of the Real Line*, Sections 2.7, 8.4 | UNFETCHED. Second-hand from 2 and 5 | add\*(N); models with add(SN) large. |
| 22 | K. Ciesielski, J. Pawlikowski, *The Covering Property Axiom, CPA* (2004), Theorem 1.1.4 | UNFETCHED. Second-hand from 1 and 9 | In the Sacks model every universally null set has size ≤ ℵ_1. |
| 23 | M. Goldstern, H. Judah, S. Shelah, *Strong measure zero sets without Cohen reals*, arXiv:math/9306214 | not re-read (earlier agents read it). Second-hand from 5 | cof(M) = ℵ_1 < add(SN) = ℵ_2 = c. |
| 24 | T. Goto, *Goldstern's principle about unions of null sets*, arXiv:2206.08147 (2022); *Goldstern's Principle with respect to Hausdorff Measures*, arXiv:2512.22852 (2025) | abstracts | About unions of monotone families of null sets indexed by reals. Not about UN. |
| 25 | M. A. Cardona, D. A. Mejía, I. E. Rivera-Madrid, *Directed schemes of ideals and cardinal characteristics, I: the meager additive ideal*, arXiv:2512.00235 (2025) | abstract | Meager-additive ideal only. |
| 26 | O. Zindulka, *Universal measure zero, large Hausdorff dimension, and nearly Lipschitz maps*, Fund. Math. 218 (2012) | UNFETCHED (an earlier agent read the abstract) | Not used. |
| 27 | A. Cieślak, *Combinatorics of translations of meager and closed measure zero sets*, arXiv:2609.28669 (2026) | not re-read (an earlier agent read it) | Not used. |

Searches run on 2026-11-19. arXiv API, all fields, newest first: "universally null",
"universal measure zero", "strong measure zero", "null-additive", "transitive additivity".
Web search: Goto's title with "cited"; MathOverflow with "universally null" and additivity;
Kraszewski; Pawlikowski. Result: in 2026 only Goto's paper and J. Z. Chen's arXiv:2608.21649
have "universally null" in the metadata. No MathOverflow thread was found. No paper citing
Goto was found. These searches see titles and abstracts only.

### 1.2 Task (a): translates, null-additive sets, transitive additivity

1. **Pawlikowski's formula is confirmed, second-hand.** Source 2 states as Theorem 1.8,
   attributed to Pawlikowski's Lemma 2.3: add(N) = min{b, non(NA)} and
   add(M) = min{b, non(MA)}. The same source says non(NA) is the transitive additivity,
   written add\*(N) in Bartoszyński–Judah. So the formula in `ideas.md`, Section 2, is right.
2. Source 2 also gives: non(NA) = minLc, where minLc is the least size of a subset of some
   product ∏b (b in ω^ω) that no slalom of width n localises (Pawlikowski, Lemma 2.2).
   add(NA) = non(NA) in ZFC (their Theorem A). non(NA) ≤ add(SN) (stated by Pawlikowski,
   first proved in source 2). NA ⊆ MA ⊆ SN.
3. **No result of the form "X small, G universally null, X + G not null" was found.** The
   closest results are Recław's (source 11). Theorem 2: if X is universally null of size c
   and lies in a meagre F_σ set C with C − X meagre, then some universally null Y has
   Y − X ⊇ a perfect set. Theorem 3: under MA, for every X of size c there is a universally
   null Y with X + Y not universally null. Both need |X| = c. His Lemma 1(b) is the
   translation form of the note's Lemma 3: Y = {x + d_x : x in X} is a one-to-one Borel
   preimage of X.
4. The papers on strong measure zero, sharp measure zero and strict measure zero in Polish
   groups (sources 12, 13, 14) do not study universally null sets beyond SN ⊆ UN.
5. An easy remark (mine). Put T = min{|X| : X + G is not null for some universally null G}.
   Then add(UN) ≤ T and non(NA) ≤ T ≤ non(N). (Z2) is the statement T = non(NA). What
   Plan Z uses is its consequence add(UN) ≤ non(NA).

### 1.3 Task (b): add(UN,N), add(SN,N), add(SN)

1. The names add(UN,N) and add(SN,N) occur only in Goto's paper (source 1). There:
   add(UN,N) = add(UN), and add(N) ≤ add(UN) ≤ add(SN,N), add(N) ≤ add(SN) ≤ add(SN,N).
   Fremlin 544L (see `partial-results.md`) is the only older statement on unions of
   universally null sets.
2. Known about add(SN), from sources 2 and 5:
   - add(N) ≤ non(NA) ≤ add(SN) (Carlson for the outer inequality; source 2).
   - b = ℵ_1 < add(SN) = c = ℵ_2 is consistent (Pawlikowski 1985, finite support iteration).
     Source 2 gives the full values of this model:
     add(N) = add(M) = b = ℵ_1 < non(NA) = non(MA) = c = ℵ_2.
   - cof(M) = ℵ_1 < add(SN) = ℵ_2 = c is consistent (Goldstern–Judah–Shelah).
   - d = ℵ_1 < add(SN) = cov(N) = ℵ_2 is consistent (Bartoszyński–Judah, Theorem 8.4.11).
   - add(SN) = ℵ_1 < add(M) = c = ℵ_2 is consistent (Judah–Shelah).
   - Source 4, last theorem of Section 5 (Theorem 5.15 in the numbering of source 2): for
     regular μ ≤ ν and λ = λ^{<μ} ≥ ν there is a ccc poset forcing add(N) = b = μ,
     minLc = ν, non(M) = cov(M) = ν, d = c = λ. It is a finite support iteration of length
     λν of the localisation posets LOC_b for bounded products, and of small ccc posets.
     Since minLc = non(NA) ≤ add(SN), this model has add(SN,N) ≥ ν > add(N) with c large.
   - Open (source 5, Section 8; repeated in source 2): is add(N) < add(SN) < b consistent?
     Is add(N) < b < add(SN) consistent?
3. So add(SN,N) > add(N) is consistent, in several ways. Whether add(SN,N) = add(SN) in ZFC
   is not discussed anywhere I looked.
4. ZFC upper bounds. For add(SN,N): only the trivial ones, add(SN,N) ≤ non(N) and
   add(SN,N) ≤ cov(SN). It is **not** bounded by d or by cof(M) (the models above). For
   add(UN): min{d, cf(non(N)), cov(UN), add(SN,N)}, where add(UN) ≤ d is the note's
   Theorem A and cov(UN) ≤ cov(SN).

### 1.4 Task (c): models where all universally null sets are small

| Model | Universally null sets | non(N) | d | cof(N) | Source |
| --- | --- | --- | --- | --- | --- |
| Sacks model | all of size ≤ ℵ_1 | ℵ_1 | ℵ_1 | ℵ_1 | 22, quoted in 1 and 9 |
| Random model, B(κ) over CH, κ arbitrary | all of size ≤ ℵ_1 | ℵ_1 | ℵ_1 | c | 8 (Baumgartner–Laver), 9 |
| PT_{f,g} model (countable support, length ω_2, over CH) | all of size ≤ ℵ_1 | ℵ_1 | ℵ_1 | ℵ_2 = c (as non(M) = c) | 1, Section 3 |
| Any measured extension of a CH model | (see Section 2.2) | ℵ_1 | ℵ_1 | — | 7 |
| Miller model | one of size c = ℵ_2 exists | ℵ_1 | ℵ_2 | ℵ_2 | 1, Section 2 |

The values of non(N), d, cof(N) in the Sacks and random models are standard. I did not fetch
a source for them. For the PT_{f,g} model, d = ℵ_1 < non(M) = c is in Goto's introduction;
non(N) = ℵ_1 follows from Grzegorek's theorem, or from Proposition 5.4 of source 7.

Answer to the question in the task. "Every universally null set has size < cof(N)" is
consistent with non(N) < cof(N): the random model and the PT_{f,g} model. In all models I
found, this is obtained together with non(N) = d = ℵ_1. Then add(UN) = ℵ_1 for trivial
reasons. **I found no model with non(N) ≥ ℵ_2 in which every universally null set has size
< cof(N).** A counterexample to add(UN) = add(N) must be such a model.

### 1.5 Task (d): work after Goto's paper

Nothing found. arXiv:2607.12936 is at v4 (2026-10-09). The acknowledgments thank D. Mejía and
T. van der Vlugt. The two 2026 papers of Reznichenko and Sadovnichiy (arXiv:2609.14414,
arXiv:2611.13821) and Chen's paper were searched by earlier agents and do not concern
add(UN). Google Scholar, MathSciNet and zbMATH were not queried.

## 2. New deductions (not refereed)

### 2.1 Cohen capture

**Fact (Cardona, source 3, Theorem A(i); mentioned by Laver, sketched by Goldstern).** If c
is a Cohen real over V, then V[c] ⊨ "2^ω ∩ V has strong measure zero".

**Corollary 1.** If W = V[c] for a Cohen real c over V, then W ⊨ add(UN) = add(N).

*Proof.* In W the set 2^ω ∩ V has strong measure zero, so it is universally null. Its size is
the continuum of V, which is the continuum of W, so it is at least cof(N)^W. Apply
Theorem B in W. ∎

So one Cohen real forces add(UN) = add(N). The same holds for one Hechler real (source 3).

**Proposition P.** Let ⟨P_α, Q_α : α < π⟩ be a finite support iteration of nontrivial ccc
posets with cf(π) > ω. Then V^{P_π} ⊨ "there is a strong measure zero set of size c". Hence
V^{P_π} ⊨ add(UN) = add(N).

*Proof.* Write V_α for the extension by P_α. Facts used: every real of V_π is in some V_α,
α < π (ccc and cf(π) > ω); the steps in [α, α+ω) add a Cohen real over V_α, for α = 0 or
α a limit. Number the blocks [ωξ, ωξ+ω). For even ξ let c_ξ in V_{ωξ+ω} be Cohen over
V_{ωξ}. Put

  U = ⋃ { c_ξ + (2^ω ∩ V_{ωξ}) : ξ even }.

Size: U contains a translate of 2^ω ∩ V_{ωξ} for cofinally many stages, and
2^ω ∩ V_π is the union of these sets, and the c_ξ are distinct. So |U| = c.

Strong measure zero: let f in V_π be increasing. Take an odd ξ with f in V_{ωξ}. From the
Cohen real of block ξ get σ in ∏_n 2^{f(n)} that is Cohen over V_{ωξ}. Let
D_σ = {x : σ(n) ⊆ x for infinitely many n}. Take a point c_ζ + x of U, with ζ even and x in
V_{ωζ}. If ζ < ξ, the point is in V_{ωξ}, and genericity of σ over V_{ωξ} puts it in D_σ.
If ζ > ξ, then σ is in V_{ωζ}; the set D_σ is a dense G_δ coded in V_{ωζ} (the strings
σ(n), n ≥ m, are dense in 2^{<ω} for every m); and c_ζ + x is Cohen over V_{ωζ}; so it is in
D_σ. Hence U ⊆ D_σ ⊆ ⋃_n [σ(n)], and |σ(n)| = f(n). ∎

The argument uses only this: W is the union of an increasing chain of models of uncountable
cofinality, every real of W is in a member of the chain, and Cohen reals are added
cofinally. A weaker form needs no chain:

**Lemma CC.** Let M be an inner model of W. Suppose every real f of W lies in a model N
with M ⊆ N ⊆ W such that W contains a Cohen real over N. Then 2^ω ∩ M has strong measure
zero in W. If also |2^ω ∩ M| ≥ cof(N)^W, then W ⊨ add(UN) = add(N).

**Consequences for the list of models in `partial-results.md`.**

1. Every finite support ccc iteration of uncountable cofinality satisfies add(UN) = add(N).
   This covers Mejía's matrix-iteration theorems and Theorem D of Brendle–Cardona–Mejía
   without Goto's Theorem 5.18 and without checking that the iterands are good. It also
   covers the Cardona–Mejía model of 1.3, where 5.18 cannot apply because add(SN,N) > add(N).
2. Boolean ultrapowers (sources 16, 17). The final forcing is j(P), where P is a finite
   support ccc iteration and M is closed under countable sequences. So j(P) is a finite
   support ccc iteration of length j(δ), and cf(j(δ)) is uncountable. Proposition P applies.
   Caveat: I read the introduction of source 16 and the statement of its lemma on j(P). I
   did not check every detail of the construction. For source 17 I only searched the text.
3. Submodel method (source 18). P ∩ N is a complete subforcing of P, every P ∩ N-name for a
   real is a name in N for some P_α ∩ N with α in π ∩ N, and the Cohen real of the next
   block has a name in N. So the proof of Proposition P goes through for the chain
   ⟨P_α ∩ N : α in π ∩ N⟩. This replaces Proposition C of round 2. Same caveat.
4. Shattered iterations (source 6). The paper states: 𝔸 is the direct limit of the
   𝔸^{ζ,η}_{ζ,η}; fewer than κ names for reals are names for one 𝔸^{ζ,η}_amal; and
   𝔸^{ζ,η}_{ζ,η} adds a Cohen real c_{ζ,η} over the 𝔸^{ζ,η}_amal-extension (proof of
   Fact 1; for Hechler iterands a Cohen real is decoded from the Hechler real). By Lemma CC
   the ground model reals have strong measure zero in the extension. The corollary on the
   Cohen version and the theorem on the Hechler version assume cof(N) = c = ν in the ground
   model and prove the same in the extension. So the ground model reals have size
   cof(N) of the extension, and add(UN) = add(N) = ℵ_1 there. If the ground model satisfies
   GCH instead, then c = λ in the extension and the ground model reals are too few. I
   expect that the set of Cohen reals of the first row, or a set like U, still has strong
   measure zero. I did not prove this.

**Remark (variant of Theorem B).** Suppose cof(N) is the sum of τ cardinals, each the size
of a universally null set. Split the cofinal family in the proof of Theorem B into τ pieces
and use one universally null set for each piece. This gives add(UN) ≤ max{add(N), τ}. It
gives nothing new when τ ≥ cf(non(N)).

### 2.2 Inheritance

**Lemma I1.** If N_1 is a measured extension of N_0 (source 7, Definition 5.1) and A in N_0
is universally null in N_0, then A is universally null in N_1.

*Proof.* Suppose not. In N_1 take an atomless Borel probability measure μ_1 and a rational
ε > 0 with outer measure μ_1\*(A) > ε. In N_0 let F be the family of all sets B ∖ C, with B
a Borel set containing A and C countable. For such a set, i(B) contains A, and μ_1 gives
measure 0 to C, so μ_1(i(B ∖ C)) ≥ ε. By clause 2 of Definition 5.1 there is in N_0 a Borel
probability measure μ_0 with μ_0(B ∖ C) ≥ ε for all B, C. Let C be the set of atoms of μ_0.
Then the atomless part of μ_0 gives every Borel B ⊇ A measure ≥ ε. So A is not universally
null in N_0. ∎

**Lemma I2.** Random forcing (any measure algebra) preserves universally null sets.

*Proof.* Let μ̇ be a name for an atomless Borel probability measure. In V put
ν(B) = E[μ̇(B)], the expected value. It is a Borel probability measure, and
ν({x}) = E[μ̇({x})] = 0. If A is universally null, take a Borel B ⊇ A with ν(B) = 0. Then
μ̇(B) = 0 is forced. ∎

**Corollary 2.** Let N_1 be a measured extension, or a random extension, of N_0. Then
add(UN)^{N_1} ≤ add(UN)^{N_0}.

*Proof.* A family of universally null sets of N_0 with a non-null union stays a family of
universally null sets (I1, I2), and its union stays non-null (source 7, Proposition 5.4;
classical for random forcing). ∎

Use: if W is such an extension of an inner model M with c^M ≤ ℵ_2, then
add(UN)^W ≤ add(UN)^M = add(N)^M by Corollary (b). So W is a counterexample only if
add(N)^W < add(N)^M. For a countable support product or iteration of polar forcings this
fails: a witness for add(N)^W = ℵ_1 is coded by ℵ_1 reals and lies in an intermediate model
of the same kind.

### 2.3 Two separations that follow

1. In Pawlikowski's model (values from source 2): c = ℵ_2, so Corollary (b) gives
   add(UN) = add(N) = b = ℵ_1 < non(NA) = add(SN) = add(SN,N) = ℵ_2.
2. In the Cardona–Mejía model: by Proposition P,
   add(UN) = add(N) = b = μ < ν = non(NA) ≤ add(SN) ≤ add(SN,N), with c = λ arbitrary large.

So "non(NA) ≤ add(UN)" is not a theorem, and Goto's bound add(UN) ≤ add(SN,N) can be strict
with large continuum. Remark 5 of `partial-results.md` had this only for c = ℵ_2 and for
the Goldstern–Judah–Shelah model.

## 3. Assessment of the consistency side

### 3.1 What a model of add(N) < add(UN) must look like

Let W be such a model. Then:

1. c ≥ ℵ_3, non(N) < cof(N), b < cof(N), add(N) < add(UN) ≤ min{d, cf(non(N)), add(SN,N)}
   (the note, Goto).
2. Every universally null set has size < cof(N). In particular every strong measure zero
   set, every set well-ordered by a Borel relation, and every ≤\*-chain has size < cof(N).
3. By Pawlikowski's formula there are two cases.
   Case (i): add(N) = b < add(UN). Then (Z1) fails.
   Case (ii): add(N) = non(NA) < b and non(NA) < add(UN). Then the bound of (Z2) fails.
4. W is not a Cohen or Hechler extension of an inner model with at least cof(N)^W reals. W
   is not a finite support ccc iteration of uncountable cofinality (Section 2.1).
5. W is not a measured or random extension of an inner model M with
   add(UN)^M ≤ add(N)^W (Section 2.2).
6. d ≥ ℵ_2 and non(N) ≥ ℵ_2. So W is not an ω^ω-bounding extension of a model of CH.

### 3.2 The simplest candidates, and where they fail

**Candidate A (finite support, outside Goto's Theorem 5.18).** Take the Cardona–Mejía
iteration with μ = ℵ_1, ν = ℵ_2, λ ≥ ℵ_3, and add restricted random posets so that
non(N) = ν. The localisation posets LOC_b raise non(NA) and so add(SN,N), and they add no
dominating reals. The numerical conditions hold: add(N) = b = ℵ_1 < ℵ_2 = non(N) =
add(SN,N) < cof(N) = d = c. Theorem 5.18 cannot apply with θ = ℵ_1, because its conclusion
add(SN,N) ≤ ℵ_1 is false in this model. I did not find the value of non(N) in source 4; the
restricted random posets are my addition and are not checked. What one would need: "every union of ℵ_1 universally null sets is null". First obstacle:
it is false. By Proposition P the model has a strong measure zero set of size c. No
preservation theorem can help. This kills every construction that adds Cohen reals
cofinally.

**Candidate B (no Cohen reals).** Start with V_1 ⊨ add(N) = c = ℵ_2 (for example MA). Force
with a product of ℵ_3 proper ω^ω-bounding definable forcings with countable support, of
creature or PT_{f,g} type. Aim: b = d = ℵ_2 (bounding); add(N) = non(NA) = ℵ_1 and
cof(N) = c = ℵ_3 (generic reals that no slalom from the other coordinates localises);
universally null sets of size ≤ ℵ_2 (Goto's argument for PT_{f,g}, using measured
extensions). This is Case (ii). What one would need: a preservation theorem of the form
"if M is an intermediate model given by ℵ_1 or ℵ_2 coordinates, then every family of ℵ_1
universally null sets of W has a null union". First obstacle: a dilemma about the tail
forcing over an intermediate model M with c^M = ℵ_2 and add(N)^M = ℵ_1. In M there are ℵ_1
universally null sets with a non-null union (Corollary (b) in M).
- If the tail preserves universally null sets and outer measure (as measured extensions
  do), the witness survives and add(UN)^W = ℵ_1 (Corollary 2).
- If every coordinate makes the reals of the other coordinates null, then non(N) = c and
  Corollary (a) applies.
- If ℵ_1 coordinates add Cohen reals over the rest, or reals that are infinitely often
  equal over the rest in every product ∏ 2^{f(n)}, then the reals of the model given by
  the other coordinates form a strong measure zero set of size c.
So the tail must make some non-null sets of M null, keep 2^ω ∩ M non-null, and not make
big sets strong measure zero. I know no forcing with these properties. I also do not know
that the product preserves ℵ_2 over a model of ¬CH.

**Candidate C (shattered iterations).** See 2.1, item 4. Dead in the form stated in the
paper. Probably dead in general.

I found no construction that satisfies all conditions of 3.1. The first obstacle is always
the same: every known way to get c ≥ ℵ_3 with non(N) ≥ ℵ_2 either adds Cohen reals over
large inner models, or is a tame (measured, bounding) extension of small inner models.

### 3.3 Which answer is more likely

My guess: ZFC proves add(UN) = add(N). Confidence about 65%.

For equality:
- Theorem B, Corollary (b), Theorem A, Proposition P and Corollary 2 together give equality
  in every model that present methods build. One Cohen real restores equality.
- The only known lower bound for add(UN) is add(N), and it is proved one measure at a time.
  For SN there is a structural lower bound, non(NA) ≤ add(SN), and it does **not** transfer:
  add(UN) < non(NA) is consistent (2.3).
- A counterexample needs non(N) ≥ ℵ_2 and no universally null set of size cof(N). No such
  model is known. In all known models with small universally null sets, non(N) = ℵ_1.

Against:
- ZFC does not prove that a universally null set of size cof(N) exists (random model). All
  ZFC arguments so far need cof(N) codes, or pay cov(M) or d.
- The missing models may only show a limit of the methods. Statements that need c ≥ ℵ_3
  and four distinct values are hard to force in general.

### 3.4 Check of Plan Z and Scheme GS

Nothing I found contradicts Plan Z or Scheme GS. Details:

1. The formula add(N) = min{b, add\*(N)} is correct (1.2).
2. Plan Z is not weaker than the problem. Since add(N) = min{b, non(NA)}, the statement
   add(UN) = add(N) is **equivalent** to "add(UN) ≤ b and add(UN) ≤ non(NA)". So (Z1) and
   the bound of (Z2) are exactly the two halves of the problem (3.1, item 3).
3. Neither half can be dropped. add(UN) = b < non(NA) holds in the models of 2.3. A model
   of add(UN) = non(NA) < b: any model of add(N) < b with c ≤ ℵ_2, for example the Hechler
   model (add(N) = ℵ_1 < b = c = ℵ_2; standard values, not fetched).
4. No model is known with b < add(UN), and none with non(NA) < add(UN). Each would be a
   counterexample to the whole question.
5. (Z2) with translation keys is Scheme GS with the keys z ↦ z − x, x in X. Recław's
   Lemma 1(b) is the same device, used with a universally null set of size c.
6. Scheme GS with |I| = non(N) holds trivially. So GS has content only when
   add(N) < non(N). Corollary 1 shows that a scheme of this kind works in V[c] with the
   code set 2^ω ∩ V in place of the Grzegorek set. The difficulty (O3)/(O4) is the size of
   the code set, as in Theorem B. I found nothing in the literature on (O1)–(O4).
7. A warning for (Z2). The set G must have size ≥ non(N). In the Cohen model, the sum of ℵ_1
   Cohen reals and the Lusin set of all Cohen reals is null (all its points are Cohen over
   V). So the obvious choice of G fails there, although add(UN) = ℵ_1 holds in that model.

## 4. What I could not reach

- Pawlikowski 1985 (HTTP 403), Bartoszyński–Judah's book, Ciesielski–Pawlikowski's book,
  Kraszewski's papers (abstract snippet only), Zindulka's Fund. Math. paper, Carlson's and
  Yorioka's papers. All statements from them are second-hand, as marked in the table.
- Google Scholar, MathSciNet, zbMATH. arXiv full text is not searchable.
- I did not read the constructions of sources 16–18 in detail. Items 2 and 3 of 2.1 rest on
  a few quoted lines.
- I did not verify the amalgamation structure of shattered iterations beyond the lines
  quoted in 2.1, item 4. The GCH case there is open.
- Standard values in the random and Sacks models are from memory.
- Proposition P, Lemma CC, Lemmas I1, I2 and the corollaries have no second reader. They
  all rest on Theorem B. Proposition P may be folklore; I did not find it stated.

## 5. Suggested edits to `partial-results.md` (not made)

- "Models": replace the three "Not decided" items by a reference to Section 2.1 here, with
  the caveats.
- Remark 5: add the two separations of Section 2.3.
- "Still undecided in ZFC": note that add(UN) ≤ b and add(UN) ≤ non(NA) together are
  equivalent to add(UN) = add(N).

The fetched texts are not in this repository.
