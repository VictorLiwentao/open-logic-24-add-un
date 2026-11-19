# A bound on add(UN): draft note

Status (2026-11-16): one independent AI review found no error in the Lemma or the Theorem.
No human expert has checked it, and no formal proof exists.

Source question: T. Goto, *Forcing and cardinal invariants of universally null sets*,
arXiv:2607.12936v4, Question 6.3. Is add(N) < add(UN) consistent, or does ZFC prove
add(N) = add(UN)?

This note does **not** answer the question. It proves a partial upper bound.

## Notation

- `λ` is the product measure on `2^ω`; `λ²` is the product measure on `2^ω × 2^ω`.
- `N` is the null ideal, `UN` the universally null ideal, `c = 2^{ℵ_0}`, `d` the dominating number.
- `+` is coordinatewise addition mod 2 on `2^ω`.
- For strictly increasing `h : ω → ω` let `g_h(w) = w∘h` and `σ_h(c, w) = (c + w∘h, w)`.
  Each `σ_h` is a continuous involution of `2^ω × 2^ω`, so a Borel automorphism.

Known facts used (all in Goto's paper):

- (F1) UN is invariant under Borel isomorphisms between uncountable Polish spaces.
  Goto states this for `2^ω` (Lemma 5.11). The general case follows by pushing the
  measure forward along the isomorphism.
- (F2) Claim 5.5.1: if `X ∈ UN` and `f : X → 2^ω` is any function, the graph of `f` is
  universally null in `2^ω × 2^ω`.
- (F3) add(N) ≤ add(UN) ≤ non(UN) = non(N).

## Theorem

Assume there is a universally null set of cardinality `c`. Then add(UN) ≤ d.

The hypothesis holds if non(N) = c (Grzegorek), if b = c, and in the Miller model
(Goto, Corollary 2.7). It fails in the Sacks model.

The Theorem has content only when d < non(N). If b = c, or in the Miller model, then
d = c and the bound is weaker than the known add(UN) ≤ non(N).

## Lemma (graphs of sparse subsequence maps)

Let `K ⊆ 2^ω × 2^ω` be compact with `λ²(K) > 0`. There is `F_K ∈ ω^ω` such that for every
strictly increasing `h` with `h(n) ≥ F_K(n)` for all `n`, some `w` has `(w∘h, w) ∈ K`.

*Proof.* By the Lebesgue density theorem pick `m_0` and `s_0, t_0 ∈ 2^{m_0}` with
`λ²(K ∩ [s_0]×[t_0]) ≥ (3/4)·4^{-m_0}`. Put `K_0 = K ∩ [s_0]×[t_0]`. For `m ≥ m_0` let `K^(m)`
be the union of the boxes `[s]×[t]` (`s, t ∈ 2^m`) that meet `K_0`. These clopen sets
decrease to `K_0`, so `δ(m) := λ²(K^(m) \ K_0) → 0`. Choose `m_0 < m_1 < m_2 < …` with
`δ(m_k) ≤ 8^{-k}·4^{-m_0}` for `k ≥ 1`, and put `F_K(n) = m_{n+1}`.

Fix `h` strictly increasing with `h(n) ≥ m_{n+1}` for all `n`. Let `γ_h` be the law of
`(w∘h, w)` for `λ`-random `w`. For `s, t ∈ 2^m` put `j = |{i < m : h(i) < m}|`. The
coordinates `h(i)`, `i < m`, are distinct, and `m − j` of them lie outside `[0, m)`, so

  `γ_h([s]×[t]) ≤ 2^{-m}·2^{-(m−j)} = 2^j·4^{-m}`,

with equality when `j = 0`. At depth `m_0` we have `j = 0` (since `h(0) ≥ m_1 > m_0`), so
`γ_h([s_0]×[t_0]) = 4^{-m_0}`. At depth `m_k` (`k ≥ 1`) we have `j ≤ k − 1`, because
`h(i) ≥ m_{i+1} ≥ m_k` for `i ≥ k − 1`. The set `K^(m_k) \ K^(m_{k+1})` is a union of
depth-`m_{k+1}` boxes, where `j ≤ k`, so

  `γ_h(K^(m_k) \ K^(m_{k+1})) ≤ 2^k·δ(m_k)`.

Hence `γ_h(K_0) ≥ 4^{-m_0} − δ(m_0) − Σ_{k≥1} 2^k δ(m_k) ≥ 4^{-m_0}(1 − 1/4 − 1/3) > 0`.
So the graph of `g_h` meets `K_0`. ∎

## Proof of the theorem

Fix a family `D` of strictly increasing functions, `|D| = d`, such that every `F ∈ ω^ω`
is pointwise below some `h ∈ D`. Such a family exists: close a dominating family of size
`d` under finite modifications, then replace each `g` by `n ↦ max_{i≤n} g(i) + n`.
Fix `P = {c_β : β < c} ∈ UN` enumerated without
repetition, and list the compact sets of positive `λ²`-measure as `{C_β : β < c}`.

For each `β`, the set `C_β + (c_β, 0)` is compact of positive measure. By the Lemma there
are `h_β ∈ D` and `w_β` with `(w_β∘h_β, w_β) ∈ C_β + (c_β, 0)`. Put

  `q_β = σ_{h_β}(c_β, w_β) = (c_β + w_β∘h_β, w_β) ∈ C_β`.

For `h ∈ D` let `Γ_h = {(c_β, w_β) : h_β = h}` and `W_h = σ_h[Γ_h] = {q_β : h_β = h}`.

- `Γ_h` is part of the graph of the function `c_β ↦ w_β` on `P`, so `Γ_h ∈ UN` by (F2).
- `W_h ∈ UN` by (F1), since `σ_h` is a Borel automorphism.
- `⋃_{h∈D} W_h = {q_β : β < c}` meets every compact set of positive measure, so it is
  not `λ²`-null, hence not universally null.

So `d` universally null sets have a union that is not universally null. ∎

## Remarks

1. The proof gives more. Let `g` be the least size of a family of Borel functions
   `2^ω → 2^ω` whose graphs have a non-null union in the plane. Under the same hypothesis,
   add(UN) ≤ g, and the Lemma shows g ≤ d. Trivially add(N) ≤ g ≤ non(N).
   The proof needs the union of graphs to meet every compact set of positive measure,
   which is full outer measure. To get this from a non-null union, close the family under
   `f ↦ (w ↦ f(w + b) + a)` for finite-support `a, b`. The size does not change, and the
   measurable hull of the union is then invariant under finite changes, so it has
   measure 1 by the 0-1 law.
2. Consequence for Question 6.3: a model of add(N) < add(UN) that has a universally null
   set of size `c` must satisfy add(N) < g ≤ d. So proper `ω^ω`-bounding iterations over a
   CH ground model that force non(N) = c cannot work.
3. Not settled here: whether add(N) < add(UN) is consistent. Candidates left open include
   the Mathias model (b = d = non(N) = c, cov(M) = ℵ_1).
4. Prior work. The Lemma is essentially known: it says non(N) ≤ d after adding one random
   real. See Bartoszyński, Rosłanowski and Shelah, "Adding one random real",
   arXiv:math/9406229, Theorem 1.1(3), attributed there to Krawczyk. The reviewer fetched
   this record, but the inequality signs were lost in extraction, so the direction is
   inferred and must be confirmed from the PDF. Pawlikowski's and Krawczyk's original
   papers were not checked.
5. A brief search found no earlier statement of the Theorem. This is not a full
   literature search.
