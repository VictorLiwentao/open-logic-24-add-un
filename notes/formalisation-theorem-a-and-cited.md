# Lean formalisation of Theorem A and the cited results

Status (2026-11-19). Every statement of `AddUN/Statements.lean` except the open question
`Question63` has a kernel-checked Lean proof. The proofs were written by an AI agent (Claude).
No human has reviewed the Lean code or the definitions.

## What is proved

| `Prop` in `Statements.lean` | Theorem | File |
| --- | --- | --- |
| `GotoCor513`: add(N) ≤ add(UN) | `gotoCor513` | `AddUN/Additivity.lean` |
| `GotoProp54`: non(UN) = non(N) | `gotoProp54` | `AddUN/Uniformity.lean` |
| `Grzegorek`: a universally null set of size non(N) | `grzegorek` | `AddUN/Grzegorek.lean` |
| `TheoremA`: add(UN) ≤ d | `theoremA` | `AddUN/TheoremA.lean` |
| `TheoremB` | `theoremB` | `AddUN/Main.lean` |
| `CorollaryA`, `CorollaryB`, `CorollaryC` | `corollaryA`, `corollaryB`, `corollaryC` | `AddUN/Main.lean` |

Also in `AddUN/Main.lean`:

```lean
theorem add_null_eq_add_universallyNull_of_continuum_le_aleph_two
    (h : (𝔠 : Cardinal.{0}) ≤ ℵ_ 2) : add 𝒩 = add 𝒰𝒩
theorem add_universallyNull_le_min : add 𝒰𝒩 ≤ min dominatingNumber (non 𝒩)
```

No theorem has a hypothesis that stands for an unproved claim. No statement in
`AddUN/Statements.lean` was changed.

Output of `#print axioms`, the same for each of `gotoCor513`, `gotoProp54`, `grzegorek`,
`theoremA`, `theoremB`, `corollaryA`, `corollaryB`, `corollaryC`,
`add_null_eq_add_universallyNull_of_continuum_le_aleph_two`, `add_universallyNull_le_min` and
`add_universallyNull_le_add_null`:

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake build` passes with no warning. The project has no `sorry`, no `axiom` and no
`native_decide`.

## What is not proved

- `Question63` (add(N) = add(UN) in ZFC) is open. It is a `def`, not a theorem.
- The note's Corollary (c) also states b < cof(N) and add(UN) ≤ min(d, cf(non(N))). The Lean
  `CorollaryC` does not contain these parts. Recław's theorem is not formalised.

## What a reviewer should check

The kernel checks the proofs, not the definitions. A reviewer should read:

- `IsUniversallyNull`, `cantorMeasure`, `Measure.nullSets` in `AddUN/UniversallyNull.lean`;
- `add`, `non`, `cof` in `AddUN/IdealInvariant.lean`;
- `dominatingNumber` and the `Prop`s in `AddUN/Statements.lean`.

The three cited results are proved by routes that differ from the sources. The papers of
Goto, Grzegorek and Recław were not used for these proofs. The proofs below are therefore new
text that only Lean has checked.

## The proofs

### `GotoCor513`: add(N) ≤ add(UN)

Goto uses the measure isomorphism theorem. The Lean proof uses slaloms, with the width
`h(n) = 2^{3 μ_n + n}` of the coding lemma (Lemma 2 of the note).

1. `exists_localising_slalom`. One slalom of width `h` localises every member of a family `F`
   of fewer than add(N) functions. For each `f` the set of the points with a marker at
   `(n, f(n))` for infinitely many `n` is null (Borel–Cantelli). The union over `F` is null.
   Take a compact `K` of positive measure disjoint from it, and the slalom `S` of the coding
   lemma for `K` and the code `0`. If `f ∈ F` escapes `S`, the coding lemma gives `w ∈ K` with
   `decode f w = 0`. Bit `0` of the code is `false` only if `w` has infinitely many markers
   along `f`. This contradicts the choice of `K`.
2. `measure_sUnion_null_of_localised`. This is the argument of Lemma 1 for an arbitrary finite
   measure `μ` on the Cantor space: if every family of at most `|𝒢|` functions is localised
   by a slalom of width `h`, then the union of the family `𝒢` of `μ`-null sets is `μ`-null.
3. So a union of fewer than add(N) `μ`-null sets is `μ`-null, for every finite measure `μ` on
   the Cantor space (`measure_sUnion_null_of_mk_lt_add`).

### `GotoProp54`: non(UN) = non(N)

Let `μ` be a finite measure on the Cantor space that vanishes on singletons.

1. `exists_measurableSet_subset_measure_eq_half`. Every measurable set `B` has a measurable
   subset of measure `μ(B)/2`. Embed the space in the real line by a measurable injection `ψ`
   (Mathlib's `embeddingReal`) and cut `B` at the supremum of the points `t` with
   `μ(B ∩ ψ⁻¹(-∞, t]) ≤ μ(B)/2`.
2. `split μ`. Halve the space again and again. The map `split μ` sends a point to its
   sequence of choices. The preimage of an initial cylinder of length `n` is a cell of measure
   `μ(univ) 2^{-n}`.
3. `map_split`. The image measure is `μ(univ)` times the coin-tossing measure, because the
   two agree on the initial cylinders, which form a π-system that generates the σ-algebra
   (`AddUN/InitialCylinder.lean`).
4. `isUniversallyNull_of_mk_lt_non`. If `|A| < non(N)`, the image of `A` is null, and `A` lies
   in the preimage of a measurable null set, which is `μ`-null.

### `Grzegorek`

1. `universalNull` is a measurable subset of `2^ω × ω^ω`. Its section at `c` is the limsup of
   the clopen sets coded by `c(n)`, restricted to measure at most `2^{-n}`. Every section is
   null and every null set lies in a section.
2. Take `X` not null of size non(N) and a well-order of `X` of the least order type. Every
   proper initial segment has size less than non(N), so it is null. Choose a code `c_a` of a
   null set that contains the initial segment below `a`.
3. Let `Y` be the set of the pairs `(a, c_a)`. It has size non(N). Let `μ` be a finite
   measure on the pairs that vanishes on singletons. By Fubini's theorem, for almost every
   `x` the set of the pairs `(a', c)` with `x` in the section at `c` is `μ`-null. As `X` is
   not null, this holds for some `a ∈ X`. That set contains `(b, c_b)` for every `b` above
   `a`. The other pairs of `Y` form a set of size less than non(N), which is `μ`-null by
   `GotoProp54`.
4. A measurable equivalence between `2^ω × ω^ω` and `2^ω` moves `Y` into the Cantor space
   (Mathlib's `measurableEquivOfNotCountable`).

### `TheoremA`: add(UN) ≤ d

The Lean proof keeps the idea of the note and changes the construction. No step of the note
was found to be wrong. The steps of the note listed below were replaced, so they were not
checked by Lean in their written form.

| Note | Lean |
| --- | --- |
| The maps `m_h` fill the coordinates outside `ran(h)` with a second point, using the enumeration `g_h` of the complement | `overwrite h c u` writes `c(n)` on the coordinate `h(n)` and keeps `u` elsewhere |
| `h` strictly increasing with odd values, `D` closed under finite modifications | `h(k) = pair(k, g(k + k₀))`, which is injective and at least `g(k + k₀)`; the family ranges over `g ∈ D` and `k₀ ∈ ω` |
| The sets `W_h` are universally null by Goto's Claim 5.5.1 (F2) and a push-forward | Lemma 3 (`IsUniversallyNull.of_injOn`) for the map `w ↦ (n ↦ w(h(n)))`, which reads the code |
| `Y = X + Q` has full outer measure by the Kolmogorov zero–one law | The family also ranges over finite sets `s`. `exists_flipSet_mem`: a set that is not null has a point with a finite modification in a given measurable set of positive measure. This uses a zero–one law for sets invariant under finite flips (`AddUN/ZeroOne.lean`) |
| Lemma 4: density step, minimal cylinders of `[s_0] ∖ K`, the sum over lengths | `exists_levels`: no density step. The open set `Kᶜ` is cut into the layers `layer Kᶜ M k`. A point with a modification on `ran(h)` outside `K` lies in a flip of a layer by a subset of `{h(0), …, h(k-1)}`. The measure of the cover is at most `λ(Kᶜ) + λ(K)/2` |

The family has size `|D| · ℵ₀ = d`. The proof that `d` is infinite uses that add(UN) is
uncountable.

## Changes to earlier files

- `AddUN/Coding.lean`: `exists_slalom_decode` states the coding lemma for the map `decode`
  and its width. `codingLemma` is derived from it.
- `AddUN/Localisation.lean`: `exists_clopens_summable` and `exists_clopens_limsup` hold for
  every finite measure on the Cantor space. `measure_sUnion_null_of_localised` is new, and
  `exists_unlocalised_family` is derived from it.
