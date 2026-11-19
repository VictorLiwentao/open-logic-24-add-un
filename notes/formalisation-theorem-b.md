# Lean formalisation of Theorem B (hard direction)

Status (2026-11-19). The inequality add(UN) ≤ add(N) of Theorem B has a kernel-checked Lean
proof. It was written by an AI agent (Claude). No human has reviewed the Lean code or the
definitions.

## What is proved

```lean
theorem AddUN.add_universallyNull_le_add_null (A : Set (ℕ → Bool))
    (hA : IsUniversallyNull A) (hcard : #A = cof 𝒩) : add 𝒰𝒩 ≤ add 𝒩
```

`#print axioms` gives `propext`, `Classical.choice`, `Quot.sound`. `lake build` passes with no
warning. The project has no `sorry` and no `axiom`.

Also proved: `theoremB_of_gotoCor513 : GotoCor513 → TheoremB` and
`corollaries_of_cited : Grzegorek → GotoCor513 → CorollaryA ∧ CorollaryB ∧ CorollaryC`.

## What is not proved

- `TheoremB` itself is an equality. Its other half, add(N) ≤ add(UN), is Goto's
  Corollary 5.13. It is still the unproved `Prop` `GotoCor513`.
- `Grzegorek`, `GotoProp54` and `TheoremA` are still unproved `Prop`s.
- No statement in `AddUN/Statements.lean` was changed.

## What a reviewer should check

The kernel checks the proof, not the definitions. A reviewer should read these:

- `IsUniversallyNull` in `AddUN/UniversallyNull.lean`: measure zero for every finite measure
  on the product σ-algebra of `ℕ → Bool` that vanishes on singletons.
- `cantorMeasure`: the infinite product of the uniform measure on `Bool`.
- `add` and `cof` in `AddUN/IdealInvariant.lean`: infima over witnesses.
- The statement of `add_universallyNull_le_add_null` above.

## Map from the note to the Lean code

| Note | Lean |
| --- | --- |
| Independence of events on disjoint coordinates | `cantorMeasure_inter_cylinder` in `CantorMeasure.lean` |
| Compact set of positive measure off a null set | `exists_isCompact_disjoint_of_null` |
| Lemma 1, Step 1 | `exists_clopens_limsup` in `Localisation.lean` |
| Lemma 1 | `exists_unlocalised_family` |
| Lemma 2, statement | `CodingLemma` in `TheoremB.lean` |
| Lemma 2, "Width" | `second_moment` in `SecondMoment.lean`, `card_le_of_subset_bad` in `Coding.lean` |
| Lemma 2, "Invariant" | `branch_spec` |
| Lemma 2, "The point w" | the proof of `codingLemma` |
| Lemma 3 | `IsUniversallyNull.of_injOn`, `IsUniversallyNull.of_injOn_restrict` in `Transfer.lean` |
| Proof of Theorem B | `add_universallyNull_le_add_null_of_codingLemma` in `TheoremB.lean` |

## Where the Lean proof differs from the note

No step of the note was found to be wrong. The Lean proof replaces some steps by simpler
ones. The replaced steps of the note were therefore not checked by Lean in their written
form.

1. **Independence.** Lean proves only this case: an event that does not depend on the
   coordinates in a finite set `B` is independent of every cylinder on `B`. The proof uses
   the invariance of the measure under the flip of one coordinate. This case is all that the
   proof needs.
2. **Lemma 1, Step 1.** The note splits each open set into disjoint cylinders and groups
   them. Lean splits each open set into disjoint clopen sets, lists all of them in one
   sequence with a finite sum of measures, and then groups that sequence. The codes are
   clopen sets, as in the note. The measure bound is `ε_n = 2^{-n} / (h(n) + 1)`, so `h` may
   take the value 0.
3. **Lemma 2, the maps.** `decode f` is a measurable map on the whole space. Bit `i` is
   `true` if for all large `n` a marker at `(n, f(n))` with `n > i` carries a message with
   bit `i` equal to `true`. On the domain of the note's `φ_f` this agrees with `φ_f`.
   Lemma 3 is proved for total maps and for maps on a measurable domain.
4. **Lemma 2, the slalom.** The note defines `S(n)` and the tree `T^n(s)` by a joint
   recursion. Lean defines `S(n)` directly as `bad K c n`: the set of `k` such that
   `λ(K ∩ E ∩ R_{n,k}) < (ρ_n / 2) λ(K ∩ E)` for some measurable `E` that depends only on
   blocks of stages below `n` and has `λ(K ∩ E) ≥ θ_n`. This set contains the note's
   `S(n)`. The second-moment argument of the note bounds its size without change. A larger
   slalom is harmless, because the conclusion is only needed for `f` that escape it.
5. **Lemma 2, the constants.** Lean uses `θ_n = 4 α_n = 2^{2 - μ_n}` in place of the tail
   sum `2 τ_{n-1}`. The two steps of the invariant become `θ_{n+1} + α_n ≤ θ_n` and
   `θ_{n+1} ≤ (ρ_n / 2) θ_n`. The first stage `n_0` satisfies `θ_{n_0} ≤ λ(K)`. The width
   bound is `|S(n)| ≤ 4 / (ρ_n θ_n²) ≤ 2^{3 μ_n + n}`, the same `h` as in the note. The note's
   tail-sum arithmetic (E) was checked by hand only.
6. **Lemma 2, the point `w`.** The sets `Q_n` of the note are not needed. The sets
   `K ∩ branch m` are nonempty, compact and decreasing, so they have a common point `w`.
   Membership in `branch (m + 1)` gives both facts used: a marker of `w` at `(n, f(n))` is
   followed by the code, and `w` hits the code when `f(n) ∉ S(n)`.
7. **Lemma 2, Cauchy–Schwarz.** Lean uses the pointwise bound `Ξ ≤ t/2 + Ξ²/(2t)` with
   `t = 2/θ` and integrates it. This avoids square roots and gives `N ρ θ² ≤ 4`.
8. **Proof of Theorem B.** The cofinal family need not consist of `G_δ` sets. For a null set
   `G`, outer regularity gives an open `U ⊇ G` of measure at most `1/2`, and `K` is the
   complement of `U`.
