# Is add(N) < add(UN) consistent?

Working notes and a Lean 4 project on Problem 24 of
[Open Problems in Mathematical Logic](https://www.openlogicproblems.com/problems/24).

**The problem is open.** This repository holds partial results. People and AI agents are
welcome to check them, break them, formalise them, or attack the remaining case.

## The problem

Let `N` be the ideal of null subsets of the Cantor space `2^ω` for the product measure. Let
`UN` be the ideal of universally null sets: sets of outer measure zero for every atomless
finite Borel measure on `2^ω`. For an ideal `I`, `add(I)` is the least size of a subfamily of
`I` whose union is not in `I`.

> **Question 6.3** (T. Goto, *Forcing and cardinal invariants of universally null sets*,
> [arXiv:2607.12936](https://arxiv.org/abs/2607.12936)). Is it consistent that
> add(N) < add(UN), or does ZFC prove add(N) = add(UN)?

Known from the paper: add(N) ≤ add(UN) ≤ non(UN) = non(N).

## Read this first: how much to trust the results

- All results here were produced by AI agents (Claude): two rounds on 2026-11-16 and a third
  on 2026-11-19.
- Each proof was attacked by independent AI referees. Theorem B was found twice by separate
  agents and passed five referee reports.
- **No human expert has checked any proof.**
- **Theorems A and B, the corollaries and the three cited results have Lean proofs**
  (2026-11-19), with no hypothesis left. Lean checks the proofs. It does not check that the
  Lean definitions say what the note means, and no human has reviewed them. See
  [notes/formalisation-theorem-b.md](notes/formalisation-theorem-b.md) and
  [notes/formalisation-theorem-a-and-cited.md](notes/formalisation-theorem-a-and-cited.md).
- The Lean proofs of the cited results (Goto's Corollary 5.13 and Proposition 5.4,
  Grzegorek's theorem) do not follow the sources. The Lean proof of Theorem A changes the
  construction of the note.
- The literature search found no earlier statement of Theorem A or B. It did not cover Google
  Scholar, MathSciNet, or arXiv full text, so novelty is not established.

Treat every claim without a Lean proof as a conjecture with a detailed proof sketch until it
is checked. The question itself is open.

## Claimed results

| Claim | Statement | Status |
| --- | --- | --- |
| Theorem A | add(UN) ≤ d | Lean proof |
| Theorem B | If there is a universally null set of size cof(N), then add(UN) = add(N) | Lean proof |
| Corollary (a) | non(N) = cof(N) implies add(UN) = add(N) | Lean proof |
| Corollary (b) | c ≤ ℵ₂ implies add(UN) = add(N) | Lean proof |
| Corollary (c) | add(N) < add(UN) implies c ≥ ℵ₃, non(N) < cof(N), and every universally null set has size < cof(N) | Lean proof |

Cited results, also proved in Lean:

| Result | Statement | Status |
| --- | --- | --- |
| Goto, Corollary 5.13 | add(N) ≤ add(UN) | Lean proof, by a different route |
| Goto, Proposition 5.4 | non(UN) = non(N) | Lean proof, by a different route |
| Grzegorek's theorem | There is a universally null set of size non(N) | Lean proof, by a different route |

"Lean proof" means: a theorem of the stated type, with no hypothesis, whose axioms are
`propext`, `Classical.choice` and `Quot.sound`. The note's Corollary (c) has two more parts
(b < cof(N) and add(UN) ≤ min(d, cf(non(N)))). They are not in the Lean statement.

By Theorem B and the cited results, the Mathias, Laver, Miller and Sacks models all satisfy
add(UN) = add(N), and no model with c ≤ ℵ₂ can separate the two cardinals.

Full proofs are in [notes/partial-results.md](notes/partial-results.md).

## What is still open

The case **non(N) < cof(N), c ≥ ℵ₃, and every universally null set has size < cof(N)**.

- Undecided in ZFC: add(UN) ≤ b, add(UN) ≤ cov(M), add(UN) ≤ non(M).
- The method of Theorem A cannot be sharpened below d, and the "leaf" devices that were tried
  need at least cov(M) maps. See "What is still open" in the note.
- Candidate models that Theorem B does not rule out: Cichoń's maximum via Boolean
  ultrapowers ([arXiv:1708.03691](https://arxiv.org/abs/1708.03691)), the alternative order of
  Kellner, Shelah and Tanasie ([arXiv:1712.00778](https://arxiv.org/abs/1712.00778)), and
  Brendle's shattered iterations ([arXiv:2302.05069](https://arxiv.org/abs/2302.05069)).

A third round (2026-11-19) attacked this case and did not solve it. Its notes are in
[notes/open-case/](notes/open-case/README.md). They have no Lean proof and no human review.
The main claim is that add(UN) = add(N) holds after adding a Cohen real, and in every finite
support iteration of nontrivial ccc posets of uncountable cofinality. If the claim is right,
the first two candidate models above probably satisfy equality. That step is only partly
checked.

## Repository layout

| Path | Content |
| --- | --- |
| `notes/partial-results.md` | The current note: statements, full informal proofs, literature, open directions |
| `notes/formalisation-theorem-b.md` | What the Lean proof of Theorem B covers and where it differs from the note |
| `notes/formalisation-theorem-a-and-cited.md` | The Lean proofs of Theorem A and the cited results, and where they differ from the note |
| `notes/open-case/` | Round 3: attempts on the open case, with a summary in its `README.md`. Not checked by Lean or by a human |
| `notes/superseded-v1.md` | An earlier, weaker note. Kept for the record |
| `agent-logs/round1.json`, `round2.json` | Raw agent output: literature reports, proof attempts (including failed ones), referee reports |
| `AddUN/IdealInvariant.lean` | `add`, `cov`, `non`, `cof` of a family of sets, with basic lemmas |
| `AddUN/UniversallyNull.lean` | Universally null sets, null sets of a measure, the coin-tossing measure |
| `AddUN/Statements.lean` | The question, cited results and claims as `Prop`s; proofs of the corollaries |
| `AddUN/CantorMeasure.lean` | Flip invariance, independence from cylinders, compact sets of positive measure |
| `AddUN/Transfer.lean` | Lemma 3: transfer of universal nullness along an injective Borel map |
| `AddUN/Localisation.lean` | Lemma 1: a family of at most add(N) functions that no slalom localises |
| `AddUN/TheoremB.lean` | The statement `CodingLemma` and Theorem B from it |
| `AddUN/SecondMoment.lean` | The second-moment bound used for the width of the slalom |
| `AddUN/Coding.lean` | Lemma 2: the proof of `CodingLemma` |
| `AddUN/Additivity.lean` | add(N) ≤ add(UN) |
| `AddUN/InitialCylinder.lean` | The initial cylinders generate the σ-algebra of the Cantor space |
| `AddUN/Uniformity.lean` | Halving of atomless measures; non(UN) = non(N) |
| `AddUN/Grzegorek.lean` | Grzegorek's theorem |
| `AddUN/ZeroOne.lean` | A zero–one law for sets invariant under finite flips |
| `AddUN/TheoremA.lean` | Theorem A |
| `AddUN/Main.lean` | The final theorems, with no hypothesis |

The agent logs mention local file paths such as `scratch/...` and `local/...`. Those files are
not in this repository.

## Lean project

Lean `v4.33.1` with Mathlib `v4.33.1`.

```bash
lake exe cache get
```

```bash
lake build
```

The project contains no `sorry` and no `axiom`. Each claim is a `def` of type `Prop` in
`AddUN/Statements.lean`, for example `AddUN.TheoremA`. A claim counts as proved when the
project has a theorem of that type and `#print axioms` shows only `propext`,
`Classical.choice` and `Quot.sound`.

Proved so far: every `Prop` of `AddUN/Statements.lean` except `Question63`.

- `gotoCor513 : GotoCor513`, `gotoProp54 : GotoProp54`, `grzegorek : Grzegorek`.
- `theoremA : TheoremA`, `theoremB : TheoremB`.
- `corollaryA : CorollaryA`, `corollaryB : CorollaryB`, `corollaryC : CorollaryC`.
- `add_null_eq_add_universallyNull_of_continuum_le_aleph_two : 𝔠 ≤ ℵ₂ → add 𝒩 = add 𝒰𝒩`.
- `add_universallyNull_le_min : add 𝒰𝒩 ≤ min 𝔡 (non 𝒩)`.
- Lemmas 1, 2 and 3 of the note: `exists_unlocalised_family`, `codingLemma`,
  `IsUniversallyNull.of_injOn`.

Not proved: `Question63`. It is the open question.

## Good next tasks

1. **Review the Lean definitions and the final statements.** Lean checks the proofs, not
   that `IsUniversallyNull`, `cantorMeasure`, `add`, `non`, `cof` and `dominatingNumber` say
   what the note means. The lists are in the two formalisation notes.
2. **Search the literature** in the places not yet covered.
3. **Attack the open case**: decide add(UN) ≤ b, or analyse one of the candidate models.
   Read [notes/open-case/README.md](notes/open-case/README.md) first. Checking its Cohen
   real argument is a good small task.
4. **Formalise the rest of Corollary (c)**: Recław's theorem (a universally null set of size
   b) and add(UN) ≤ cf(non(N)).

See [AGENTS.md](AGENTS.md) for the working rules.

## Licence

Apache 2.0. See [LICENSE](LICENSE).
