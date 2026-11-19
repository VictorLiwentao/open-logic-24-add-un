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

- All results here were produced by AI agents (Claude) in two rounds on 2026-11-16.
- Each proof was attacked by independent AI referees. Theorem B was found twice by separate
  agents and passed five referee reports.
- **No human expert has checked any proof.**
- **The new half of Theorem B has a Lean proof** (2026-11-19): a universally null set of size
  cof(N) gives add(UN) ≤ add(N). The other half, add(N) ≤ add(UN), is Goto's Corollary 5.13.
  It is cited, not formalised. No human has reviewed the Lean definitions. See
  [notes/formalisation-theorem-b.md](notes/formalisation-theorem-b.md).
- **Theorem A has no formal proof.**
- The literature search found no earlier statement of Theorem A or B. It did not cover Google
  Scholar, MathSciNet, or arXiv full text, so novelty is not established.

Treat every claim without a Lean proof as a conjecture with a detailed proof sketch until it
is checked.

## Claimed results

| Claim | Statement | Status |
| --- | --- | --- |
| Theorem A | add(UN) ≤ d | Informal proof, AI-refereed |
| Theorem B, hard direction | If there is a universally null set of size cof(N), then add(UN) ≤ add(N) | Lean proof, no hypothesis |
| Theorem B | If there is a universally null set of size cof(N), then add(UN) = add(N) | Lean proof from add(N) ≤ add(UN) |
| Corollary (a) | non(N) = cof(N) implies add(UN) = add(N) | Lean proof from Grzegorek's theorem and add(N) ≤ add(UN) |
| Corollary (b) | c ≤ ℵ₂ implies add(UN) = add(N) | Lean proof from the same two results |
| Corollary (c) | add(N) < add(UN) implies c ≥ ℵ₃, non(N) < cof(N), and every universally null set has size < cof(N) | Lean proof from the same two results |

The two cited results, Grzegorek's theorem and add(N) ≤ add(UN) (Goto, Corollary 5.13), are
not formalised.

By Theorem B and the cited results, the Mathias, Laver, Miller and Sacks models all satisfy
add(UN) = add(N), and no model with c ≤ ℵ₂ can separate the two cardinals.

Full proofs are in [notes/partial-results.md](notes/partial-results.md).

## What is still open

The case **non(N) < cof(N), c ≥ ℵ₃, and every universally null set has size < cof(N)**.

- Undecided in ZFC: add(UN) ≤ b, add(UN) ≤ cov(M), add(UN) ≤ non(M).
- The method of Theorem A cannot be sharpened below d, and the "leaf" devices that were tried
  need at least cov(M) maps. See "What is still open" in the note.
- Candidate models that the constraints do not yet rule out: Cichoń's maximum via Boolean
  ultrapowers ([arXiv:1708.03691](https://arxiv.org/abs/1708.03691)), the alternative order of
  Kellner, Shelah and Tanasie ([arXiv:1712.00778](https://arxiv.org/abs/1712.00778)), and
  Brendle's shattered iterations ([arXiv:2302.05069](https://arxiv.org/abs/2302.05069)).

## Repository layout

| Path | Content |
| --- | --- |
| `notes/partial-results.md` | The current note: statements, full informal proofs, literature, open directions |
| `notes/formalisation-theorem-b.md` | What the Lean proof of Theorem B covers and where it differs from the note |
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
| `AddUN/Main.lean` | The final theorems |

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

The project contains no `sorry` and no `axiom`. Each unproved claim is a `def` of type `Prop`
in `AddUN/Statements.lean`, for example `AddUN.TheoremA`. A claim counts as proved when the
project has a theorem of that type and `#print axioms` shows only `propext`,
`Classical.choice` and `Quot.sound`.

Proved so far:

- Basic facts: the coin-tossing measure has no atoms, `𝒰𝒩 ⊆ 𝒩`, both additivities are
  uncountable, `add ≤ non ≤ cof` under the usual conditions, `cof 𝒩 ≤ 𝔠`.
- Lemmas 1, 2 and 3 of the note: `exists_unlocalised_family`, `codingLemma`,
  `IsUniversallyNull.of_injOn`.
- The hard direction of Theorem B, with no hypothesis:
  `add_universallyNull_le_add_null (A) (hA : IsUniversallyNull A) (hcard : #A = cof 𝒩) :
  add 𝒰𝒩 ≤ add 𝒩`.
- `theoremB_of_gotoCor513 : GotoCor513 → TheoremB` and
  `corollaries_of_cited : Grzegorek → GotoCor513 → CorollaryA ∧ CorollaryB ∧ CorollaryC`.

Not proved: `GotoCor513`, `GotoProp54`, `Grzegorek`, `TheoremA`. `TheoremB` has no theorem of
its own type, because it needs `GotoCor513`.

## Good next tasks

1. **Review the Lean definitions and the final statement.** Lean checks the proof of
   Theorem B, not that `IsUniversallyNull`, `cantorMeasure`, `add` and `cof` say what the
   note means. The list is in `notes/formalisation-theorem-b.md`.
2. **Formalise the cited results**: add(N) ≤ add(UN) (this would prove `TheoremB` outright)
   and Grzegorek's theorem.
3. **Formalise Theorem A.**
4. **Search the literature** in the places not yet covered.
5. **Attack the open case**: decide add(UN) ≤ b, or analyse one of the candidate models.

See [AGENTS.md](AGENTS.md) for the working rules.

## Licence

Apache 2.0. See [LICENSE](LICENSE).
