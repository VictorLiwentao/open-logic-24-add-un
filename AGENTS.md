# Working rules

These rules apply to people and to AI agents.

## Start here

1. Read `README.md`, then `notes/partial-results.md` in full.
2. Read Goto's paper, [arXiv:2607.12936](https://arxiv.org/abs/2607.12936), at least
   Sections 5 and 6.
3. Skim `agent-logs/` before you try an idea. Several approaches failed and the logs say why.

## Honesty

- State the status of every claim: formal proof, human-checked proof, AI-checked proof, or
  sketch. Do not upgrade a status without the evidence.
- The problem is open. Do not write that it is solved unless a full proof exists and has been
  checked by a set theorist or by Lean.
- If you find an error or a gap in a proof, report it in an issue and mark the claim in the
  note. Do not quietly weaken a statement to make it true.
- Read a source before you cite it. Do not write a title, author or theorem number from
  memory.
- Say what you did not check.

## Mathematics

- Put new results and failed attempts in `notes/`. A failed attempt with a clear obstacle is
  useful.
- Keep the notation of the note: `N`, `UN`, `add`, `cov`, `non`, `cof`, `b`, `d`.
- Separate what is proved in ZFC from what holds in a particular model.

## Lean

- No `sorry`, no `axiom`, no `native_decide`.
- State an unproved claim as a `def` of type `Prop` and pass it as a hypothesis. See
  `AddUN/Statements.lean`.
- Do not change a `Prop` in `AddUN/Statements.lean` to make it easier to prove. If a statement
  is wrong, open an issue and explain why.
- Run `lake build` before you commit. Check a finished theorem with `#print axioms`.
- Search Mathlib before you add a definition.

## Pull requests

Keep each pull request to one topic. Say what changed, why, and how you checked it. Disclose
AI use.
