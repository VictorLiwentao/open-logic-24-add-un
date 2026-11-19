# Open case, round 3: summary

Status (2026-11-19). **The open case is not solved.** This folder holds one round of
attempts by AI agents (Claude). Nothing here is checked by a human or by Lean. The
coordinating AI refereed only the items marked "refereed" below.

Files:

- `ideas.md`: the starting ideas (fibre lemma, translates, the self-referential Grzegorek
  scheme GS).
- `gs-scheme.md`: attempt to realise or refute GS. Verdict: undecided.
- `plan-z.md`: attempt to prove add(UN) ≤ b and add(UN) ≤ add*(N). Verdict: both fail at
  the same step.
- `literature-and-models.md`: literature search and the consistency side.

## What was gained

1. **Cohen capture (refereed, proof re-read line by line).** If W = V[c] for a Cohen real
   c, then add(UN) = add(N) in W. Reason: the ground model reals have strong measure zero in
   W (M. A. Cardona, arXiv:2005.07912, abstract checked), so they are a universally null set
   of size c, and Theorem B applies. The same argument gives a strong measure zero set of
   size c after every finite support iteration of nontrivial ccc posets whose length has
   uncountable cofinality (`literature-and-models.md`, Proposition P), so add(UN) = add(N)
   in all such models.
2. **Effect on candidate models (not refereed in detail).** The Boolean ultrapower models of
   Cichoń's maximum, the Kellner–Shelah–Tanasie order and the submodel method are finite
   support ccc iterations or close to them, so equality should hold there. The agent read
   those constructions only in part. Shattered iterations are decided only for the ground
   models used in Brendle's paper.
3. **Inheritance (refereed for random forcing).** Random forcing keeps universally null sets
   universally null, so add(UN) does not go up in a random extension. The same is claimed
   for measured extensions.
4. **The formula add(N) = min{b, add*(N)} is confirmed** (Pawlikowski 1985, as quoted in
   arXiv:2401.15364; the original paper was not reached). Hence "add(UN) ≤ b and
   add(UN) ≤ add*(N)" is equivalent to the problem. Neither half is proved.
5. **The exact obstacle (refereed: Lemma R, Proposition 6.1, Corollary 6.2 of
   `gs-scheme.md`).** The recursion behind Theorem B can always be run, with add(N) keys,
   until the chosen points form a non-null set. It proves add(UN) ≤ add(N) if every proper
   initial segment stays universally null. If add(N) < add(UN), every run passes through an
   initial segment that is null but not universally null.
6. **A sub-question about null sets only.** Let sn be the least number of null sets whose
   union contains a non-null set of size non(N). Then add(N) ≤ sn ≤ cov(N). If sn > add(N)
   is consistent, every argument whose witness has size non(N) fails. This is undecided.
7. **A new separation (follows from item 1 and published models).** add(UN) = add(N) = b <
   non(NA) ≤ add(SN) is consistent, also with large continuum.

## What this says about the answer

A model of add(N) < add(UN) needs c ≥ ℵ_3, d ≥ ℵ_2, non(N) ≥ ℵ_2, non(N) < cof(N), and must
not be a Cohen extension of a model with the same continuum, nor a finite support ccc
iteration. No known forcing technique produces such a model. This is evidence for a ZFC
proof of equality, not a proof. No ZFC argument found so far gets below cov(M) or d without
a universally null set of size cof(N).

## Not checked

Most of the "PROVED" items in `gs-scheme.md` and `plan-z.md` were read by their author only.
Statements about cardinal values in specific models are partly from memory. Google Scholar,
MathSciNet and zbMATH were not searched.
