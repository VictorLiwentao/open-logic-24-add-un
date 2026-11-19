/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.Coding

/-!
# Theorem B: the hard direction

This file states the results that are proved in Lean.

* `add_universallyNull_le_add_null`: if there is a universally null set of cardinality
  `cof 𝒩`, then `add 𝒰𝒩 ≤ add 𝒩`. This is proved with no hypothesis.
* `theoremB_of_gotoCor513`: `TheoremB` follows from `add 𝒩 ≤ add 𝒰𝒩`, which is Goto's
  Corollary 5.13. That result is cited, not proved here.
* `corollaries_of_cited`: the three corollaries follow from the two cited results.
-/

@[expose] public section

open Cardinal MeasureTheory IdealInvariant

namespace AddUN

/-- **The hard direction of Theorem B.** If there is a universally null set of cardinality
`cof 𝒩`, then `add 𝒰𝒩 ≤ add 𝒩`. -/
theorem add_universallyNull_le_add_null (A : Set (ℕ → Bool)) (hA : IsUniversallyNull A)
    (hcard : #A = cof 𝒩) : add 𝒰𝒩 ≤ add 𝒩 :=
  add_universallyNull_le_add_null_of_codingLemma codingLemma A hA hcard

/-- Theorem B follows from `add 𝒩 ≤ add 𝒰𝒩` (Goto, Corollary 5.13). -/
theorem theoremB_of_gotoCor513 (hle : GotoCor513) : TheoremB :=
  theoremB_of_codingLemma codingLemma hle

/-- Corollaries (a), (b) and (c) follow from Grzegorek's theorem and `add 𝒩 ≤ add 𝒰𝒩`. -/
theorem corollaries_of_cited (hG : Grzegorek) (hle : GotoCor513) :
    CorollaryA ∧ CorollaryB ∧ CorollaryC :=
  corollaries_of_theoremB (theoremB_of_gotoCor513 hle) hG hle

end AddUN
