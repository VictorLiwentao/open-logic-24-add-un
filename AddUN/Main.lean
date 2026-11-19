/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.Additivity
public import AddUN.TheoremA

/-!
# The results that are proved

Every statement of `AddUN/Statements.lean` except `Question63` is proved here or in the files
that this file imports. No hypothesis is left.

* `gotoCor513 : GotoCor513`, in `AddUN/Additivity.lean`.
* `gotoProp54 : GotoProp54`, in `AddUN/Uniformity.lean`.
* `grzegorek : Grzegorek`, in `AddUN/Grzegorek.lean`.
* `theoremA : TheoremA`, in `AddUN/TheoremA.lean`.
* `theoremB : TheoremB`, `corollaryA`, `corollaryB`, `corollaryC`, in this file.
* `add_null_eq_add_universallyNull_of_continuum_le_aleph_two`: `add 𝒩 = add 𝒰𝒩` if `𝔠 ≤ ℵ₂`.
* `add_universallyNull_le_min`: `add 𝒰𝒩 ≤ min 𝔡 (non 𝒩)`.

`Question63` is open. It is not proved.
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

/-- **Theorem B.** If there is a universally null set of cardinality `cof 𝒩`, then
`add 𝒰𝒩 = add 𝒩`. -/
theorem theoremB : TheoremB := theoremB_of_gotoCor513 gotoCor513

/-- **Corollary (a).** If `non 𝒩 = cof 𝒩`, then `add 𝒰𝒩 = add 𝒩`. -/
theorem corollaryA : CorollaryA := (corollaries_of_cited grzegorek gotoCor513).1

/-- **Corollary (b).** If `𝔠 ≤ ℵ₂`, then `add 𝒰𝒩 = add 𝒩`. -/
theorem corollaryB : CorollaryB := (corollaries_of_cited grzegorek gotoCor513).2.1

/-- **Corollary (c).** If `add 𝒩 < add 𝒰𝒩`, then `ℵ₃ ≤ 𝔠`, `non 𝒩 < cof 𝒩`, and every
universally null set has cardinality less than `cof 𝒩`. -/
theorem corollaryC : CorollaryC := (corollaries_of_cited grzegorek gotoCor513).2.2

/-- If `𝔠 ≤ ℵ₂`, then `add 𝒩 = add 𝒰𝒩`: the open question `Question63` has a positive answer
in every model with `𝔠 ≤ ℵ₂`. -/
theorem add_null_eq_add_universallyNull_of_continuum_le_aleph_two
    (h : (𝔠 : Cardinal.{0}) ≤ ℵ_ 2) : add 𝒩 = add 𝒰𝒩 :=
  question63_of_continuum_le_aleph_two theoremB grzegorek gotoCor513 h

/-- `add 𝒩 ≤ add 𝒰𝒩 ≤ min 𝔡 (non 𝒩)`. -/
theorem add_universallyNull_le_min : add 𝒰𝒩 ≤ min dominatingNumber (non 𝒩) :=
  le_min theoremA add_universallyNull_le_non_null

end AddUN
