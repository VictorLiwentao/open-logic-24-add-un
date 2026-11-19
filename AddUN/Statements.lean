/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.UniversallyNull

/-!
# Goto's Question 6.3: statements

Source: T. Goto, *Forcing and cardinal invariants of universally null sets*,
[arXiv:2607.12936](https://arxiv.org/abs/2607.12936), Question 6.3. Also Problem 24 of
[Open Problems in Mathematical Logic](https://www.openlogicproblems.com/problems/24).

Let `𝒩` be the ideal of null sets of the coin-tossing measure on the Cantor space `ℕ → Bool`
and `𝒰𝒩` the ideal of universally null sets. The question asks whether `add 𝒩 < add 𝒰𝒩` is
consistent, or whether ZFC proves `add 𝒩 = add 𝒰𝒩`.

Every unproved claim in this file is a `def` of type `Prop`. Nothing here uses `sorry` or an
`axiom`. A claim is proved when the project contains a theorem of that type whose axioms are
only `propext`, `Classical.choice` and `Quot.sound`.

* `Question63`: the open question. Lean cannot state consistency over ZFC, so this is the
  statement of equality. A ZFC proof of equality proves it.
* `GotoCor513`, `GotoProp54`, `Grzegorek`: results cited from the literature, not proved here.
* `TheoremA`, `TheoremB`, `CorollaryA`, `CorollaryB`, `CorollaryC`: claims of
  `notes/partial-results.md`. Their informal proofs have not been checked by a human.

The theorems at the end are proved. They show that the corollaries follow from `TheoremB` and
the cited results.
-/

@[expose] public section

open Cardinal MeasureTheory IdealInvariant Filter

namespace AddUN

/-- The ideal `𝒩` of null sets of the coin-tossing measure on the Cantor space. -/
scoped notation "𝒩" => Measure.nullSets cantorMeasure

/-- The ideal `𝒰𝒩` of universally null subsets of the Cantor space. -/
scoped notation "𝒰𝒩" => universallyNullSets (ℕ → Bool)

/-- The *dominating number* `𝔡`: the least size of a family `D` of functions `ℕ → ℕ` such that
every function is eventually bounded by a member of `D`. -/
noncomputable def dominatingNumber : Cardinal.{0} :=
  ⨅ D : {D : Set (ℕ → ℕ) // ∀ f, ∃ g ∈ D, f ≤ᶠ[atTop] g}, #D.1

/-! ### The open question -/

/-- **Question 6.3 (Goto).** Does `add 𝒩 = add 𝒰𝒩` hold? Open. -/
def Question63 : Prop := add 𝒩 = add 𝒰𝒩

/-! ### Cited results (not proved here) -/

/-- **Goto, Corollary 5.13.** `add 𝒩 ≤ add 𝒰𝒩`. -/
def GotoCor513 : Prop := add 𝒩 ≤ add 𝒰𝒩

/-- **Goto, Proposition 5.4.** `non 𝒰𝒩 = non 𝒩`. -/
def GotoProp54 : Prop := non 𝒰𝒩 = non 𝒩

/-- **Grzegorek's theorem.** There is a universally null set of cardinality `non 𝒩`. -/
def Grzegorek : Prop := ∃ A : Set (ℕ → Bool), IsUniversallyNull A ∧ #A = non 𝒩

/-! ### Claims of `notes/partial-results.md` (informal proofs only) -/

/-- **Theorem A.** `add 𝒰𝒩 ≤ 𝔡`. -/
def TheoremA : Prop := add 𝒰𝒩 ≤ dominatingNumber

/-- **Theorem B.** If there is a universally null set of cardinality `cof 𝒩`, then
`add 𝒰𝒩 = add 𝒩`. -/
def TheoremB : Prop :=
  ∀ A : Set (ℕ → Bool), IsUniversallyNull A → #A = cof 𝒩 → add 𝒰𝒩 = add 𝒩

/-- **Corollary (a).** If `non 𝒩 = cof 𝒩`, then `add 𝒰𝒩 = add 𝒩`. -/
def CorollaryA : Prop := non 𝒩 = cof 𝒩 → add 𝒰𝒩 = add 𝒩

/-- **Corollary (b).** If `𝔠 ≤ ℵ₂`, then `add 𝒰𝒩 = add 𝒩`. -/
def CorollaryB : Prop := (𝔠 : Cardinal.{0}) ≤ ℵ_ 2 → add 𝒰𝒩 = add 𝒩

/-- **Corollary (c).** If `add 𝒩 < add 𝒰𝒩`, then `ℵ₃ ≤ 𝔠`, `non 𝒩 < cof 𝒩`, and every
universally null set has cardinality less than `cof 𝒩`. -/
def CorollaryC : Prop :=
  add 𝒩 < add 𝒰𝒩 →
    (ℵ_ 3 : Cardinal.{0}) ≤ 𝔠 ∧ non 𝒩 < cof 𝒩 ∧
      ∀ A : Set (ℕ → Bool), IsUniversallyNull A → #A < cof 𝒩

/-! ### Proved facts -/

/-- Every universally null set is null. -/
theorem universallyNull_subset_null : 𝒰𝒩 ⊆ 𝒩 :=
  universallyNullSets_subset_nullSets cantorMeasure

/-- The Cantor space is not null. -/
theorem univ_notMem_null : Set.univ ∉ 𝒩 := by
  simp

/-- `add 𝒩` is uncountable. -/
theorem aleph0_lt_add_null : ℵ₀ < add 𝒩 :=
  aleph0_lt_add_nullSets cantorMeasure

/-- `add 𝒰𝒩` is uncountable. -/
theorem aleph0_lt_add_universallyNull : ℵ₀ < add 𝒰𝒩 :=
  aleph0_lt_add_universallyNullSets not_isUniversallyNull_univ_cantor

/-- `add 𝒰𝒩 ≤ non 𝒰𝒩`. -/
theorem add_universallyNull_le_non_universallyNull : add 𝒰𝒩 ≤ non 𝒰𝒩 :=
  add_le_non (fun x ↦ (Set.countable_singleton x).isUniversallyNull)
    ⟨Set.univ, not_isUniversallyNull_univ_cantor⟩

/-- The easy half of `GotoProp54`: `non 𝒰𝒩 ≤ non 𝒩`. -/
theorem non_universallyNull_le_non_null : non 𝒰𝒩 ≤ non 𝒩 :=
  non_le_non universallyNull_subset_null ⟨Set.univ, univ_notMem_null⟩

/-- `add 𝒰𝒩 ≤ non 𝒩`. -/
theorem add_universallyNull_le_non_null : add 𝒰𝒩 ≤ non 𝒩 :=
  add_universallyNull_le_non_universallyNull.trans non_universallyNull_le_non_null

/-- Corollary (a) follows from Theorem B and Grzegorek's theorem. -/
theorem corollaryA_of_theoremB (hB : TheoremB) (hG : Grzegorek) : CorollaryA := by
  intro h
  obtain ⟨A, hA, hcard⟩ := hG
  exact hB A hA (hcard.trans h)

/-- Corollary (b) follows from Corollary (a) and `add 𝒩 ≤ add 𝒰𝒩`. -/
theorem corollaryB_of_corollaryA (ha : CorollaryA) (hle : GotoCor513) : CorollaryB := by
  intro h
  by_cases hnc : non 𝒩 = cof 𝒩
  · exact ha hnc
  have h1 : non 𝒩 < ℵ_ 2 := ((non_le_cof univ_notMem_null).lt_of_ne hnc).trans_le
    ((cof_nullSets_le_continuum cantorMeasure).trans h)
  have h2 : non 𝒩 ≤ ℵ₁ := by
    rwa [← one_add_one_eq_two, ← succ_aleph, Order.lt_succ_iff] at h1
  have h4 : ℵ₁ ≤ add 𝒩 := aleph_one_le_iff.2 aleph0_lt_add_null
  exact le_antisymm (add_universallyNull_le_non_null.trans (h2.trans h4)) hle

/-- Corollary (c) follows from Theorem B and Corollaries (a) and (b). -/
theorem corollaryC_of_theoremB (hB : TheoremB) (ha : CorollaryA) (hb : CorollaryB) :
    CorollaryC := by
  intro h
  refine ⟨?_, ?_, fun A hA ↦ ?_⟩
  · rw [show (3 : Ordinal) = 2 + 1 by norm_num, ← succ_aleph, Order.succ_le_iff]
    exact not_le.1 fun hc ↦ h.ne' (hb hc)
  · exact (non_le_cof univ_notMem_null).lt_of_ne fun hnc ↦ h.ne' (ha hnc)
  · by_contra hc
    obtain ⟨B, hBA, hBcard⟩ := le_mk_iff_exists_subset.1 (not_lt.1 hc)
    exact h.ne' (hB B (hA.mono hBA) hBcard)

/-- All three corollaries follow from Theorem B and the two cited results. -/
theorem corollaries_of_theoremB (hB : TheoremB) (hG : Grzegorek) (hle : GotoCor513) :
    CorollaryA ∧ CorollaryB ∧ CorollaryC :=
  have ha := corollaryA_of_theoremB hB hG
  have hb := corollaryB_of_corollaryA ha hle
  ⟨ha, hb, corollaryC_of_theoremB hB ha hb⟩

/-- Under Theorem B and the two cited results, the open question has a positive answer whenever
`𝔠 ≤ ℵ₂`. -/
theorem question63_of_continuum_le_aleph_two (hB : TheoremB) (hG : Grzegorek) (hle : GotoCor513)
    (h : (𝔠 : Cardinal.{0}) ≤ ℵ_ 2) : Question63 :=
  ((corollaries_of_theoremB hB hG hle).2.1 h).symm

end AddUN
