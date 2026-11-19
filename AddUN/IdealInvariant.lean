/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinal invariants of a family of sets

Let `I` be a family of subsets of a type `X`. In applications `I` is an ideal, such as the null
sets of a measure. This file defines the four standard cardinal invariants of `I`:

* `IdealInvariant.add I`: the least size of a subfamily of `I` whose union is not in `I`;
* `IdealInvariant.cov I`: the least size of a subfamily of `I` whose union is `X`;
* `IdealInvariant.non I`: the least size of a subset of `X` that is not in `I`;
* `IdealInvariant.cof I`: the least size of a subfamily of `I` that is cofinal in `(I, ⊆)`.

Each invariant is an infimum over witnesses. When there is no witness the value is `0`.
-/

@[expose] public section

universe u

open Cardinal Set

namespace IdealInvariant

variable {X : Type u} {I : Set (Set X)} {𝒜 : Set (Set X)} {A : Set X}

/-- The *additivity* `add(I)`: the least cardinality of a subfamily of `I` whose union is not
in `I`. It is `0` when there is no such subfamily. -/
noncomputable def add (I : Set (Set X)) : Cardinal.{u} :=
  ⨅ 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 ∉ I}, #𝒜.1

/-- The *covering number* `cov(I)`: the least cardinality of a subfamily of `I` whose union is
the whole space. It is `0` when there is no such subfamily. -/
noncomputable def cov (I : Set (Set X)) : Cardinal.{u} :=
  ⨅ 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 = univ}, #𝒜.1

/-- The *uniformity* `non(I)`: the least cardinality of a set that is not in `I`. It is `0` when
every set is in `I`. -/
noncomputable def non (I : Set (Set X)) : Cardinal.{u} :=
  ⨅ A : {A : Set X // A ∉ I}, #A.1

/-- The *cofinality* `cof(I)`: the least cardinality of a subfamily `𝒜` of `I` such that every
member of `I` is contained in a member of `𝒜`. -/
noncomputable def cof (I : Set (Set X)) : Cardinal.{u} :=
  ⨅ 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B}, #𝒜.1

theorem add_le (h𝒜 : 𝒜 ⊆ I) (hU : ⋃₀ 𝒜 ∉ I) : add I ≤ #𝒜 :=
  ciInf_le' (fun 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 ∉ I} ↦ #𝒜.1) ⟨𝒜, h𝒜, hU⟩

theorem cov_le (h𝒜 : 𝒜 ⊆ I) (hU : ⋃₀ 𝒜 = univ) : cov I ≤ #𝒜 :=
  ciInf_le' (fun 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 = univ} ↦ #𝒜.1) ⟨𝒜, h𝒜, hU⟩

theorem non_le (hA : A ∉ I) : non I ≤ #A :=
  ciInf_le' (fun A : {A : Set X // A ∉ I} ↦ #A.1) ⟨A, hA⟩

theorem cof_le (h𝒜 : 𝒜 ⊆ I) (hcof : ∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B) : cof I ≤ #𝒜 :=
  ciInf_le' (fun 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B} ↦ #𝒜.1)
    ⟨𝒜, h𝒜, hcof⟩

/-- A subfamily of `I` of size less than `add I` has its union in `I`. -/
theorem sUnion_mem_of_lt_add (h𝒜 : 𝒜 ⊆ I) (h : #𝒜 < add I) : ⋃₀ 𝒜 ∈ I :=
  by_contra fun hU ↦ (add_le h𝒜 hU).not_gt h

/-- A set of size less than `non I` is in `I`. -/
theorem mem_of_lt_non (h : #A < non I) : A ∈ I :=
  by_contra fun hA ↦ (non_le hA).not_gt h

/-- The uniformity is attained when some set is not in `I`. -/
theorem exists_notMem_mk_eq_non (hI : ∃ A, A ∉ I) : ∃ A, A ∉ I ∧ #A = non I := by
  obtain ⟨A, hA⟩ := hI
  have : Nonempty {A : Set X // A ∉ I} := ⟨⟨A, hA⟩⟩
  obtain ⟨⟨B, hB⟩, h⟩ := ciInf_mem fun A : {A : Set X // A ∉ I} ↦ #A.1
  exact ⟨B, hB, h⟩

/-- The cofinality is attained. -/
theorem exists_cofinal_mk_eq_cof (I : Set (Set X)) :
    ∃ 𝒜 ⊆ I, (∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B) ∧ #𝒜 = cof I := by
  have : Nonempty {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B} :=
    ⟨⟨I, Subset.rfl, fun A hA ↦ ⟨A, hA, Subset.rfl⟩⟩⟩
  obtain ⟨⟨𝒜, h𝒜, hcof⟩, h⟩ :=
    ciInf_mem fun 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B} ↦ #𝒜.1
  exact ⟨𝒜, h𝒜, hcof, h⟩

/-- If `I` is closed under countable unions and some subfamily of `I` has its union outside `I`,
then `add I` is uncountable. -/
theorem aleph0_lt_add (hσ : ∀ 𝒜 ⊆ I, 𝒜.Countable → ⋃₀ 𝒜 ∈ I) (hI : ∃ 𝒜 ⊆ I, ⋃₀ 𝒜 ∉ I) :
    ℵ₀ < add I := by
  obtain ⟨𝒜, h𝒜, hU⟩ := hI
  have : Nonempty {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 ∉ I} := ⟨⟨𝒜, h𝒜, hU⟩⟩
  obtain ⟨⟨ℬ, hℬ, hV⟩, h⟩ :=
    ciInf_mem fun 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 ∉ I} ↦ #𝒜.1
  rw [add, ← h]
  exact not_le.1 fun hle ↦ hV (hσ ℬ hℬ (le_aleph0_iff_set_countable.1 hle))

/-- If `I` contains every singleton and some set is not in `I`, then `add I ≤ non I`. -/
theorem add_le_non (hsing : ∀ x, {x} ∈ I) (hI : ∃ A, A ∉ I) : add I ≤ non I := by
  obtain ⟨A, hA, hcard⟩ := exists_notMem_mk_eq_non hI
  have hU : ⋃₀ ((fun x ↦ ({x} : Set X)) '' A) = A := by
    ext y
    simp
  rw [← hcard]
  refine (add_le ?_ (by rwa [hU])).trans mk_image_le
  rintro _ ⟨x, -, rfl⟩
  exact hsing x

/-- If the whole space is not in `I`, then `non I ≤ cof I`. -/
theorem non_le_cof (huniv : univ ∉ I) : non I ≤ cof I := by
  obtain ⟨𝒜, h𝒜, hcof, hcard⟩ := exists_cofinal_mk_eq_cof I
  have hne : ∀ B : 𝒜, ∃ x, x ∉ B.1 := fun B ↦ by
    by_contra h
    push Not at h
    exact huniv (eq_univ_of_forall h ▸ h𝒜 B.2)
  choose f hf using hne
  have hrange : range f ∉ I := fun h ↦ by
    obtain ⟨B, hB, hsub⟩ := hcof _ h
    exact hf ⟨B, hB⟩ (hsub ⟨⟨B, hB⟩, rfl⟩)
  rw [← hcard]
  exact (non_le hrange).trans mk_range_le

/-- The uniformity is monotone: a smaller family has a smaller uniformity, provided the larger
family does not contain every set. -/
theorem non_le_non {J : Set (Set X)} (hIJ : I ⊆ J) (hJ : ∃ A, A ∉ J) : non I ≤ non J := by
  obtain ⟨A, hA, hcard⟩ := exists_notMem_mk_eq_non hJ
  exact hcard ▸ non_le fun h ↦ hA (hIJ h)

end IdealInvariant
