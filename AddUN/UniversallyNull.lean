/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.IdealInvariant
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure

/-!
# Universally null sets

A subset of a measurable space is *universally null* if every finite measure that gives measure
zero to each singleton gives it measure zero. For a set that is not measurable, `μ A` is the
outer measure of `A`.

This file also defines the family of null sets of a measure and the coin-tossing measure on the
Cantor space `ℕ → Bool`. It proves basic bounds on the cardinal invariants of these families.
-/

@[expose] public section

open Set Filter Topology Cardinal IdealInvariant
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {A B : Set X}

/-- The family of null sets of a measure. -/
def Measure.nullSets (μ : Measure X) : Set (Set X) := {A | μ A = 0}

@[simp]
lemma Measure.mem_nullSets {μ : Measure X} : A ∈ μ.nullSets ↔ μ A = 0 := Iff.rfl

/-- A set is *universally null* if it has measure zero for every finite measure that vanishes on
singletons. On a standard Borel space these are the atomless finite Borel measures. -/
def IsUniversallyNull (A : Set X) : Prop :=
  ∀ (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ], μ A = 0

variable (X) in
/-- The family of universally null subsets of `X`. -/
def universallyNullSets : Set (Set X) := {A | IsUniversallyNull A}

@[simp]
lemma mem_universallyNullSets : A ∈ universallyNullSets X ↔ IsUniversallyNull A := Iff.rfl

lemma IsUniversallyNull.mono (hB : IsUniversallyNull B) (h : A ⊆ B) : IsUniversallyNull A :=
  fun μ _ _ ↦ measure_mono_null h (hB μ)

lemma _root_.Set.Countable.isUniversallyNull (hA : A.Countable) : IsUniversallyNull A :=
  fun μ _ _ ↦ hA.measure_zero μ

/-- A countable union of universally null sets is universally null. -/
lemma isUniversallyNull_sUnion {𝒜 : Set (Set X)} (h𝒜 : 𝒜.Countable)
    (h : ∀ A ∈ 𝒜, IsUniversallyNull A) : IsUniversallyNull (⋃₀ 𝒜) :=
  fun μ _ _ ↦ (measure_sUnion_null_iff h𝒜).2 fun A hA ↦ h A hA μ

/-- A universally null set is null for every finite measure that vanishes on singletons. -/
lemma universallyNullSets_subset_nullSets (μ : Measure X) [IsFiniteMeasure μ]
    [NullSingletonClass μ] : universallyNullSets X ⊆ μ.nullSets :=
  fun _ h ↦ h μ

/-- The coin-tossing measure on the Cantor space `ℕ → Bool`: the product of the uniform
measures on `Bool`. -/
noncomputable def cantorMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ ↦ (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure cantorMeasure := by
  unfold cantorMeasure
  infer_instance

instance : NullSingletonClass cantorMeasure where
  measure_singleton x := by
    have hx : cantorMeasure {x} = ∏' _ : ℕ, (2⁻¹ : ℝ≥0∞) := by
      simp [cantorMeasure, PMF.uniformOfFintype_apply]
    have hle (n : ℕ) : cantorMeasure {x} ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
      rw [hx, ENNReal.tprod_eq_iInf_prod (by simp)]
      exact (iInf_le _ (Finset.range n)).trans (by simp)
    exact le_antisymm (ge_of_tendsto'
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simp)) hle) zero_le

/-- The Cantor space is not universally null. -/
lemma not_isUniversallyNull_univ_cantor : ¬ IsUniversallyNull (Set.univ : Set (ℕ → Bool)) :=
  fun h ↦ by simpa using h cantorMeasure

/-! ### Cardinal invariants -/

/-- The additivity of the null sets of a nonzero measure that vanishes on singletons is
uncountable. -/
theorem aleph0_lt_add_nullSets (μ : Measure X) [NullSingletonClass μ] [NeZero μ] :
    ℵ₀ < add μ.nullSets := by
  refine aleph0_lt_add (fun 𝒜 h𝒜 hc ↦ (measure_sUnion_null_iff hc).2 fun A hA ↦ h𝒜 hA)
    ⟨range fun x ↦ ({x} : Set X), ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact measure_singleton x
  · have h : ⋃₀ (range fun x ↦ ({x} : Set X)) = Set.univ := by
      ext
      simp
    simpa [h] using NeZero.ne μ

/-- The additivity of the universally null sets is uncountable when the whole space is not
universally null. -/
theorem aleph0_lt_add_universallyNullSets (h : ¬ IsUniversallyNull (Set.univ : Set X)) :
    ℵ₀ < add (universallyNullSets X) := by
  refine aleph0_lt_add (fun 𝒜 h𝒜 hc ↦ isUniversallyNull_sUnion hc fun A hA ↦ h𝒜 hA)
    ⟨range fun x ↦ ({x} : Set X), ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (countable_singleton x).isUniversallyNull
  · have hU : ⋃₀ (range fun x ↦ ({x} : Set X)) = Set.univ := by
      ext
      simp
    simpa [hU] using h

/-- In a countably generated measurable space the null sets of a measure have a cofinal
subfamily of size at most the continuum: the measurable null sets. -/
theorem cof_nullSets_le_continuum [MeasurableSpace.CountablyGenerated X] (μ : Measure X) :
    cof μ.nullSets ≤ 𝔠 := by
  have hsub : {B | MeasurableSet B ∧ μ B = 0} ⊆ μ.nullSets := fun B hB ↦ hB.2
  have hcof : ∀ A ∈ μ.nullSets, ∃ B ∈ {B | MeasurableSet B ∧ μ B = 0}, A ⊆ B := fun A hA ↦
    ⟨toMeasurable μ A, ⟨measurableSet_toMeasurable μ A, (measure_toMeasurable A).trans hA⟩,
      subset_toMeasurable μ A⟩
  refine (cof_le hsub hcof).trans ((mk_le_mk_of_subset fun B hB ↦ hB.1).trans ?_)
  obtain ⟨b, hbc, rfl⟩ := MeasurableSpace.CountablyGenerated.isCountablyGenerated (α := X)
  exact MeasurableSpace.cardinal_measurableSet_le_continuum
    ((le_aleph0_iff_set_countable.2 hbc).trans aleph0_le_continuum)

end MeasureTheory
