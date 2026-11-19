/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.UniversallyNull

/-!
# Transfer of universal nullness

Lemma 3 of `notes/partial-results.md`: a set that a Borel map sends injectively into a
universally null set is universally null.

* `IsUniversallyNull.of_injOn`: the map is measurable on the whole space.
* `IsUniversallyNull.of_injOn_restrict`: the map is measurable on a measurable set `Δ` that
  contains the set.
-/

@[expose] public section

open Set

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- **Lemma 3.** Let `φ` be measurable, injective on `A`, and map `A` into a universally null
set `P`. Then `A` is universally null. -/
theorem IsUniversallyNull.of_injOn {P : Set Y} (hP : IsUniversallyNull P) {φ : X → Y}
    (hφ : Measurable φ) {A : Set X} (hinj : InjOn φ A) (himg : φ '' A ⊆ P) :
    IsUniversallyNull A := by
  intro μ _ _
  -- The atoms of the image measure form a countable set.
  have hAt : {c : Y | 0 < μ.map φ {c}}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ.map φ)
      (As := fun c : Y ↦ ({c} : Set Y)) (fun c ↦ measurableSet_singleton c)
      (fun a b hab ↦ by simpa [Function.onFun] using hab)
  set At : Set Y := {c : Y | 0 < μ.map φ {c}} with hAtdef
  have hAtm : MeasurableSet At := hAt.measurableSet
  -- Removing the atoms gives a finite measure that vanishes on singletons.
  have hsing : NullSingletonClass ((μ.map φ).restrict Atᶜ) := ⟨fun c ↦ by
    rw [Measure.restrict_apply (measurableSet_singleton c)]
    by_cases hc : c ∈ At
    · have h : ({c} : Set Y) ∩ Atᶜ = ∅ := by
        ext y
        simp only [mem_inter_iff, mem_singleton_iff, mem_compl_iff, mem_empty_iff_false,
          iff_false, not_and, not_not]
        rintro rfl
        exact hc
      rw [h, measure_empty]
    · exact le_antisymm ((measure_mono inter_subset_left).trans (not_lt.1 hc)) zero_le⟩
  have h0 : μ.map φ (P ∩ Atᶜ) = 0 := by
    have := hP ((μ.map φ).restrict Atᶜ)
    rwa [Measure.restrict_apply' hAtm.compl] at this
  have h1 : μ (φ ⁻¹' (P ∩ Atᶜ)) = 0 :=
    le_antisymm ((Measure.le_map_apply hφ.aemeasurable _).trans h0.le) zero_le
  -- The points of `A` that are sent to atoms form a countable set.
  have h2 : (A ∩ φ ⁻¹' At).Countable :=
    countable_of_injective_of_countable_image (hinj.mono inter_subset_left)
      (hAt.mono (image_subset_iff.2 inter_subset_right))
  refine measure_mono_null (t := φ ⁻¹' (P ∩ Atᶜ) ∪ A ∩ φ ⁻¹' At) (fun x hx ↦ ?_)
    (measure_union_null h1 (h2.measure_zero μ))
  by_cases hxa : φ x ∈ At
  · exact Or.inr ⟨hx, hxa⟩
  · exact Or.inl ⟨himg ⟨x, hx, rfl⟩, hxa⟩

/-- **Lemma 3, partial maps.** Let `Δ` be measurable and `φ` measurable on `Δ`. Let `A ⊆ Δ` be
such that `φ` is injective on `A` and maps `A` into a universally null set `P`. Then `A` is
universally null. -/
theorem IsUniversallyNull.of_injOn_restrict {P : Set Y} (hP : IsUniversallyNull P) {Δ : Set X}
    (hΔ : MeasurableSet Δ) {φ : X → Y} (hφ : Measurable (Δ.domRestrict φ)) {A : Set X}
    (hA : A ⊆ Δ) (hinj : InjOn φ A) (himg : φ '' A ⊆ P) : IsUniversallyNull A := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact countable_empty.isUniversallyNull
  classical
  have hψ : Measurable (Δ.piecewise φ fun _ ↦ φ a) :=
    measurable_of_restrict_of_restrict_compl hΔ (by rwa [domRestrict_piecewise])
      (by rw [domRestrict_piecewise_compl]; exact measurable_const)
  have heq : EqOn (Δ.piecewise φ fun _ ↦ φ a) φ A := fun x hx ↦ piecewise_eq_of_mem _ _ _ (hA hx)
  exact hP.of_injOn hψ (hinj.congr heq.symm) (by rwa [heq.image_eq])

end MeasureTheory
