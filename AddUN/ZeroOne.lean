/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.InitialCylinder

/-!
# A zero–one law for the coin-tossing measure

`flipSet s` flips the coordinates in the finite set `s`. A measurable set that is invariant
under every `flipSet s` has measure `0` or `1`
(`measure_eq_zero_or_one_of_flipSet_invariant`). Such a set does not depend on any finite set
of coordinates, so it is independent of every initial cylinder, hence of itself.

`saturation E` is the set of the points that differ from a point of `E` on finitely many
coordinates. If `E` is measurable and not null, then `saturation E` has measure `1`. So every
set that is not null contains a point with a finite modification in `E`
(`exists_flipSet_mem`).
-/

@[expose] public section

open Set

namespace MeasureTheory

/-- Flip the coordinates in the finite set `s`. -/
def flipSet (s : Finset ℕ) (w : ℕ → Bool) : ℕ → Bool := fun j ↦ if j ∈ s then !w j else w j

lemma flipSet_apply_of_mem {s : Finset ℕ} {j : ℕ} (h : j ∈ s) (w : ℕ → Bool) :
    flipSet s w j = !w j := by
  simp [flipSet, h]

lemma flipSet_apply_of_notMem {s : Finset ℕ} {j : ℕ} (h : j ∉ s) (w : ℕ → Bool) :
    flipSet s w j = w j := by
  simp [flipSet, h]

lemma flipSet_flipSet (s t : Finset ℕ) (w : ℕ → Bool) :
    flipSet s (flipSet t w) = flipSet (symmDiff s t) w := by
  ext j
  by_cases hs : j ∈ s <;> by_cases ht : j ∈ t <;> simp [flipSet, Finset.mem_symmDiff, hs, ht]

/-- Flipping finitely many coordinates preserves the coin-tossing measure. -/
theorem measurePreserving_flipSet (s : Finset ℕ) :
    MeasurePreserving (flipSet s) cantorMeasure cantorMeasure := by
  have hf : ∀ j : ℕ, Measurable (fun b : Bool ↦ if j ∈ s then !b else b) := fun j ↦ by fun_prop
  have hflip : flipSet s =
      fun (w : ℕ → Bool) j ↦ (fun b : Bool ↦ if j ∈ s then !b else b) (w j) := rfl
  refine ⟨by rw [hflip]; fun_prop, ?_⟩
  rw [hflip, cantorMeasure, Measure.infinitePi_map_pi _ hf]
  congr 1
  ext1 j
  by_cases h : j ∈ s
  · simp only [h, if_true]
    exact uniformBool_map_not
  · simp only [h, if_false]
    exact Measure.map_id'

/-- **A zero–one law.** A measurable set that is invariant under every finite flip has measure
`0` or `1`. -/
theorem measure_eq_zero_or_one_of_flipSet_invariant {E : Set (ℕ → Bool)} (hE : MeasurableSet E)
    (hinv : ∀ t : Finset ℕ, flipSet t ⁻¹' E = E) :
    cantorMeasure E = 0 ∨ cantorMeasure E = 1 := by
  -- `E` does not depend on the first `n` coordinates.
  have hdet : ∀ n : ℕ, Determined (↑(Finset.range n))ᶜ E := by
    intro n w w' hww' hw
    have hfl : w = flipSet ((Finset.range n).filter fun j ↦ w j ≠ w' j) w' := by
      ext j
      by_cases hj : j ∈ (Finset.range n).filter fun j ↦ w j ≠ w' j
      · rw [flipSet_apply_of_mem hj]
        have hne := (Finset.mem_filter.1 hj).2
        cases hw1 : w j <;> cases hw2 : w' j <;> simp_all
      · rw [flipSet_apply_of_notMem hj]
        by_cases hjn : j ∈ Finset.range n
        · by_contra hne
          exact hj (Finset.mem_filter.2 ⟨hjn, hne⟩)
        · exact hww' j (by simpa using hjn)
    rw [hfl] at hw
    rw [← hinv ((Finset.range n).filter fun j ↦ w j ≠ w' j)]
    exact hw
  -- So `E` is independent of every measurable set, and of itself.
  have hmeas : cantorMeasure.restrict E = cantorMeasure E • cantorMeasure := by
    refine Measure.ext_of_initialCylinders fun n v ↦ ?_
    rw [Measure.restrict_apply (measurableSet_cylinderOn _ _), inter_comm,
      cantorMeasure_inter_cylinder _ _ (hdet n), Measure.smul_apply, cantorMeasure_cylinderOn,
      smul_eq_mul]
  have h2 : cantorMeasure E = cantorMeasure E * cantorMeasure E := by
    have h := congrArg (fun ν : Measure (ℕ → Bool) ↦ ν E) hmeas
    simpa [Measure.restrict_apply hE] using h
  by_cases h0 : cantorMeasure E = 0
  · exact Or.inl h0
  · refine Or.inr ((ENNReal.mul_right_inj h0 (measure_ne_top _ _)).1 ?_)
    rw [mul_one]
    exact h2.symm

/-- The points that differ from a point of `E` on finitely many coordinates. -/
def saturation (E : Set (ℕ → Bool)) : Set (ℕ → Bool) := ⋃ s : Finset ℕ, flipSet s ⁻¹' E

lemma subset_saturation (E : Set (ℕ → Bool)) : E ⊆ saturation E := fun w hw ↦
  mem_iUnion.2 ⟨∅, by
    have h : flipSet ∅ w = w := by
      ext j
      simp [flipSet]
    rwa [mem_preimage, h]⟩

lemma measurableSet_saturation {E : Set (ℕ → Bool)} (hE : MeasurableSet E) :
    MeasurableSet (saturation E) :=
  .iUnion fun s ↦ (measurePreserving_flipSet s).measurable hE

lemma flipSet_preimage_saturation (E : Set (ℕ → Bool)) (t : Finset ℕ) :
    flipSet t ⁻¹' saturation E = saturation E := by
  ext w
  simp only [saturation, mem_preimage, mem_iUnion]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨symmDiff s t, by rwa [← flipSet_flipSet]⟩
  · rintro ⟨s, hs⟩
    exact ⟨symmDiff s t, by rwa [flipSet_flipSet, symmDiff_symmDiff_cancel_right]⟩

theorem measure_saturation_eq_one {E : Set (ℕ → Bool)} (hE : MeasurableSet E)
    (hpos : cantorMeasure E ≠ 0) : cantorMeasure (saturation E) = 1 :=
  (measure_eq_zero_or_one_of_flipSet_invariant (measurableSet_saturation hE)
    (flipSet_preimage_saturation E)).resolve_left
      fun h0 ↦ hpos (measure_mono_null (subset_saturation E) h0)

/-- A set that is not null contains a point with a finite modification in a given measurable
set of positive measure. -/
theorem exists_flipSet_mem {X E : Set (ℕ → Bool)} (hX : cantorMeasure X ≠ 0)
    (hE : MeasurableSet E) (hpos : cantorMeasure E ≠ 0) :
    ∃ x ∈ X, ∃ s : Finset ℕ, flipSet s x ∈ E := by
  by_contra hno
  refine hX (measure_mono_null (t := (saturation E)ᶜ) (fun x hx hsat ↦ ?_) ?_)
  · obtain ⟨s, hs⟩ := mem_iUnion.1 hsat
    exact hno ⟨x, hx, s, hs⟩
  · rw [measure_compl (measurableSet_saturation hE) (measure_ne_top _ _), measure_univ,
      measure_saturation_eq_one hE hpos, tsub_self]

end MeasureTheory
