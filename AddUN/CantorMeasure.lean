/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox

/-!
# The coin-tossing measure on the Cantor space

This file collects the facts about `cantorMeasure` that the proof of Theorem B uses.

* `measurePreserving_flip`: flipping one coordinate preserves the measure.
* `Determined s E`: membership in `E` depends only on the coordinates in `s`.
* `cantorMeasure_inter_cylinder`: an event that does not depend on the coordinates in a finite
  set `B` is independent of every cylinder on `B`.
* `cantorMeasure_cylinder`: a cylinder on `B` has measure `2⁻¹ ^ B.card`.
* `exists_isCompact_disjoint_of_null`: the complement of a null set contains a compact set of
  positive measure.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace
open scoped ENNReal

namespace MeasureTheory

/-! ### Flipping one coordinate -/

/-- Flip the coordinate `i` of a point of the Cantor space. -/
def flip (i : ℕ) (w : ℕ → Bool) : ℕ → Bool := fun j ↦ if j = i then !w j else w j

@[simp]
lemma flip_apply_self (i : ℕ) (w : ℕ → Bool) : flip i w i = !w i := by simp [flip]

lemma flip_apply_of_ne {i j : ℕ} (h : j ≠ i) (w : ℕ → Bool) : flip i w j = w j := by
  simp [flip, h]

@[simp]
lemma flip_flip (i : ℕ) (w : ℕ → Bool) : flip i (flip i w) = w := by
  ext j
  by_cases h : j = i <;> simp [flip, h]

lemma uniformBool_map_not :
    (PMF.uniformOfFintype Bool).toMeasure.map (fun b ↦ !b) =
      (PMF.uniformOfFintype Bool).toMeasure := by
  refine Measure.ext_of_singleton fun a ↦ ?_
  have h : (fun b : Bool ↦ !b) ⁻¹' {a} = {!a} := by
    ext b
    cases a <;> cases b <;> simp
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton a), h,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.uniformOfFintype_apply]

/-- Flipping one coordinate preserves the coin-tossing measure. -/
theorem measurePreserving_flip (i : ℕ) :
    MeasurePreserving (flip i) cantorMeasure cantorMeasure := by
  have hf : ∀ j : ℕ, Measurable (fun b : Bool ↦ if j = i then !b else b) := fun j ↦ by fun_prop
  have hflip : flip i = fun (w : ℕ → Bool) j ↦ (fun b : Bool ↦ if j = i then !b else b) (w j) :=
    rfl
  refine ⟨by rw [hflip]; fun_prop, ?_⟩
  rw [hflip, cantorMeasure, Measure.infinitePi_map_pi _ hf]
  congr 1
  ext1 j
  by_cases h : j = i
  · simp only [h, if_true]
    exact uniformBool_map_not
  · simp only [h, if_false]
    exact Measure.map_id'

lemma measurableEmbedding_flip (i : ℕ) : MeasurableEmbedding (flip i) :=
  MeasurableEquiv.measurableEmbedding
    { toFun := flip i
      invFun := flip i
      left_inv := flip_flip i
      right_inv := flip_flip i
      measurable_toFun := (measurePreserving_flip i).measurable
      measurable_invFun := (measurePreserving_flip i).measurable }

/-! ### Events determined by a set of coordinates -/

/-- Membership in `E` depends only on the coordinates in `s`. -/
def Determined (s : Set ℕ) (E : Set (ℕ → Bool)) : Prop :=
  ∀ ⦃w w' : ℕ → Bool⦄, (∀ i ∈ s, w i = w' i) → w ∈ E → w' ∈ E

namespace Determined

variable {s t : Set ℕ} {E F : Set (ℕ → Bool)}

lemma mem_iff (h : Determined s E) {w w' : ℕ → Bool} (hw : ∀ i ∈ s, w i = w' i) :
    w ∈ E ↔ w' ∈ E :=
  ⟨fun hE ↦ h hw hE, fun hE ↦ h (fun i hi ↦ (hw i hi).symm) hE⟩

lemma mono (h : Determined s E) (hst : s ⊆ t) : Determined t E :=
  fun _ _ hw hE ↦ h (fun i hi ↦ hw i (hst hi)) hE

lemma univ : Determined s (Set.univ : Set (ℕ → Bool)) := fun _ _ _ _ ↦ trivial

lemma inter (hE : Determined s E) (hF : Determined s F) : Determined s (E ∩ F) :=
  fun _ _ hw h ↦ ⟨hE hw h.1, hF hw h.2⟩

lemma compl (hE : Determined s E) : Determined s Eᶜ :=
  fun _ _ hw h h' ↦ h (hE (fun i hi ↦ (hw i hi).symm) h')

lemma diff (hE : Determined s E) (hF : Determined s F) : Determined s (E \ F) :=
  hE.inter hF.compl

/-- An event that does not depend on the coordinate `i` is invariant under the flip at `i`. -/
lemma preimage_flip {i : ℕ} (hE : Determined s E) (hi : i ∉ s) : flip i ⁻¹' E = E := by
  ext w
  exact hE.mem_iff fun j hj ↦ flip_apply_of_ne (by rintro rfl; exact hi hj) w

end Determined

/-- The cylinder of the points that agree with `v` on the finite set `B`. -/
def cylinderOn (B : Finset ℕ) (v : ℕ → Bool) : Set (ℕ → Bool) := {w | ∀ i ∈ B, w i = v i}

lemma mem_cylinderOn {B : Finset ℕ} {v w : ℕ → Bool} : w ∈ cylinderOn B v ↔ ∀ i ∈ B, w i = v i :=
  Iff.rfl

lemma cylinderOn_eq_biInter (B : Finset ℕ) (v : ℕ → Bool) :
    cylinderOn B v = ⋂ i ∈ B, (fun w : ℕ → Bool ↦ w i) ⁻¹' {v i} := by
  ext w
  simp [cylinderOn]

lemma isClopen_cylinderOn (B : Finset ℕ) (v : ℕ → Bool) : IsClopen (cylinderOn B v) := by
  rw [cylinderOn_eq_biInter]
  exact B.finite_toSet.isClopen_biInter fun i _ ↦
    (isClopen_discrete {v i}).preimage (continuous_apply i)

lemma measurableSet_cylinderOn (B : Finset ℕ) (v : ℕ → Bool) : MeasurableSet (cylinderOn B v) :=
  (isClopen_cylinderOn B v).isClosed.measurableSet

lemma determined_cylinderOn (B : Finset ℕ) (v : ℕ → Bool) {s : Set ℕ} (h : ↑B ⊆ s) :
    Determined s (cylinderOn B v) :=
  fun _ _ hw hE i hi ↦ (hw i (h hi)).symm.trans (hE i hi)

lemma cylinderOn_insert {B : Finset ℕ} {i : ℕ} (v : ℕ → Bool) :
    cylinderOn (insert i B) v = cylinderOn B v ∩ {w | w i = v i} := by
  ext w
  simp [cylinderOn, and_comm]

/-! ### Independence -/

/-- An event that is invariant under the flip at `i` is split into two halves of equal measure
by the coordinate `i`. -/
theorem cantorMeasure_inter_coord {E : Set (ℕ → Bool)} {i : ℕ} (hflip : flip i ⁻¹' E = E)
    (b : Bool) : cantorMeasure (E ∩ {w | w i = b}) = cantorMeasure E / 2 := by
  have hmeas : ∀ b : Bool, MeasurableSet {w : ℕ → Bool | w i = b} := fun b ↦
    measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  have hpre : flip i ⁻¹' (E ∩ {w | w i = !b}) = E ∩ {w | w i = b} := by
    rw [preimage_inter, hflip]
    ext w
    cases b <;> simp
  have heq : cantorMeasure (E ∩ {w | w i = b}) = cantorMeasure (E ∩ {w | w i = !b}) := by
    rw [← hpre]
    exact (measurePreserving_flip i).measure_preimage_emb (measurableEmbedding_flip i) _
  have hdiff : E \ {w | w i = b} = E ∩ {w | w i = !b} := by
    ext w
    cases b <;> simp
  have hsum := measure_inter_add_sdiff (μ := cantorMeasure) E (hmeas b)
  rw [hdiff, ← heq, ← two_mul] at hsum
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]
  exact hsum

/-- **Independence.** An event that does not depend on the coordinates in the finite set `B` is
independent of every cylinder on `B`. -/
theorem cantorMeasure_inter_cylinder {E : Set (ℕ → Bool)} (B : Finset ℕ) (v : ℕ → Bool)
    (hE : Determined (↑B)ᶜ E) :
    cantorMeasure (E ∩ cylinderOn B v) = cantorMeasure E * 2⁻¹ ^ B.card := by
  induction B using Finset.induction_on with
  | empty => simp [cylinderOn]
  | insert i B hi ih =>
    have hE' : Determined (↑B)ᶜ E := hE.mono (by simp)
    have hdet : Determined {i}ᶜ (E ∩ cylinderOn B v) :=
      (hE.mono (by simp)).inter (determined_cylinderOn B v (by simpa using hi))
    rw [cylinderOn_insert, ← inter_assoc,
      cantorMeasure_inter_coord (hdet.preimage_flip (by simp)), ih hE',
      Finset.card_insert_of_notMem hi, pow_succ, ENNReal.div_eq_inv_mul]
    ring

/-- A cylinder on the finite set `B` has measure `2⁻¹ ^ B.card`. -/
theorem cantorMeasure_cylinderOn (B : Finset ℕ) (v : ℕ → Bool) :
    cantorMeasure (cylinderOn B v) = 2⁻¹ ^ B.card := by
  simpa using cantorMeasure_inter_cylinder B v (E := Set.univ) Determined.univ

/-! ### Compact sets of positive measure -/

instance : Countable (Clopens (ℕ → Bool)) :=
  Clopens.countable_iff_secondCountable.2 inferInstance

/-- The complement of a null set contains a compact set of positive measure. -/
theorem exists_isCompact_disjoint_of_null {G : Set (ℕ → Bool)} (hG : cantorMeasure G = 0) :
    ∃ K : Set (ℕ → Bool), IsCompact K ∧ cantorMeasure K ≠ 0 ∧ Disjoint K G := by
  obtain ⟨U, hGU, hU, hμU⟩ := G.exists_isOpen_le_add cantorMeasure (ε := 2⁻¹) (by simp)
  refine ⟨Uᶜ, hU.isClosed_compl.isCompact, fun h0 ↦ ?_,
    disjoint_compl_left.mono_right hGU⟩
  have h1 : cantorMeasure U = 1 := by
    have := measure_add_measure_compl (μ := cantorMeasure) hU.measurableSet
    rwa [h0, add_zero, measure_univ] at this
  rw [hG, zero_add, h1] at hμU
  exact absurd hμU (by simp)

end MeasureTheory
