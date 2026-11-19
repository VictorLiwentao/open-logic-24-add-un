/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.InitialCylinder
public import AddUN.Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# `non 𝒰𝒩 = non 𝒩`

This file proves `GotoProp54`. This is Proposition 5.4 of Goto's paper. The proof here does
not use the measure isomorphism theorem.

Let `μ` be a finite measure on the Cantor space that vanishes on singletons.

* `exists_measurableSet_subset_measure_eq_half`: every measurable set has a measurable subset
  of half its measure. The proof embeds the space in the real line and cuts at a suitable
  point.
* `split μ`: a measurable map of the Cantor space to itself. Its fibres over the initial
  cylinders are obtained by halving again and again, so `μ.map (split μ)` is `μ univ` times the
  coin-tossing measure (`map_split`).
* `isUniversallyNull_of_mk_lt_non`: a set of cardinality less than `non 𝒩` is universally null.
  Its image under `split μ` is null, and the preimage of a null set is `μ`-null.
-/

@[expose] public section

open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal

namespace MeasureTheory

/-- A finite measure that vanishes on singletons, on a standard Borel space: every measurable
set has a measurable subset of half its measure. -/
theorem exists_measurableSet_subset_measure_eq_half {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {B : Set X} (hB : MeasurableSet B) : ∃ B' ⊆ B, MeasurableSet B' ∧ μ B' = μ B / 2 := by
  by_cases h0 : μ B = 0
  · exact ⟨∅, empty_subset _, .empty, by simp [h0]⟩
  have hψ : Measurable (embeddingReal X) := measurable_embeddingReal X
  have hψi : Function.Injective (embeddingReal X) := (measurableEmbedding_embeddingReal X).injective
  set ψ := embeddingReal X
  let G : ℝ → ℝ≥0∞ := fun t ↦ μ (B ∩ ψ ⁻¹' Iic t)
  have hGm : Monotone G := fun a b hab ↦
    measure_mono (inter_subset_inter_right _ (preimage_mono (Iic_subset_Iic.2 hab)))
  have hmeas : ∀ t, MeasurableSet (B ∩ ψ ⁻¹' Iic t) := fun t ↦ hB.inter (hψ measurableSet_Iic)
  have hpos : 0 < μ B / 2 := ENNReal.div_pos h0 (by simp)
  have hlt : μ B / 2 < μ B := ENNReal.half_lt_self h0 (measure_ne_top _ _)
  -- `G` is small far to the left and large far to the right.
  have hbot : Tendsto (fun n : ℕ ↦ G (-(n : ℝ))) atTop (𝓝 0) := by
    have hlim := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun n : ℕ ↦ B ∩ ψ ⁻¹' Iic (-(n : ℝ))) (fun n ↦ (hmeas _).nullMeasurableSet)
      (fun m n hmn ↦ inter_subset_inter_right _
        (preimage_mono (Iic_subset_Iic.2 (neg_le_neg (Nat.cast_le.2 hmn)))))
      ⟨0, measure_ne_top _ _⟩
    have hempty : ⋂ n : ℕ, B ∩ ψ ⁻¹' Iic (-(n : ℝ)) = ∅ := by
      ext x
      simp only [mem_iInter, mem_inter_iff, mem_preimage, mem_Iic, mem_empty_iff_false,
        iff_false, not_forall]
      obtain ⟨n, hn⟩ := exists_nat_gt (-ψ x)
      exact ⟨n, fun h ↦ by linarith [h.2]⟩
    rwa [hempty, measure_empty] at hlim
  obtain ⟨n₀, hn₀⟩ := (hbot.eventually_lt_const hpos).exists
  have htop : Tendsto (fun n : ℕ ↦ G (n : ℝ)) atTop (𝓝 (μ B)) := by
    have hlim := tendsto_measure_iUnion_atTop (μ := μ)
      (s := fun n : ℕ ↦ B ∩ ψ ⁻¹' Iic (n : ℝ)) (fun m n hmn ↦ inter_subset_inter_right _
        (preimage_mono (Iic_subset_Iic.2 (Nat.cast_le.2 hmn))))
    have hU : ⋃ n : ℕ, B ∩ ψ ⁻¹' Iic (n : ℝ) = B := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_Iic, exists_and_left,
        and_iff_left_iff_imp]
      exact fun _ ↦ exists_nat_ge (ψ x)
    rwa [hU] at hlim
  obtain ⟨n₁, hn₁⟩ := (htop.eventually_const_lt hlt).exists
  -- Cut at the supremum of the points where `G` is at most half the measure of `B`.
  let S : Set ℝ := {t | G t ≤ μ B / 2}
  have hSne : S.Nonempty := ⟨-(n₀ : ℝ), hn₀.le⟩
  have hSbdd : BddAbove S :=
    ⟨n₁, fun t ht ↦ le_of_not_gt fun hgt ↦ (hn₁.trans_le (hGm hgt.le)).not_ge ht⟩
  have hinv : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n ↦ by positivity
  have ha : μ B / 2 ≤ G (sSup S) := by
    have hlim := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun n : ℕ ↦ B ∩ ψ ⁻¹' Iic (sSup S + 1 / ((n : ℝ) + 1)))
      (fun n ↦ (hmeas _).nullMeasurableSet)
      (fun m n hmn ↦ inter_subset_inter_right _ (preimage_mono (Iic_subset_Iic.2
        (add_le_add_right (Nat.one_div_le_one_div hmn) _))))
      ⟨0, measure_ne_top _ _⟩
    have hI : ⋂ n : ℕ, B ∩ ψ ⁻¹' Iic (sSup S + 1 / ((n : ℝ) + 1)) = B ∩ ψ ⁻¹' Iic (sSup S) := by
      ext x
      simp only [mem_iInter, mem_inter_iff, mem_preimage, mem_Iic]
      constructor
      · intro h
        refine ⟨(h 0).1, le_of_not_gt fun hgt ↦ ?_⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hgt)
        linarith [(h n).2]
      · exact fun h n ↦ ⟨h.1, h.2.trans (by linarith [hinv n])⟩
    rw [hI] at hlim
    refine ge_of_tendsto' hlim fun n ↦ ?_
    have hnot : sSup S + 1 / ((n : ℝ) + 1) ∉ S := fun hmem ↦ by
      linarith [le_csSup hSbdd hmem, hinv n]
    exact (not_le.1 hnot).le
  have hb : μ (B ∩ ψ ⁻¹' Iio (sSup S)) ≤ μ B / 2 := by
    have hlim := tendsto_measure_iUnion_atTop (μ := μ)
      (s := fun n : ℕ ↦ B ∩ ψ ⁻¹' Iic (sSup S - 1 / ((n : ℝ) + 1)))
      (fun m n hmn ↦ inter_subset_inter_right _ (preimage_mono (Iic_subset_Iic.2
        (sub_le_sub_left (Nat.one_div_le_one_div hmn) _))))
    have hU : ⋃ n : ℕ, B ∩ ψ ⁻¹' Iic (sSup S - 1 / ((n : ℝ) + 1)) = B ∩ ψ ⁻¹' Iio (sSup S) := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_Iic, mem_Iio]
      constructor
      · rintro ⟨n, h1, h2⟩
        exact ⟨h1, by linarith [hinv n]⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h2)
        exact ⟨n, h1, by linarith⟩
    rw [hU] at hlim
    refine le_of_tendsto' hlim fun n ↦ ?_
    obtain ⟨s, hs, hslt⟩ := exists_lt_of_lt_csSup hSne
      (show sSup S - 1 / ((n : ℝ) + 1) < sSup S by linarith [hinv n])
    exact (hGm hslt.le).trans hs
  have hc : G (sSup S) ≤ μ B / 2 := by
    have hsub : B ∩ ψ ⁻¹' Iic (sSup S) ⊆ B ∩ ψ ⁻¹' Iio (sSup S) ∪ ψ ⁻¹' {sSup S} := by
      rintro x ⟨hxB, hx⟩
      rcases lt_or_eq_of_le (show ψ x ≤ sSup S from hx) with h | h
      · exact Or.inl ⟨hxB, h⟩
      · exact Or.inr h
    have hsing : μ (ψ ⁻¹' {sSup S}) = 0 :=
      Set.Subsingleton.measure_zero (subsingleton_singleton.preimage hψi) μ
    calc G (sSup S) ≤ μ (B ∩ ψ ⁻¹' Iio (sSup S) ∪ ψ ⁻¹' {sSup S}) := measure_mono hsub
      _ ≤ μ (B ∩ ψ ⁻¹' Iio (sSup S)) + μ (ψ ⁻¹' {sSup S}) := measure_union_le _ _
      _ ≤ μ B / 2 := by rw [hsing, add_zero]; exact hb
  exact ⟨B ∩ ψ ⁻¹' Iic (sSup S), inter_subset_left, hmeas _, le_antisymm hc ha⟩

/-! ### A measure-preserving map onto the coin-tossing measure -/

section Split

variable (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] [NullSingletonClass μ]

open Classical in
/-- A measurable subset of `B` of half the measure of `B`, when `B` is measurable. -/
noncomputable def half (B : Set (ℕ → Bool)) : Set (ℕ → Bool) :=
  if hB : MeasurableSet B then (exists_measurableSet_subset_measure_eq_half μ hB).choose else ∅

lemma half_subset (B : Set (ℕ → Bool)) : half μ B ⊆ B := by
  unfold half
  split_ifs with hB
  · exact (exists_measurableSet_subset_measure_eq_half μ hB).choose_spec.1
  · exact empty_subset _

lemma measurableSet_half (B : Set (ℕ → Bool)) : MeasurableSet (half μ B) := by
  unfold half
  split_ifs with hB
  · exact (exists_measurableSet_subset_measure_eq_half μ hB).choose_spec.2.1
  · exact .empty

lemma measure_half {B : Set (ℕ → Bool)} (hB : MeasurableSet B) : μ (half μ B) = μ B / 2 := by
  unfold half
  rw [dif_pos hB]
  exact (exists_measurableSet_subset_measure_eq_half μ hB).choose_spec.2.2

/-- The cells of the halving tree. The list gives the choices made, the last one first. -/
noncomputable def cell : List Bool → Set (ℕ → Bool)
  | [] => univ
  | b :: s => if b then half μ (cell s) else cell s \ half μ (cell s)

lemma measurableSet_cell (s : List Bool) : MeasurableSet (cell μ s) := by
  induction s with
  | nil => exact .univ
  | cons b s ih =>
    cases b
    · simpa [cell] using ih.diff (measurableSet_half μ _)
    · simpa [cell] using measurableSet_half μ _

lemma measure_cell (s : List Bool) : μ (cell μ s) = μ univ * 2⁻¹ ^ s.length := by
  induction s with
  | nil => simp [cell]
  | cons b s ih =>
    have hh := measure_half μ (measurableSet_cell μ s)
    cases b
    · simp only [cell, Bool.false_eq_true, if_false, List.length_cons]
      rw [measure_sdiff (half_subset μ _) (measurableSet_half μ _).nullMeasurableSet
        (measure_ne_top _ _), hh, ENNReal.sub_half (measure_ne_top _ _), ih, pow_succ,
        div_eq_mul_inv, mul_assoc]
    · simp only [cell, if_true, List.length_cons]
      rw [hh, ih, pow_succ, div_eq_mul_inv, mul_assoc]

open Classical in
/-- The choices that lead to the cell of level `n` that contains `x`, the last one first. -/
noncomputable def pre (x : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => decide (x ∈ half μ (cell μ (pre x n))) :: pre x n

open Classical in
/-- The map that sends `x` to its sequence of choices in the halving tree. -/
noncomputable def split (x : ℕ → Bool) (n : ℕ) : Bool :=
  decide (x ∈ half μ (cell μ (pre μ x n)))

/-- The first `n` values of `v`, the last one first. -/
def revPrefix (v : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => v n :: revPrefix v n

@[simp]
lemma length_revPrefix (v : ℕ → Bool) (n : ℕ) : (revPrefix v n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [revPrefix, ih]

lemma revPrefix_congr {v v' : ℕ → Bool} {n : ℕ} (h : ∀ i < n, v i = v' i) :
    revPrefix v n = revPrefix v' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [revPrefix]
    rw [h n (Nat.lt_succ_self n), ih fun i hi ↦ h i (Nat.lt_succ_of_lt hi)]

lemma pre_eq (x : ℕ → Bool) (n : ℕ) : pre μ x n = revPrefix (split μ x) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pre, revPrefix, split, ih]

lemma mem_cell_pre (x : ℕ → Bool) (n : ℕ) : x ∈ cell μ (pre μ x n) := by
  induction n with
  | zero => exact mem_univ x
  | succ n ih =>
    by_cases hx : x ∈ half μ (cell μ (pre μ x n))
    · simp [pre, cell, hx]
    · simpa [pre, cell, hx] using ih

lemma mem_cell_revPrefix_iff (x v : ℕ → Bool) (n : ℕ) :
    x ∈ cell μ (revPrefix v n) ↔ ∀ i < n, split μ x i = v i := by
  constructor
  · induction n with
    | zero => exact fun _ i hi ↦ absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
      intro hx
      have hsub : x ∈ cell μ (revPrefix v n) := by
        simp only [revPrefix, cell] at hx
        split_ifs at hx
        · exact half_subset μ _ hx
        · exact hx.1
      have hlow := ih hsub
      have hpre : pre μ x n = revPrefix v n := by rw [pre_eq, revPrefix_congr hlow]
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact hlow i h
      · simp only [revPrefix, cell] at hx
        unfold split
        rw [hpre]
        split_ifs at hx with hv
        · rw [hv]
          simpa using hx
        · rw [Bool.eq_false_iff.2 hv]
          simpa using hx.2
  · intro h
    rw [← revPrefix_congr h, ← pre_eq]
    exact mem_cell_pre μ x n

lemma split_preimage_cylinderOn (n : ℕ) (v : ℕ → Bool) :
    split μ ⁻¹' cylinderOn (Finset.range n) v = cell μ (revPrefix v n) := by
  ext x
  simp [mem_cylinderOn, mem_cell_revPrefix_iff]

lemma measurable_split : Measurable (split μ) := by
  have h := @measurable_generateFrom (ℕ → Bool) (ℕ → Bool) _ initialCylinders (split μ) (by
    rintro _ ⟨n, v, rfl⟩
    rw [split_preimage_cylinderOn]
    exact measurableSet_cell μ _)
  rwa [← generateFrom_initialCylinders] at h

/-- The map `split μ` sends `μ` to `μ univ` times the coin-tossing measure. -/
theorem map_split : μ.map (split μ) = μ univ • cantorMeasure := by
  refine Measure.ext_of_initialCylinders fun n v ↦ ?_
  rw [Measure.map_apply (measurable_split μ) (measurableSet_cylinderOn _ _),
    split_preimage_cylinderOn, measure_cell, Measure.smul_apply, cantorMeasure_cylinderOn,
    smul_eq_mul, Finset.card_range, length_revPrefix]

end Split

end MeasureTheory

namespace AddUN

/-- A set of cardinality less than `non 𝒩` is universally null. -/
theorem isUniversallyNull_of_mk_lt_non {A : Set (ℕ → Bool)} (hA : #A < non 𝒩) :
    IsUniversallyNull A := by
  intro μ _ _
  have hnull : cantorMeasure (split μ '' A) = 0 := mem_of_lt_non (mk_image_le.trans_lt hA)
  have h1 : μ.map (split μ) (toMeasurable cantorMeasure (split μ '' A)) = 0 := by
    rw [map_split, Measure.smul_apply, measure_toMeasurable, hnull, smul_zero]
  rw [Measure.map_apply (measurable_split μ) (measurableSet_toMeasurable _ _)] at h1
  exact measure_mono_null (show A ⊆ split μ ⁻¹' toMeasurable cantorMeasure (split μ '' A) from
    fun x hx ↦ subset_toMeasurable _ _ (mem_image_of_mem _ hx)) h1

/-- **Goto, Proposition 5.4.** `non 𝒰𝒩 = non 𝒩`. -/
theorem gotoProp54 : GotoProp54 := by
  have hne : Nonempty {A : Set (ℕ → Bool) // A ∉ 𝒰𝒩} := ⟨⟨univ, not_isUniversallyNull_univ_cantor⟩⟩
  exact le_antisymm non_universallyNull_le_non_null
    (le_ciInf fun A ↦ not_lt.1 fun hlt ↦ A.2 (isUniversallyNull_of_mk_lt_non hlt))

end AddUN
