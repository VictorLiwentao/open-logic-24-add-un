/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.Coding

/-!
# `add 𝒩 ≤ add 𝒰𝒩`

This file proves `GotoCor513`: the additivity of the null ideal is at most the additivity of
the universally null ideal. This is Corollary 5.13 of Goto's paper. The proof here is not
Goto's.

The proof has two steps. Both use the width `h n = 2 ^ (3 * mu n + n)` of the coding lemma.

* `exists_localising_slalom`: one slalom of width `h` localises every member of a family of
  fewer than `add 𝒩` functions. For each `f` the set of points with a marker at `(n, f n)` for
  infinitely many `n` is null. Take a compact set `K` of positive measure that is disjoint
  from these sets for all `f` in the family. The slalom of the coding lemma for `K` localises
  the family, because a function that escapes it has a point of `K` with infinitely many
  markers.
* `measure_sUnion_null_of_mk_lt_add`: for every finite measure `μ` on the Cantor space, a
  union of fewer than `add 𝒩` `μ`-null sets is `μ`-null. This is
  `measure_sUnion_null_of_localised` together with the first step.
-/

@[expose] public section

open Set Filter Cardinal MeasureTheory IdealInvariant

namespace AddUN

open Coding

/-- One slalom of width `2 ^ (3 * mu n + n)` localises every member of a family of fewer than
`add 𝒩` functions. -/
theorem exists_localising_slalom {F : Set (ℕ → ℕ)} (hF : #F < add 𝒩) :
    ∃ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ 2 ^ (3 * mu n + n)) ∧
      ∀ f ∈ F, ∀ᶠ n in atTop, f n ∈ S n := by
  -- The points with infinitely many markers along `f` form a null set.
  let N : (ℕ → ℕ) → Set (ℕ → Bool) := fun f ↦ {w | ∃ᶠ n in atTop, w ∈ marker n (f n)}
  have hN : ∀ f, cantorMeasure (N f) = 0 := fun f ↦ by
    have hsum : ∑' n, cantorMeasure (marker n (f n)) ≠ ⊤ := by
      have hle : ∀ n, cantorMeasure (marker n (f n)) ≤ 2⁻¹ ^ n := fun n ↦ by
        rw [marker, cantorMeasure_cylinderOn, card_markerBlock]
        exact pow_le_pow_of_le_one zero_le (by simp) (lt_mu n).le
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
      rw [ENNReal.tsum_geometric]
      simp
    refine measure_mono_null (fun w hw ↦ ?_) (measure_limsup_atTop_eq_zero hsum)
    rw [mem_limsup_iff_frequently_mem]
    exact hw
  have hnull : ⋃₀ (N '' F) ∈ 𝒩 :=
    sUnion_mem_of_lt_add (by rintro _ ⟨f, -, rfl⟩; exact hN f) (mk_image_le.trans_lt hF)
  obtain ⟨K, hK, hKpos, hKN⟩ := exists_isCompact_disjoint_of_null hnull
  obtain ⟨S, hS, hSf⟩ := exists_slalom_decode hK hKpos fun _ ↦ false
  refine ⟨S, hS, fun f hf ↦ by_contra fun hev ↦ ?_⟩
  obtain ⟨w, hwK, hw⟩ := hSf f (not_eventually.1 hev)
  refine disjoint_left.1 hKN hwK ⟨N f, mem_image_of_mem N hf, ?_⟩
  -- The bit `0` of the code is `false`, so `w` has infinitely many markers along `f`.
  have h0 : decode f w 0 = false := congrFun hw 0
  unfold decode at h0
  rw [decide_eq_false_iff_not] at h0
  exact (not_eventually.1 h0).mono fun n hn ↦ by
    by_contra hmark
    exact hn fun h ↦ absurd h.2 hmark

/-- For every finite measure `μ` on the Cantor space, a union of fewer than `add 𝒩` `μ`-null
sets is `μ`-null. -/
theorem measure_sUnion_null_of_mk_lt_add (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ]
    {𝒢 : Set (Set (ℕ → Bool))} (h𝒢 : ∀ G ∈ 𝒢, μ G = 0) (hcard : #𝒢 < add 𝒩) :
    μ (⋃₀ 𝒢) = 0 :=
  measure_sUnion_null_of_localised μ (fun n ↦ 2 ^ (3 * mu n + n)) h𝒢 fun _ hF ↦
    exists_localising_slalom (hF.trans_lt hcard)

/-- A union of fewer than `add 𝒩` universally null sets is universally null. -/
theorem isUniversallyNull_sUnion_of_mk_lt_add {𝒜 : Set (Set (ℕ → Bool))}
    (h𝒜 : ∀ A ∈ 𝒜, IsUniversallyNull A) (hcard : #𝒜 < add 𝒩) : IsUniversallyNull (⋃₀ 𝒜) :=
  fun μ _ _ ↦ measure_sUnion_null_of_mk_lt_add μ (fun A hA ↦ h𝒜 A hA μ) hcard

/-- **Goto, Corollary 5.13.** `add 𝒩 ≤ add 𝒰𝒩`. -/
theorem gotoCor513 : GotoCor513 := by
  have hne : Nonempty {𝒜 : Set (Set (ℕ → Bool)) // 𝒜 ⊆ 𝒰𝒩 ∧ ⋃₀ 𝒜 ∉ 𝒰𝒩} := by
    refine ⟨⟨range fun x ↦ ({x} : Set (ℕ → Bool)), ?_, ?_⟩⟩
    · rintro _ ⟨x, rfl⟩
      exact (countable_singleton x).isUniversallyNull
    · have h : ⋃₀ (range fun x ↦ ({x} : Set (ℕ → Bool))) = Set.univ := by
        ext
        simp
      rw [h]
      exact not_isUniversallyNull_univ_cantor
  refine le_ciInf fun 𝒜 ↦ not_lt.1 fun hlt ↦ ?_
  exact 𝒜.2.2 (isUniversallyNull_sUnion_of_mk_lt_add (fun A hA ↦ 𝒜.2.1 hA) hlt)

end AddUN
