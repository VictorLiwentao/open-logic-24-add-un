/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.CantorMeasure
public import AddUN.Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite

/-!
# A small family of functions that no slalom localises

Lemma 1 of `notes/partial-results.md`. A *slalom* of width `h` is a map `S : ℕ → Finset ℕ` with
`(S n).card ≤ h n` for all `n`. It *localises* `f : ℕ → ℕ` if `f n ∈ S n` for all but finitely
many `n`.

* `exists_clopens_limsup`: every null set is contained in the `limsup` of a sequence of clopen
  sets with prescribed bounds on their measures.
* `exists_unlocalised_family`: for every `h` there is a family of at most `add 𝒩` functions
  that no slalom of width `h` localises.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal

namespace IdealInvariant

universe u

variable {X : Type u} {I : Set (Set X)}

/-- The additivity is attained when some subfamily of `I` has its union outside `I`. -/
theorem exists_sUnion_notMem_mk_eq_add (hI : ∃ 𝒜 ⊆ I, ⋃₀ 𝒜 ∉ I) :
    ∃ 𝒜 ⊆ I, ⋃₀ 𝒜 ∉ I ∧ #𝒜 = add I := by
  obtain ⟨𝒜, h𝒜, hU⟩ := hI
  have : Nonempty {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 ∉ I} := ⟨⟨𝒜, h𝒜, hU⟩⟩
  obtain ⟨⟨ℬ, hℬ, hV⟩, h⟩ :=
    ciInf_mem fun 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 ∉ I} ↦ #𝒜.1
  exact ⟨ℬ, hℬ, hV, h⟩

end IdealInvariant

namespace AddUN

/-- Every open subset of the Cantor space is the union of a sequence of pairwise disjoint clopen
sets. The measures of these sets add up to the measure of the open set. -/
lemma exists_clopens_iUnion_eq (μ : Measure (ℕ → Bool)) {U : Set (ℕ → Bool)} (hU : IsOpen U) :
    ∃ D : ℕ → Clopens (ℕ → Bool), ⋃ r, (D r : Set (ℕ → Bool)) = U ∧ ∑' r, μ (D r) = μ U := by
  obtain ⟨O, hO⟩ := exists_surjective_nat (Clopens (ℕ → Bool))
  classical
  let V : ℕ → Set (ℕ → Bool) := fun r ↦ if (O r : Set (ℕ → Bool)) ⊆ U then O r else ∅
  have hVc : ∀ r, IsClopen (V r) := fun r ↦ by
    by_cases h : (O r : Set (ℕ → Bool)) ⊆ U
    · simpa [V, h] using (O r).isClopen
    · simpa [V, h] using isClopen_empty
  have hVU : ⋃ r, V r = U := by
    apply Subset.antisymm
    · refine iUnion_subset fun r ↦ ?_
      by_cases h : (O r : Set (ℕ → Bool)) ⊆ U <;> simp [V, h]
    · intro x hx
      obtain ⟨s, hs, hxs, hsU⟩ := isTopologicalBasis_isClopen.exists_subset_of_mem_open hx hU
      obtain ⟨r, hr⟩ := hO ⟨s, hs⟩
      have hrs : (O r : Set (ℕ → Bool)) = s := by rw [hr]; rfl
      exact mem_iUnion.2 ⟨r, by simp [V, hrs, hsU, hxs]⟩
  have hDc : ∀ r, IsClopen (disjointed V r) := fun r ↦
    disjointedRec (fun t i ht ↦ ht.diff (hVc i)) (hVc r)
  refine ⟨fun r ↦ ⟨disjointed V r, hDc r⟩, by simpa [iUnion_disjointed] using hVU, ?_⟩
  simp only [Clopens.coe_mk]
  rw [← measure_iUnion (disjoint_disjointed V) fun r ↦ (hDc r).isOpen.measurableSet,
    iUnion_disjointed, hVU]

/-- Every null set is covered infinitely often by a sequence of clopen sets whose measures have
a finite sum. -/
lemma exists_clopens_summable {G : Set (ℕ → Bool)} (hG : cantorMeasure G = 0) :
    ∃ B : ℕ → Clopens (ℕ → Bool), ∑' i, cantorMeasure (B i) ≠ ∞ ∧
      ∀ x ∈ G, ∃ᶠ i in atTop, x ∈ B i := by
  have hU : ∀ j : ℕ, ∃ U ⊇ G, IsOpen U ∧ cantorMeasure U ≤ 2⁻¹ ^ j := fun j ↦ by
    simpa [hG] using G.exists_isOpen_le_add cantorMeasure (ε := 2⁻¹ ^ j) (by simp)
  choose U hGU hUo hUm using hU
  choose D hDU hDm using fun j ↦ exists_clopens_iUnion_eq cantorMeasure (hUo j)
  refine ⟨fun i ↦ D i.unpair.1 i.unpair.2, ?_, fun x hx ↦ ?_⟩
  · have h1 : ∑' i : ℕ, cantorMeasure (D i.unpair.1 i.unpair.2) =
        ∑' p : ℕ × ℕ, cantorMeasure (D p.1 p.2) :=
      (Nat.pairEquiv.symm.tsum_eq fun p : ℕ × ℕ ↦ cantorMeasure (D p.1 p.2))
    rw [h1, ENNReal.tsum_prod (f := fun j r ↦ cantorMeasure (D j r))]
    simp_rw [hDm]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hUm)
    rw [ENNReal.tsum_geometric]
    simp
  · have hr : ∀ j, ∃ r, x ∈ D j r := fun j ↦ by
      have : x ∈ ⋃ r, (D j r : Set (ℕ → Bool)) := by rw [hDU]; exact hGU j hx
      simpa using this
    choose r hr using hr
    rw [Nat.frequently_atTop_iff_infinite]
    refine infinite_of_injective_forall_mem (f := fun j ↦ Nat.pair j (r j)) (fun a b hab ↦ ?_)
      fun j ↦ ?_
    · exact (Nat.pair_eq_pair.1 hab).1
    · simpa using hr j

/-- A strictly increasing sequence of natural numbers splits the numbers from its first term on
into intervals. -/
lemma exists_between_of_strictMono {φ : ℕ → ℕ} (hφ : StrictMono φ) {N i : ℕ} (hi : φ N ≤ i) :
    ∃ n, N ≤ n ∧ φ n ≤ i ∧ i < φ (n + 1) := by
  have hN : N ≤ i := (hφ.le_apply).trans hi
  refine ⟨Nat.findGreatest (fun m ↦ φ m ≤ i) i, Nat.le_findGreatest hN hi,
    Nat.findGreatest_spec (P := fun m ↦ φ m ≤ i) hN hi, ?_⟩
  by_contra hcon
  have hle : Nat.findGreatest (fun m ↦ φ m ≤ i) i + 1 ≤ i :=
    (hφ.le_apply).trans (not_lt.1 hcon)
  exact Nat.findGreatest_is_greatest (P := fun m ↦ φ m ≤ i) (Nat.lt_succ_self _) hle
    (not_lt.1 hcon)

/-- Step 1 of Lemma 1. Every null set is contained in the `limsup` of a sequence of clopen sets
`C n` with `cantorMeasure (C n) ≤ ε n`. -/
theorem exists_clopens_limsup {G : Set (ℕ → Bool)} (hG : cantorMeasure G = 0) {ε : ℕ → ℝ≥0∞}
    (hε : ∀ n, ε n ≠ 0) :
    ∃ C : ℕ → Clopens (ℕ → Bool), (∀ n, cantorMeasure (C n) ≤ ε n) ∧
      ∀ x ∈ G, ∃ᶠ n in atTop, x ∈ C n := by
  obtain ⟨B, hB, hGB⟩ := exists_clopens_summable hG
  have htail : ∀ n, ∀ᶠ k in atTop, ∑' i, cantorMeasure (B (i + k)) ≤ ε n := fun n ↦
    (ENNReal.tendsto_sum_nat_add _ hB).eventually_le_const (pos_iff_ne_zero.2 (hε n))
  obtain ⟨φ, hφ, hφε⟩ := extraction_forall_of_eventually htail
  have hCc : ∀ n, IsClopen (⋃ i ∈ Finset.Ico (φ n) (φ (n + 1)), (B i : Set (ℕ → Bool))) :=
    fun n ↦ (Finset.Ico (φ n) (φ (n + 1))).finite_toSet.isClopen_biUnion fun i _ ↦ (B i).isClopen
  refine ⟨fun n ↦ ⟨_, hCc n⟩, fun n ↦ ?_, fun x hx ↦ ?_⟩
  · simp only [Clopens.coe_mk]
    refine (measure_biUnion_finset_le _ _).trans (le_trans ?_ (hφε n))
    rw [Finset.sum_Ico_eq_sum_range]
    simp_rw [add_comm (φ n)]
    exact ENNReal.sum_le_tsum _
  · rw [frequently_atTop]
    intro N
    obtain ⟨i, hi, hxi⟩ := (frequently_atTop.1 (hGB x hx)) (φ N)
    obtain ⟨n, hNn, hn1, hn2⟩ := exists_between_of_strictMono hφ hi
    refine ⟨n, hNn, ?_⟩
    change x ∈ ⋃ i ∈ Finset.Ico (φ n) (φ (n + 1)), (B i : Set (ℕ → Bool))
    exact mem_biUnion (Finset.mem_Ico.2 ⟨hn1, hn2⟩) hxi

/-- Some family of null sets has a union that is not null. -/
lemma exists_null_sUnion_notMem : ∃ 𝒜 ⊆ 𝒩, ⋃₀ 𝒜 ∉ 𝒩 := by
  refine ⟨range fun x ↦ ({x} : Set (ℕ → Bool)), ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact measure_singleton x
  · have h : ⋃₀ (range fun x ↦ ({x} : Set (ℕ → Bool))) = Set.univ := by
      ext
      simp
    simp [h]

/-- **Lemma 1.** For every `h : ℕ → ℕ` there is a family `F` of at most `add 𝒩` functions such
that no slalom of width `h` localises every member of `F`. -/
theorem exists_unlocalised_family (h : ℕ → ℕ) :
    ∃ F : Set (ℕ → ℕ), #F ≤ add 𝒩 ∧
      ∀ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ h n) → ∃ f ∈ F, ∃ᶠ n in atTop, f n ∉ S n := by
  obtain ⟨𝒢, h𝒢, hU, hcard⟩ := exists_sUnion_notMem_mk_eq_add exists_null_sUnion_notMem
  obtain ⟨O, hO⟩ := exists_surjective_nat (Clopens (ℕ → Bool))
  let ε : ℕ → ℝ≥0∞ := fun n ↦ 2⁻¹ ^ n * ((h n : ℝ≥0∞) + 1)⁻¹
  have hε : ∀ n, ε n ≠ 0 := fun n ↦ by simp [ε]
  choose C hCε hCG using fun G : 𝒢 ↦ exists_clopens_limsup (h𝒢 G.2) hε
  refine ⟨range fun G : 𝒢 ↦ fun n ↦ Function.surjInv hO (C G n), hcard ▸ mk_range_le,
    fun S hS ↦ ?_⟩
  by_contra hcon
  push Not at hcon
  classical
  -- The slalom gives a null set that contains every member of `𝒢`.
  let D : ℕ → Set (ℕ → Bool) := fun n ↦
    ⋃ k ∈ S n, if cantorMeasure (O k) ≤ ε n then (O k : Set (ℕ → Bool)) else ∅
  have hD : ∀ n, cantorMeasure (D n) ≤ 2⁻¹ ^ n := fun n ↦ by
    have h1 : cantorMeasure (D n) ≤ ∑ k ∈ S n, ε n := by
      refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
      split_ifs with hk
      · exact hk
      · simp
    refine h1.trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_left_comm]
    refine mul_le_of_le_one_right zero_le ?_
    rw [← div_eq_mul_inv]
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact (Nat.cast_le.2 (hS n)).trans le_self_add
  have hnull : cantorMeasure (limsup D atTop) = 0 := by
    refine measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hD))
    rw [ENNReal.tsum_geometric]
    simp
  refine hU (measure_mono_null (fun x hx ↦ ?_) hnull)
  obtain ⟨G, hG, hxG⟩ := hx
  have hloc : ∀ᶠ n in atTop, Function.surjInv hO (C ⟨G, hG⟩ n) ∈ S n := by
    have := hcon _ ⟨⟨G, hG⟩, rfl⟩
    simpa using this
  rw [mem_limsup_iff_frequently_mem]
  refine ((hCG ⟨G, hG⟩ x hxG).and_eventually hloc).mono fun n hn ↦ ?_
  have hOk : O (Function.surjInv hO (C ⟨G, hG⟩ n)) = C ⟨G, hG⟩ n := Function.surjInv_eq hO _
  refine mem_biUnion hn.2 ?_
  rw [hOk, if_pos (hCε ⟨G, hG⟩ n)]
  exact hn.1

end AddUN
