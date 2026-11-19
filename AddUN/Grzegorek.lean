/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.Localisation
public import AddUN.Transfer
public import AddUN.Uniformity
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Grzegorek's theorem

This file proves `Grzegorek`: there is a universally null subset of the Cantor space of
cardinality `non 𝒩`.

## Proof

* `universalNull` is a measurable subset of `(ℕ → Bool) × (ℕ → ℕ)`. Each of its sections at a
  code `c : ℕ → ℕ` is null, and every null set is contained in a section
  (`exists_code_of_null`).
* Take a set `X` that is not null, of cardinality `non 𝒩`, and a well-order of `X` of order
  type `(non 𝒩).ord`. Each proper initial segment of `X` has cardinality less than `non 𝒩`, so
  it is null. Choose a code `c a` of a null set that contains the initial segment below `a`.
* The set `Y` of the pairs `(a, c a)` is universally null. Let `μ` be a finite measure on the
  pairs that vanishes on singletons. By Fubini's theorem, for almost every `x` the set of the
  pairs `(a', c)` with `x` in the section at `c` is `μ`-null. Since `X` is not null, this holds
  for some `a ∈ X`. That set contains `(b, c b)` for every `b` above `a`. The other pairs of
  `Y` form a set of cardinality less than `non 𝒩`, which is `μ`-null by
  `isUniversallyNull_of_mk_lt_non`.
* A measurable equivalence moves `Y` into the Cantor space.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal

namespace AddUN

/-- A set of cardinality less than `non 𝒩` is universally null, in every measurable space that
has a measurable injection into the Cantor space. -/
theorem isUniversallyNull_of_mk_lt_non_of_injective {Z : Type} [MeasurableSpace Z]
    {j : Z → ℕ → Bool} (hj : Measurable j) (hinj : Function.Injective j) {A : Set Z}
    (hA : #A < non 𝒩) : IsUniversallyNull A :=
  (isUniversallyNull_of_mk_lt_non (mk_image_le.trans_lt hA)).of_injOn hj hinj.injOn Subset.rfl

/-! ### A universal null set -/

/-- A fixed enumeration of the clopen subsets of the Cantor space. -/
noncomputable def clopenEnum : ℕ → Clopens (ℕ → Bool) :=
  (exists_surjective_nat (Clopens (ℕ → Bool))).choose

lemma clopenEnum_surjective : Function.Surjective clopenEnum :=
  (exists_surjective_nat (Clopens (ℕ → Bool))).choose_spec

open Classical in
/-- The `k`-th clopen set if its measure is at most `2⁻¹ ^ n`, and the empty set otherwise. -/
noncomputable def smallClopen (n k : ℕ) : Set (ℕ → Bool) :=
  if cantorMeasure (clopenEnum k) ≤ 2⁻¹ ^ n then clopenEnum k else ∅

lemma measurableSet_smallClopen (n k : ℕ) : MeasurableSet (smallClopen n k) := by
  unfold smallClopen
  split_ifs
  · exact (clopenEnum k).isClopen.isOpen.measurableSet
  · exact .empty

lemma measure_smallClopen_le (n k : ℕ) : cantorMeasure (smallClopen n k) ≤ 2⁻¹ ^ n := by
  unfold smallClopen
  split_ifs with h
  · exact h
  · simp

/-- A universal null set: the section at the code `c` is the set of the points that lie in
`smallClopen n (c n)` for infinitely many `n`. -/
def universalNull : Set ((ℕ → Bool) × (ℕ → ℕ)) :=
  {p | ∃ᶠ n in atTop, p.1 ∈ smallClopen n (p.2 n)}

lemma measurableSet_universalNull : MeasurableSet universalNull := by
  have h : universalNull = ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), ⋃ k : ℕ,
      smallClopen n k ×ˢ {c : ℕ → ℕ | c n = k} := by
    ext p
    simp only [universalNull, mem_ofPred_eq, frequently_atTop, mem_iInter, mem_iUnion, mem_prod,
      exists_prop]
    constructor
    · intro h N
      obtain ⟨n, hn, hp⟩ := h N
      exact ⟨n, hn, p.2 n, hp, rfl⟩
    · intro h N
      obtain ⟨n, hn, k, hp, hk⟩ := h N
      exact ⟨n, hn, by rwa [hk]⟩
  rw [h]
  exact .iInter fun N ↦ .iUnion fun n ↦ .iUnion fun _ ↦ .iUnion fun k ↦
    (measurableSet_smallClopen n k).prod
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)

lemma measure_section_universalNull (c : ℕ → ℕ) :
    cantorMeasure {x | (x, c) ∈ universalNull} = 0 := by
  have hsum : ∑' n, cantorMeasure (smallClopen n (c n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n ↦ measure_smallClopen_le n (c n))
    rw [ENNReal.tsum_geometric]
    simp
  refine measure_mono_null (fun x hx ↦ ?_) (measure_limsup_atTop_eq_zero hsum)
  rw [mem_limsup_iff_frequently_mem]
  exact hx

/-- Every null set is contained in a section of the universal null set. -/
lemma exists_code_of_null {G : Set (ℕ → Bool)} (hG : cantorMeasure G = 0) :
    ∃ c : ℕ → ℕ, ∀ x ∈ G, (x, c) ∈ universalNull := by
  obtain ⟨C, hC, hGC⟩ := exists_clopens_limsup cantorMeasure hG (ε := fun n ↦ 2⁻¹ ^ n)
    (fun n ↦ by simp)
  refine ⟨fun n ↦ Function.surjInv clopenEnum_surjective (C n), fun x hx ↦
    (hGC x hx).mono fun n hn ↦ ?_⟩
  have h : clopenEnum (Function.surjInv clopenEnum_surjective (C n)) = C n :=
    Function.surjInv_eq _ _
  simp only [smallClopen]
  rw [h, if_pos (hC n)]
  exact hn

/-! ### The theorem -/

/-- **Grzegorek's theorem.** There is a universally null set of cardinality `non 𝒩`. -/
theorem grzegorek : Grzegorek := by
  -- A set that is not null, of cardinality `non 𝒩`, with a well-order of the least order type.
  obtain ⟨X, hX, hXcard⟩ := exists_notMem_mk_eq_non (I := 𝒩) ⟨univ, univ_notMem_null⟩
  have hXpos : cantorMeasure X ≠ 0 := hX
  obtain ⟨r, wo, hr⟩ := Cardinal.exists_ord_eq X
  have haleph : ℵ₀ ≤ non 𝒩 := aleph0_lt_add_null.le.trans
    (add_le_non (fun x ↦ measure_singleton x) ⟨univ, univ_notMem_null⟩)
  have hinit : ∀ a : X, #{b : X | r b a} < non 𝒩 := fun a ↦ by
    have h := Cardinal.card_typein_lt (r := r) a hr
    rwa [Ordinal.card_typein, hXcard] at h
  -- A code for a null set that contains the initial segment below `a`.
  have hI : ∀ a : X, cantorMeasure (Subtype.val '' {b : X | r b a}) = 0 := fun a ↦
    mem_of_lt_non (mk_image_le.trans_lt (hinit a))
  choose c hc using fun a : X ↦ exists_code_of_null (hI a)
  let y : X → (ℕ → Bool) × (ℕ → ℕ) := fun a ↦ (a, c a)
  have hy : Function.Injective y := fun a b hab ↦ Subtype.ext (congrArg Prod.fst hab)
  have hunc : ¬ Countable (ℕ → Bool) := fun h ↦ by
    have h0 := (Set.countable_univ (α := ℕ → Bool)).measure_zero cantorMeasure
    simp at h0
  have hunc' : ¬ Countable ((ℕ → Bool) × (ℕ → ℕ)) := fun h ↦
    hunc ((Prod.mk_left_injective (fun _ ↦ 0 : ℕ → ℕ)).countable)
  let e : (ℕ → Bool) × (ℕ → ℕ) ≃ᵐ (ℕ → Bool) :=
    PolishSpace.measurableEquivOfNotCountable hunc' hunc
  -- The set of the pairs `(a, c a)` is universally null.
  have hY : IsUniversallyNull (range y) := by
    intro μ _ _
    let U' : Set ((ℕ → Bool) × ((ℕ → Bool) × (ℕ → ℕ))) :=
      (fun q ↦ (q.1, q.2.2)) ⁻¹' universalNull
    have hU' : MeasurableSet U' :=
      measurableSet_universalNull.preimage
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    have hprod : (cantorMeasure.prod μ) U' = 0 := by
      rw [Measure.prod_apply_symm hU']
      have hsec : ∀ p : (ℕ → Bool) × (ℕ → ℕ), cantorMeasure ((fun x ↦ (x, p)) ⁻¹' U') = 0 :=
        fun p ↦ measure_section_universalNull p.2
      simp [hsec]
    have hae := (Measure.measure_prod_null hU').1 hprod
    obtain ⟨a, ha⟩ : ∃ a : X, μ (Prod.mk (a : ℕ → Bool) ⁻¹' U') = 0 := by
      by_contra hno
      exact hXpos (measure_mono_null
        (show X ⊆ {x | ¬ (fun x ↦ μ (Prod.mk x ⁻¹' U')) x = (0 : (ℕ → Bool) → ℝ≥0∞) x} from
          fun x hx h0 ↦ hno ⟨⟨x, hx⟩, h0⟩) (ae_iff.1 hae))
    have hsmall : IsUniversallyNull (y '' {b : X | ¬ r a b}) := by
      refine isUniversallyNull_of_mk_lt_non_of_injective e.measurable e.injective
        (mk_image_le.trans_lt ?_)
      have hsub : {b : X | ¬ r a b} ⊆ {b | r b a} ∪ {a} := fun b hb ↦ by
        rcases trichotomous_of r a b with h | h | h
        · exact absurd h hb
        · exact Or.inr h.symm
        · exact Or.inl h
      calc #{b : X | ¬ r a b} ≤ #({b | r b a} ∪ {a} : Set X) := mk_le_mk_of_subset hsub
        _ ≤ #{b : X | r b a} + #({a} : Set X) := mk_union_le _ _
        _ < non 𝒩 := Cardinal.add_lt_of_lt haleph (hinit a)
            (by simpa using one_lt_aleph0.trans_le haleph)
    refine measure_mono_null (t := Prod.mk (a : ℕ → Bool) ⁻¹' U' ∪ y '' {b : X | ¬ r a b}) ?_
      (measure_union_null ha (hsmall μ))
    rintro _ ⟨b, rfl⟩
    by_cases hab : r a b
    · exact Or.inl (hc b a ⟨a, hab, rfl⟩)
    · exact Or.inr ⟨b, hab, rfl⟩
  -- Move the set into the Cantor space.
  refine ⟨e '' range y, hY.of_injOn e.symm.measurable e.symm.injective.injOn ?_, ?_⟩
  · rw [← image_comp]
    simp
  · rw [mk_image_eq e.injective, mk_range_eq y hy, hXcard]

end AddUN
