/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.Grzegorek
public import AddUN.ZeroOne

/-!
# Theorem A: `add 𝒰𝒩 ≤ 𝔡`

This file proves `TheoremA` of `notes/partial-results.md`.

## Proof

Let `P` be a universally null set of cardinality `non 𝒩` (Grzegorek's theorem), `X` a set that
is not null, of the same cardinality, and `e` a bijection from `X` to `P`. Let `D` be a
dominating family of cardinality `𝔡`.

For `g ∈ D` and `k₀ : ℕ` put `h k = Nat.pair k (g (k + k₀))`. This map is injective and
`g (k + k₀) ≤ h k`. For a finite set `s` let `W (g, k₀, s)` be the set of the points
`overwrite h (e x) (flipSet s x)`, `x ∈ X`: flip the coordinates of `x` in `s`, then write the
code `e x` on the coordinates `h 0, h 1, …`.

* Each `W (g, k₀, s)` is universally null by Lemma 3: the map `w ↦ (n ↦ w (h n))` reads the
  code, so it sends the set injectively into `P`.
* The union is not null. Let `K` be compact of positive measure. `exists_levels` gives a
  sequence `M` such that, if `M k ≤ h k` for all `k`, then the set of the points `u` whose
  modifications on the range of `h` all lie in `K` has positive measure. Since `D` is
  dominating, some `g ∈ D` and `k₀` give such an `h`. By the zero–one law some `x ∈ X` has a
  finite modification `flipSet s x` in that set. Then `overwrite h (e x) (flipSet s x) ∈ K`.
* There are `𝔡` sets `W (g, k₀, s)`, because `𝔡` is infinite.

## Differences from the note

* The note fills the coordinates outside the range of `h` with a second point and uses the
  enumeration of the complement of the range. Here the code overwrites the coordinates in the
  range of `h` and the other coordinates are kept.
* The note uses Goto's Claim 5.5.1 on graphs to see that the sets are universally null. Here
  this is Lemma 3 applied to the map that reads the code.
* The note takes a set of full outer measure, by the Kolmogorov zero–one law. Here the family
  also ranges over the finite sets `s`, and `exists_flipSet_mem` replaces full outer measure.
* Lemma 4 of the note is replaced by `exists_levels`. The density step of the note is not
  needed, and the sum over the cylinders of the open set is replaced by the layers
  `layer U M k`.
-/

@[expose] public section

open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal

namespace AddUN

/-! ### Approximation of an open set from inside -/

/-- The points whose cylinder of length `n` is contained in `U`. -/
def inner (U : Set (ℕ → Bool)) (n : ℕ) : Set (ℕ → Bool) :=
  {x | cylinderOn (Finset.range n) x ⊆ U}

variable {U : Set (ℕ → Bool)}

lemma inner_subset (n : ℕ) : inner U n ⊆ U := fun _ hx ↦ hx fun _ _ ↦ rfl

lemma inner_mono {m n : ℕ} (h : m ≤ n) : inner U m ⊆ inner U n := fun _ hx _ hy ↦
  hx fun i hi ↦ hy i (Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) h))

lemma determined_inner (n : ℕ) : Determined (↑(Finset.range n)) (inner U n) :=
  fun _ _ h hw _ hy ↦ hw fun i hi ↦ (hy i hi).trans (h i hi).symm

lemma isOpen_inner (n : ℕ) : IsOpen (inner U n) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  exact ⟨cylinderOn (Finset.range n) x,
    fun y hy ↦ determined_inner n (fun i hi ↦ (hy i hi).symm) hx,
    (isClopen_cylinderOn _ _).isOpen, fun _ _ ↦ rfl⟩

lemma iUnion_inner (hU : IsOpen U) : ⋃ n, inner U n = U := by
  refine Subset.antisymm (iUnion_subset fun n ↦ inner_subset n) fun x hx ↦ ?_
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hU x hx
  refine mem_iUnion.2 ⟨I.sup id + 1, fun y hy ↦ hsub fun i hi ↦ ?_⟩
  rw [hy i (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)))]
  exact (hu i hi).2

/-- The layers of `U` along the levels `M`. -/
def layer (U : Set (ℕ → Bool)) (M : ℕ → ℕ) : ℕ → Set (ℕ → Bool)
  | 0 => inner U (M 0)
  | k + 1 => inner U (M (k + 1)) \ inner U (M k)

lemma measurableSet_layer (M : ℕ → ℕ) (k : ℕ) : MeasurableSet (layer U M k) := by
  cases k with
  | zero => exact (isOpen_inner _).measurableSet
  | succ k => exact (isOpen_inner _).measurableSet.diff (isOpen_inner _).measurableSet

lemma determined_layer {M : ℕ → ℕ} (hM : Monotone M) (k : ℕ) :
    Determined (↑(Finset.range (M k))) (layer U M k) := by
  cases k with
  | zero => exact determined_inner _
  | succ k =>
    exact (determined_inner _).diff ((determined_inner _).mono
      (Finset.coe_subset.2 (Finset.range_subset_range.2 (hM (Nat.le_succ k)))))

lemma exists_mem_layer (hU : IsOpen U) {M : ℕ → ℕ} (hM : StrictMono M) {y : ℕ → Bool}
    (hy : y ∈ U) : ∃ k, y ∈ layer U M k := by
  classical
  have hex : ∃ k, y ∈ inner U (M k) := by
    rw [← iUnion_inner hU] at hy
    obtain ⟨n, hn⟩ := mem_iUnion.1 hy
    exact ⟨n, inner_mono hM.le_apply hn⟩
  refine ⟨Nat.find hex, ?_⟩
  cases hk : Nat.find hex with
  | zero => simpa [layer, hk] using Nat.find_spec hex
  | succ k =>
    refine ⟨by simpa [hk] using Nat.find_spec hex, ?_⟩
    exact Nat.find_min hex (by omega)

/-! ### Sets whose modifications on a sparse set stay in a compact set -/

/-- For a compact set `K` of positive measure there is a sequence `M` of levels with this
property. If `M k ≤ h k` for all `k`, then some measurable set of positive measure consists of
points `u` such that every point that agrees with `u` outside the range of `h` lies in `K`. -/
theorem exists_levels {K : Set (ℕ → Bool)} (hK : IsCompact K) (hKpos : cantorMeasure K ≠ 0) :
    ∃ M : ℕ → ℕ, Monotone M ∧ ∀ h : ℕ → ℕ, (∀ k, M k ≤ h k) →
      ∃ Good : Set (ℕ → Bool), MeasurableSet Good ∧ cantorMeasure Good ≠ 0 ∧
        ∀ u ∈ Good, ∀ y : ℕ → Bool, (∀ i, i ∉ range h → y i = u i) → y ∈ K := by
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  -- The part of the complement of `K` outside `inner Kᶜ m` is small for large `m`.
  have htend : Tendsto (fun m ↦ cantorMeasure (Kᶜ \ inner Kᶜ m)) atTop (𝓝 0) := by
    have hlim := tendsto_measure_iInter_atTop (μ := cantorMeasure)
      (s := fun m ↦ Kᶜ \ inner Kᶜ m)
      (fun m ↦ (hU.measurableSet.diff (isOpen_inner m).measurableSet).nullMeasurableSet)
      (fun m n hmn ↦ sdiff_subset_sdiff_right (inner_mono hmn)) ⟨0, measure_ne_top _ _⟩
    have hempty : ⋂ m, Kᶜ \ inner Kᶜ m = ∅ := by
      rw [← sdiff_iUnion, iUnion_inner hU, sdiff_self]
    rwa [hempty, measure_empty] at hlim
  let δ : ℕ → ℝ≥0∞ := fun k ↦ cantorMeasure K / 2 * 2⁻¹ ^ (k + 1) / 2 ^ (k + 1)
  have hδ : ∀ k, 0 < δ k := fun k ↦
    ENNReal.div_pos (mul_ne_zero (ENNReal.div_pos hKpos (by simp)).ne' (by simp)) (by simp)
  obtain ⟨M, hM, hMδ⟩ :=
    extraction_forall_of_eventually fun k ↦ htend.eventually_le_const (hδ k)
  refine ⟨M, hM.monotone, fun h hh ↦ ?_⟩
  classical
  -- The points with a modification on the range of `h` outside `K` are covered by `Cover`.
  let Cover : Set (ℕ → Bool) :=
    ⋃ k, ⋃ s ∈ ((Finset.range k).image h).powerset, flipSet s ⁻¹' layer Kᶜ M k
  have hCm : MeasurableSet Cover :=
    .iUnion fun k ↦ Finset.measurableSet_biUnion _ fun s _ ↦
      (measurePreserving_flipSet s).measurable (measurableSet_layer M k)
  have hk : ∀ k, cantorMeasure
      (⋃ s ∈ ((Finset.range k).image h).powerset, flipSet s ⁻¹' layer Kᶜ M k) ≤
      2 ^ k * cantorMeasure (layer Kᶜ M k) := fun k ↦ by
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hpre : ∀ s : Finset ℕ, cantorMeasure (flipSet s ⁻¹' layer Kᶜ M k) =
        cantorMeasure (layer Kᶜ M k) := fun s ↦
      (measurePreserving_flipSet s).measure_preimage (measurableSet_layer M k).nullMeasurableSet
    simp_rw [hpre]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
    refine mul_le_mul_left ?_ _
    have hcard : ((Finset.range k).image h).card ≤ k :=
      Finset.card_image_le.trans (Finset.card_range k).le
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) hcard
  have hsucc : ∀ k, 2 ^ (k + 1) * cantorMeasure (layer Kᶜ M (k + 1)) ≤
      cantorMeasure K / 2 * 2⁻¹ ^ (k + 1) := fun k ↦
    ENNReal.mul_le_of_le_div' ((measure_mono (sdiff_subset_sdiff_left (inner_subset _))).trans
      (hMδ k))
  have hCover : cantorMeasure Cover ≤ cantorMeasure Kᶜ + cantorMeasure K / 2 := by
    calc cantorMeasure Cover
        ≤ ∑' k, 2 ^ k * cantorMeasure (layer Kᶜ M k) :=
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hk)
      _ = 2 ^ 0 * cantorMeasure (layer Kᶜ M 0) +
            ∑' k, 2 ^ (k + 1) * cantorMeasure (layer Kᶜ M (k + 1)) :=
          tsum_eq_zero_add' ENNReal.summable
      _ ≤ cantorMeasure Kᶜ + ∑' k : ℕ, cantorMeasure K / 2 * 2⁻¹ ^ (k + 1) := by
          refine add_le_add ?_ (ENNReal.tsum_le_tsum hsucc)
          rw [pow_zero, one_mul]
          exact measure_mono (inner_subset _)
      _ = cantorMeasure Kᶜ + cantorMeasure K / 2 := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two,
            inv_inv, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
  refine ⟨Coverᶜ, hCm.compl, fun h0 ↦ ?_, fun u hu y hy ↦ by_contra fun hyK ↦ ?_⟩
  · -- The cover has measure less than `1`.
    have h1 : cantorMeasure Cover = 1 := by
      have := measure_add_measure_compl (μ := cantorMeasure) hCm
      rwa [h0, add_zero, measure_univ] at this
    have h2 : cantorMeasure Kᶜ + cantorMeasure K = 1 := by
      rw [add_comm, measure_add_measure_compl hK.isClosed.measurableSet, measure_univ]
    rw [h1, ← h2] at hCover
    exact (ENNReal.half_lt_self hKpos (measure_ne_top _ _)).not_ge
      ((ENNReal.add_le_add_iff_left (measure_ne_top _ _)).1 hCover)
  · -- A modification outside `K` puts `u` in the cover.
    obtain ⟨k, hyk⟩ := exists_mem_layer hU hM (y := y) hyK
    have hagree : ∀ i ∈ (↑(Finset.range (M k)) : Set ℕ),
        y i = flipSet (((Finset.range k).image h).filter fun i ↦ y i ≠ u i) u i := by
      intro i hi
      by_cases hne : y i = u i
      · rw [flipSet_apply_of_notMem (by simp [hne]), hne]
      · have hir : i ∈ range h := by_contra fun hnr ↦ hne (hy i hnr)
        obtain ⟨j, rfl⟩ := hir
        have hjk : j < k := by
          by_contra hjk
          have h1 := (hM.monotone (not_lt.1 hjk)).trans (hh j)
          have h2 := Finset.mem_range.1 (Finset.mem_coe.1 hi)
          omega
        rw [flipSet_apply_of_mem (Finset.mem_filter.2
          ⟨Finset.mem_image.2 ⟨j, Finset.mem_range.2 hjk, rfl⟩, hne⟩)]
        cases hy1 : y (h j) <;> cases hu1 : u (h j) <;> simp_all
    exact hu (mem_iUnion.2 ⟨k, mem_iUnion₂.2 ⟨_, Finset.mem_powerset.2 (Finset.filter_subset _ _),
      determined_layer hM.monotone k hagree hyk⟩⟩)

/-! ### Writing a code on a sparse set of coordinates -/

/-- An injective map `h` with `g (k + k₀) ≤ h k`. -/
def spread (g : ℕ → ℕ) (k₀ k : ℕ) : ℕ := Nat.pair k (g (k + k₀))

lemma le_spread (g : ℕ → ℕ) (k₀ k : ℕ) : g (k + k₀) ≤ spread g k₀ k := Nat.right_le_pair _ _

/-- Write `c n` on the coordinate `h n` and keep `u` on the other coordinates. -/
def overwrite (h : ℕ → ℕ) (c u : ℕ → Bool) (i : ℕ) : Bool :=
  if h (Nat.unpair i).1 = i then c (Nat.unpair i).1 else u i

lemma overwrite_spread_apply (g : ℕ → ℕ) (k₀ : ℕ) (c u : ℕ → Bool) (n : ℕ) :
    overwrite (spread g k₀) c u (spread g k₀ n) = c n := by
  simp [overwrite, spread]

lemma overwrite_of_notMem_range {h : ℕ → ℕ} (c u : ℕ → Bool) {i : ℕ} (hi : i ∉ range h) :
    overwrite h c u i = u i := by
  unfold overwrite
  rw [if_neg fun heq ↦ hi ⟨_, heq⟩]

/-! ### The theorem -/

/-- Theorem A, from Grzegorek's theorem. -/
theorem theoremA_of_grzegorek (hG : Grzegorek) : TheoremA := by
  obtain ⟨P, hP, hPcard⟩ := hG
  obtain ⟨X, hX, hXcard⟩ := exists_notMem_mk_eq_non (I := 𝒩) ⟨univ, univ_notMem_null⟩
  have hXpos : cantorMeasure X ≠ 0 := hX
  obtain ⟨e⟩ : Nonempty (X ≃ P) := Cardinal.eq.1 (hXcard.trans hPcard.symm)
  -- A dominating family of cardinality `𝔡`.
  have hne : Nonempty {D : Set (ℕ → ℕ) // ∀ f, ∃ g ∈ D, f ≤ᶠ[atTop] g} :=
    ⟨⟨univ, fun f ↦ ⟨f, mem_univ f, EventuallyLE.refl _ _⟩⟩⟩
  obtain ⟨⟨D, hD⟩, hDcard⟩ :=
    ciInf_mem fun D : {D : Set (ℕ → ℕ) // ∀ f, ∃ g ∈ D, f ≤ᶠ[atTop] g} ↦ #D.1
  let W : D × ℕ × Finset ℕ → Set (ℕ → Bool) := fun π ↦
    range fun x : X ↦ overwrite (spread π.1 π.2.1) (e x) (flipSet π.2.2 x)
  -- Each set is universally null: reading the code is injective on it.
  have hW : ∀ π, IsUniversallyNull (W π) := fun π ↦ by
    have hread : ∀ x : X, (fun n ↦ overwrite (spread π.1 π.2.1) (e x) (flipSet π.2.2 x)
        (spread π.1 π.2.1 n)) = e x := fun x ↦ funext fun n ↦ overwrite_spread_apply _ _ _ _ n
    refine hP.of_injOn (φ := fun w n ↦ w (spread π.1 π.2.1 n))
      (measurable_pi_lambda _ fun n ↦ measurable_pi_apply _) ?_ ?_
    · rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ heq
      have hee : (e x : ℕ → Bool) = e x' := by
        rw [← hread x, ← hread x']
        exact heq
      rw [e.injective (Subtype.ext hee)]
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      change (fun n ↦ overwrite (spread π.1 π.2.1) (e x) (flipSet π.2.2 x)
        (spread π.1 π.2.1 n)) ∈ P
      rw [hread x]
      exact (e x).2
  -- The union is not null.
  have hUnion : ⋃₀ range W ∉ 𝒰𝒩 := by
    intro hUN
    obtain ⟨K, hK, hKpos, hKdisj⟩ :=
      exists_isCompact_disjoint_of_null (universallyNull_subset_null hUN)
    obtain ⟨M, hMmono, hM⟩ := exists_levels hK hKpos
    obtain ⟨g, hgD, hg⟩ := hD M
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hg
    obtain ⟨Good, hGm, hGpos, hGood⟩ := hM (spread g k₀) fun k ↦
      ((hMmono (Nat.le_add_right k k₀)).trans (hk₀ _ (Nat.le_add_left _ _))).trans
        (le_spread g k₀ k)
    obtain ⟨x, hx, s, hs⟩ := exists_flipSet_mem hXpos hGm hGpos
    have hmem : overwrite (spread g k₀) (e ⟨x, hx⟩) (flipSet s x) ∈ K :=
      hGood _ hs _ fun i hi ↦ overwrite_of_notMem_range _ _ hi
    exact disjoint_left.1 hKdisj hmem
      ⟨W (⟨g, hgD⟩, k₀, s), mem_range_self _, ⟨⟨x, hx⟩, rfl⟩⟩
  -- There are `𝔡` sets.
  have h1 : add 𝒰𝒩 ≤ #D * ℵ₀ := by
    refine ((add_le (by rintro _ ⟨π, rfl⟩; exact hW π) hUnion).trans mk_range_le).trans ?_
    simp [mk_eq_aleph0]
  have h3 : ℵ₀ ≤ #D := by
    by_contra hlt
    have h4 : #D * ℵ₀ ≤ ℵ₀ :=
      (mul_le_mul_left (not_le.1 hlt).le ℵ₀).trans aleph0_mul_aleph0.le
    exact (aleph0_lt_add_universallyNull.trans_le (h1.trans h4)).false
  rw [mul_aleph0_eq h3] at h1
  exact h1.trans hDcard.le

/-- **Theorem A.** `add 𝒰𝒩 ≤ 𝔡`. -/
theorem theoremA : TheoremA := theoremA_of_grzegorek grzegorek

end AddUN
