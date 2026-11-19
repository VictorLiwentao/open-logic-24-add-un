/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.SecondMoment
public import AddUN.TheoremB

/-!
# The coding lemma

This file proves `AddUN.CodingLemma`, which is Lemma 2 of `notes/partial-results.md`.

## The coding

Put `mu n = 4 ^ (n + 1)`. The block `block n k` has `mu n + n` coordinates `coord n k j`. The
blocks are pairwise disjoint. A point `w` has a *marker* at `(n, k)` if it is `false` on the
first `mu n` coordinates of the block. It *hits* `c` at `(n, k)` if it has a marker there and
its next `n` coordinates are `c 0, …, c (n - 1)`. The map `decode f` reads the bit `i` of the
code from the blocks `(n, f n)` with `n > i` that carry a marker.

## Differences from the note

The proof follows the note with three changes. None of them changes the statement.

* `decode f` is defined on the whole space, so no domain is needed.
* The slalom is `bad K c n`: the set of `k` such that the hit at `(n, k)` takes less than half
  of its share of `K ∩ E` for *some* event `E` that depends only on blocks of stages below `n`
  and has `K ∩ E` of measure at least `theta n`. The note uses only the events of its tree.
  The larger set has the same width bound, and its definition needs no recursion.
* The lower bound for the measure at stage `n` is `theta n = 4 * 2 ^ (-mu n)` in place of the
  tail sum `2 τ_{n-1}`. The point `w` is taken in the intersection of the sets `K ∩ branch m`,
  so the sets `Q_n` of the note are not needed.
-/

@[expose] public section

open Set Filter MeasureTheory

namespace AddUN

namespace Coding

/-! ### Blocks -/

/-- The number of marker coordinates of a block of stage `n`. -/
def mu (n : ℕ) : ℕ := 4 ^ (n + 1)

lemma mu_succ (n : ℕ) : mu (n + 1) = 4 * mu n := by
  simp only [mu, pow_succ]
  ring

lemma lt_mu (n : ℕ) : n < mu n :=
  (Nat.lt_pow_self (by norm_num)).trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n))

/-- The coordinate `j` of the block `(n, k)`. -/
def coord (n k j : ℕ) : ℕ := Nat.pair (Nat.pair n k) j

/-- The stage of the block that contains a coordinate. -/
def stage (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair i).1).1

@[simp]
lemma stage_coord (n k j : ℕ) : stage (coord n k j) = n := by simp [stage, coord]

lemma coord_inj {n k j n' k' j' : ℕ} :
    coord n k j = coord n' k' j' ↔ n = n' ∧ k = k' ∧ j = j' := by
  simp [coord, Nat.pair_eq_pair, and_assoc]

/-- The coordinates of the blocks of stages below `n`. -/
def low (n : ℕ) : Set ℕ := {i | stage i < n}

lemma low_mono {m n : ℕ} (h : m ≤ n) : low m ⊆ low n := fun _ hi ↦ lt_of_lt_of_le hi h

/-- The block `(n, k)`. -/
def block (n k : ℕ) : Finset ℕ := (Finset.range (mu n + n)).image (coord n k)

/-- The marker part of the block `(n, k)`. -/
def markerBlock (n k : ℕ) : Finset ℕ := (Finset.range (mu n)).image (coord n k)

lemma card_block (n k : ℕ) : (block n k).card = mu n + n := by
  rw [block, Finset.card_image_of_injective _ fun a b h ↦ (coord_inj.1 h).2.2, Finset.card_range]

lemma card_markerBlock (n k : ℕ) : (markerBlock n k).card = mu n := by
  rw [markerBlock, Finset.card_image_of_injective _ fun a b h ↦ (coord_inj.1 h).2.2,
    Finset.card_range]

lemma block_subset_low (n k : ℕ) : (block n k : Set ℕ) ⊆ low (n + 1) := by
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hi)
  simp [low]

lemma markerBlock_subset_block (n k : ℕ) : markerBlock n k ⊆ block n k :=
  Finset.image_subset_image (Finset.range_subset_range.2 (Nat.le_add_right _ _))

lemma disjoint_low_block (n k : ℕ) : Disjoint (low n) (block n k : Set ℕ) := by
  rw [Set.disjoint_left]
  intro i hi hb
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
  simp [low] at hi

lemma disjoint_block {n k k' : ℕ} (h : k ≠ k') : Disjoint (block n k) (block n k') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
  obtain ⟨j', -, h'⟩ := Finset.mem_image.1 hi'
  exact h (coord_inj.1 h').2.1.symm

/-! ### Markers and hits -/

/-- The values that a point must take on the blocks in order to hit `c`. -/
def pattern (c : ℕ → Bool) (i : ℕ) : Bool :=
  decide (mu (stage i) ≤ (Nat.unpair i).2) && c ((Nat.unpair i).2 - mu (stage i))

lemma pattern_coord_of_lt (c : ℕ → Bool) {n j : ℕ} (k : ℕ) (h : j < mu n) :
    pattern c (coord n k j) = false := by
  simp [pattern, coord, stage, h]

lemma pattern_coord_add (c : ℕ → Bool) (n k i : ℕ) : pattern c (coord n k (mu n + i)) = c i := by
  simp [pattern, coord, stage]

/-- The points with a marker at `(n, k)`. -/
def marker (n k : ℕ) : Set (ℕ → Bool) := cylinderOn (markerBlock n k) fun _ ↦ false

/-- The points that hit `c` at `(n, k)`. -/
def hit (c : ℕ → Bool) (n k : ℕ) : Set (ℕ → Bool) := cylinderOn (block n k) (pattern c)

lemma mem_marker {n k : ℕ} {w : ℕ → Bool} :
    w ∈ marker n k ↔ ∀ j < mu n, w (coord n k j) = false := by
  simp [marker, cylinderOn, markerBlock]

lemma mem_hit {c : ℕ → Bool} {n k : ℕ} {w : ℕ → Bool} :
    w ∈ hit c n k ↔ ∀ j < mu n + n, w (coord n k j) = pattern c (coord n k j) := by
  simp [hit, cylinderOn, block]

lemma hit_subset_marker (c : ℕ → Bool) (n k : ℕ) : hit c n k ⊆ marker n k := by
  intro w hw
  rw [mem_marker]
  intro j hj
  rw [mem_hit.1 hw j (by omega), pattern_coord_of_lt c k hj]

lemma apply_of_mem_hit {c : ℕ → Bool} {n k i : ℕ} {w : ℕ → Bool} (hw : w ∈ hit c n k)
    (hi : i < n) : w (coord n k (mu n + i)) = c i := by
  rw [mem_hit.1 hw _ (by omega), pattern_coord_add]

lemma isClopen_marker (n k : ℕ) : IsClopen (marker n k) := isClopen_cylinderOn _ _

lemma isClopen_hit (c : ℕ → Bool) (n k : ℕ) : IsClopen (hit c n k) := isClopen_cylinderOn _ _

lemma determined_marker (n k : ℕ) : Determined (low (n + 1)) (marker n k) :=
  determined_cylinderOn _ _
    ((Finset.coe_subset.2 (markerBlock_subset_block n k)).trans (block_subset_low n k))

lemma determined_hit (c : ℕ → Bool) (n k : ℕ) : Determined (low (n + 1)) (hit c n k) :=
  determined_cylinderOn _ _ (block_subset_low n k)

lemma real_marker (n k : ℕ) : cantorMeasure.real (marker n k) = (1 / 2) ^ mu n := by
  rw [marker, cantorMeasure_real_cylinderOn, card_markerBlock]

/-! ### The decoding map -/

open Classical in
/-- The decoding map. The bit `i` of `decode f w` is `true` if, for all large `n`, a marker of
`w` at `(n, f n)` is followed by a message whose bit `i` is `true`. -/
noncomputable def decode (f : ℕ → ℕ) (w : ℕ → Bool) (i : ℕ) : Bool :=
  decide (∀ᶠ n in atTop, i < n ∧ w ∈ marker n (f n) → w (coord n (f n) (mu n + i)) = true)

lemma measurable_decode (f : ℕ → ℕ) : Measurable (decode f) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_to_bool ?_
  have hset : (fun w ↦ decode f w i) ⁻¹' {true} = ⋃ N : ℕ, ⋂ n : ℕ, ⋂ _ : N ≤ n,
      {w | i < n ∧ w ∈ marker n (f n) → w (coord n (f n) (mu n + i)) = true} := by
    ext w
    simp [decode, eventually_atTop]
  rw [hset]
  refine .iUnion fun N ↦ .iInter fun n ↦ .iInter fun _ ↦ ?_
  by_cases hin : i < n
  · have h : {w : ℕ → Bool | i < n ∧ w ∈ marker n (f n) → w (coord n (f n) (mu n + i)) = true} =
        (marker n (f n))ᶜ ∪ {w | w (coord n (f n) (mu n + i)) = true} := by
      ext w
      simp [hin, imp_iff_not_or]
    rw [h]
    exact (isClopen_marker _ _).isOpen.measurableSet.compl.union
      (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
  · simp [hin]

/-! ### Arithmetic -/

/-- The lower bound for the measure of the sets of stage `n`. -/
noncomputable def theta (n : ℕ) : ℝ := 4 * (1 / 2) ^ mu n

lemma theta_pos (n : ℕ) : 0 < theta n := by
  unfold theta
  positivity

lemma theta_succ_add_le (n : ℕ) : theta (n + 1) + (1 / 2) ^ mu n ≤ theta n := by
  unfold theta
  rw [mu_succ, pow_mul']
  have hx0 : (0 : ℝ) < (1 / 2) ^ mu n := by positivity
  have hx1 : ((1 : ℝ) / 2) ^ mu n ≤ 1 / 2 := by
    calc ((1 : ℝ) / 2) ^ mu n ≤ (1 / 2) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.one_le_of_lt (lt_mu n))
      _ = 1 / 2 := by norm_num
  have h3 : (((1 : ℝ) / 2) ^ mu n) ^ 3 ≤ 1 / 8 := by
    calc (((1 : ℝ) / 2) ^ mu n) ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hx0.le hx1 3
      _ = 1 / 8 := by norm_num
  nlinarith [mul_le_mul_of_nonneg_left h3 hx0.le]

lemma theta_succ_le (n : ℕ) : theta (n + 1) ≤ (1 / 2) ^ (mu n + n) / 2 * theta n := by
  unfold theta
  have h1 : ((1 : ℝ) / 2) ^ mu (n + 1) ≤ (1 / 2) ^ (mu n + n + mu n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by
      rw [mu_succ]
      have := lt_mu n
      omega)
  rw [pow_succ, pow_add] at h1
  linarith

/-! ### The slalom -/

/-- The slalom for `K` and `c`. A number `k` is in `bad K c n` if, for some event `E` that
depends only on the blocks of stages below `n` and has `K ∩ E` of measure at least `theta n`,
the hit at `(n, k)` takes less than half of its share of `K ∩ E`. -/
def bad (K : Set (ℕ → Bool)) (c : ℕ → Bool) (n : ℕ) : Set ℕ :=
  {k | ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ Determined (low n) E ∧
    theta n ≤ cantorMeasure.real (K ∩ E) ∧
    cantorMeasure.real (K ∩ E ∩ hit c n k) <
      (1 / 2) ^ (mu n + n) / 2 * cantorMeasure.real (K ∩ E)}

/-- The width of the slalom. -/
lemma card_le_of_subset_bad {K : Set (ℕ → Bool)} (hK : MeasurableSet K) {c : ℕ → Bool} {n : ℕ}
    (J : Finset ℕ) (hJ : (J : Set ℕ) ⊆ bad K c n) : J.card ≤ 2 ^ (3 * mu n + n) := by
  have hex : ∀ k, ∃ E : Set (ℕ → Bool), k ∈ J → MeasurableSet E ∧ Determined (low n) E ∧
      theta n ≤ cantorMeasure.real (K ∩ E) ∧
      cantorMeasure.real (K ∩ E ∩ hit c n k) <
        (1 / 2) ^ (mu n + n) / 2 * cantorMeasure.real (K ∩ E) := fun k ↦ by
    by_cases hk : k ∈ J
    · obtain ⟨E, hE⟩ := hJ hk
      exact ⟨E, fun _ ↦ hE⟩
    · exact ⟨univ, fun h ↦ absurd h hk⟩
  choose E hE using hex
  have key := second_moment hK J E (fun k ↦ block n k) (pattern c) (mu n + n) (low n)
    (theta_pos n) (fun k hk ↦ (hE k hk).1) (fun k hk ↦ (hE k hk).2.1)
    (fun k _ ↦ disjoint_low_block n k) (fun k _ k' _ h ↦ disjoint_block h)
    (fun k _ ↦ card_block n k) (fun k hk ↦ (hE k hk).2.2.1) (fun k hk ↦ (hE k hk).2.2.2.le)
  have e : ((1 : ℝ) / 2) ^ (mu n + n) * theta n ^ 2 = 16 * (1 / 2) ^ (3 * mu n + n) := by
    unfold theta
    rw [mul_pow, ← pow_mul, show 3 * mu n + n = mu n + n + mu n * 2 by ring, pow_add (1 / 2 : ℝ)]
    ring
  rw [mul_assoc, e] at key
  have hk2 : ((1 : ℝ) / 2) ^ (3 * mu n + n) * 2 ^ (3 * mu n + n) = 1 := by
    rw [← mul_pow]
    norm_num
  have hpos : (0 : ℝ) < 2 ^ (3 * mu n + n) := by positivity
  have hle : (J.card : ℝ) ≤ 2 ^ (3 * mu n + n) := by
    calc (J.card : ℝ) = J.card * (1 / 2) ^ (3 * mu n + n) * 2 ^ (3 * mu n + n) := by
          rw [mul_assoc, hk2, mul_one]
      _ ≤ 1 / 4 * 2 ^ (3 * mu n + n) := mul_le_mul_of_nonneg_right (by linarith) hpos.le
      _ ≤ 2 ^ (3 * mu n + n) := by linarith
  exact_mod_cast hle

lemma finite_bad {K : Set (ℕ → Bool)} (hK : MeasurableSet K) (c : ℕ → Bool) (n : ℕ) :
    (bad K c n).Finite := by
  by_contra hinf
  obtain ⟨J, hJ, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (2 ^ (3 * mu n + n) + 1)
  have := card_le_of_subset_bad hK J hJ
  omega

/-! ### The branch of a function -/

open Classical in
/-- The events along the branch of `f`, from the stage `n₀` on. At the stage `n₀ + m` the event
is intersected with the hit at `(n₀ + m, f (n₀ + m))` if `f (n₀ + m)` is not in the slalom. If
it is in the slalom, the points with a marker and no hit are removed. -/
noncomputable def branch (K : Set (ℕ → Bool)) (c : ℕ → Bool) (f : ℕ → ℕ) (n₀ : ℕ) :
    ℕ → Set (ℕ → Bool)
  | 0 => univ
  | m + 1 =>
    if f (n₀ + m) ∈ bad K c (n₀ + m) then
      branch K c f n₀ m \ (marker (n₀ + m) (f (n₀ + m)) \ hit c (n₀ + m) (f (n₀ + m)))
    else branch K c f n₀ m ∩ hit c (n₀ + m) (f (n₀ + m))

variable {K : Set (ℕ → Bool)} {c : ℕ → Bool} {f : ℕ → ℕ} {n₀ : ℕ}

lemma branch_succ_of_mem {m : ℕ} (h : f (n₀ + m) ∈ bad K c (n₀ + m)) :
    branch K c f n₀ (m + 1) =
      branch K c f n₀ m \ (marker (n₀ + m) (f (n₀ + m)) \ hit c (n₀ + m) (f (n₀ + m))) := by
  rw [branch, if_pos h]

lemma branch_succ_of_notMem {m : ℕ} (h : f (n₀ + m) ∉ bad K c (n₀ + m)) :
    branch K c f n₀ (m + 1) = branch K c f n₀ m ∩ hit c (n₀ + m) (f (n₀ + m)) := by
  rw [branch, if_neg h]

lemma branch_succ_subset (m : ℕ) : branch K c f n₀ (m + 1) ⊆ branch K c f n₀ m := by
  by_cases h : f (n₀ + m) ∈ bad K c (n₀ + m)
  · rw [branch_succ_of_mem h]
    exact sdiff_subset
  · rw [branch_succ_of_notMem h]
    exact inter_subset_left

/-- The invariant of the fusion: the events of the branch are closed, depend only on the blocks
of lower stages, and meet `K` in a set of measure at least `theta`. -/
lemma branch_spec (hn₀ : theta n₀ ≤ cantorMeasure.real K) (m : ℕ) :
    IsClosed (branch K c f n₀ m) ∧ Determined (low (n₀ + m)) (branch K c f n₀ m) ∧
      theta (n₀ + m) ≤ cantorMeasure.real (K ∩ branch K c f n₀ m) := by
  induction m with
  | zero => exact ⟨isClosed_univ, Determined.univ, by simpa [branch] using hn₀⟩
  | succ m ih =>
    obtain ⟨hc, hd, hθ⟩ := ih
    have hd' : Determined (low (n₀ + m + 1)) (branch K c f n₀ m) :=
      hd.mono (low_mono (Nat.le_succ _))
    by_cases hb : f (n₀ + m) ∈ bad K c (n₀ + m)
    · rw [branch_succ_of_mem hb]
      refine ⟨hc.sdiff ((isClopen_marker _ _).diff (isClopen_hit _ _ _)).isOpen,
        hd'.diff ((determined_marker _ _).diff (determined_hit _ _ _)), ?_⟩
      have hsub : K ∩ branch K c f n₀ m ⊆
          K ∩ (branch K c f n₀ m \ (marker (n₀ + m) (f (n₀ + m)) \
            hit c (n₀ + m) (f (n₀ + m)))) ∪ marker (n₀ + m) (f (n₀ + m)) := by
        intro w hw
        by_cases hA : w ∈ marker (n₀ + m) (f (n₀ + m)) \ hit c (n₀ + m) (f (n₀ + m))
        · exact Or.inr hA.1
        · exact Or.inl ⟨hw.1, hw.2, hA⟩
      have h1 := (measureReal_mono (μ := cantorMeasure) hsub).trans (measureReal_union_le _ _)
      rw [real_marker] at h1
      have h2 := theta_succ_add_le (n₀ + m)
      change theta (n₀ + m + 1) ≤ _
      linarith
    · rw [branch_succ_of_notMem hb]
      refine ⟨hc.inter (isClopen_hit _ _ _).isClosed, hd'.inter (determined_hit _ _ _), ?_⟩
      have hnb : (1 / 2) ^ (mu (n₀ + m) + (n₀ + m)) / 2 *
          cantorMeasure.real (K ∩ branch K c f n₀ m) ≤
          cantorMeasure.real (K ∩ branch K c f n₀ m ∩ hit c (n₀ + m) (f (n₀ + m))) :=
        not_lt.1 fun h ↦ hb ⟨_, hc.measurableSet, hd, hθ, h⟩
      rw [← inter_assoc]
      change theta (n₀ + m + 1) ≤ _
      refine (theta_succ_le (n₀ + m)).trans (le_trans ?_ hnb)
      exact mul_le_mul_of_nonneg_left hθ (by positivity)

end Coding

open Coding

/-- The coding lemma for the map `decode` and the width `2 ^ (3 * mu n + n)`. -/
theorem exists_slalom_decode {K : Set (ℕ → Bool)} (hK : IsCompact K) (hKpos : cantorMeasure K ≠ 0)
    (c : ℕ → Bool) :
    ∃ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ 2 ^ (3 * mu n + n)) ∧
      ∀ f : ℕ → ℕ, (∃ᶠ n in atTop, f n ∉ S n) → ∃ w ∈ K, decode f w = c := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine ⟨fun n ↦ (finite_bad hKm c n).toFinset,
    fun n ↦ card_le_of_subset_bad hKm (c := c) (n := n) _ (by simp), fun f hf ↦ ?_⟩
  have hf' : ∃ᶠ n in atTop, f n ∉ bad K c n := hf.mono fun n hn ↦ by simpa using hn
  -- The first stage.
  have hKr : 0 < cantorMeasure.real K := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hKpos (measure_ne_top _ _)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, theta n₀ ≤ cantorMeasure.real K := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < cantorMeasure.real K / 4 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have h1 : ((1 : ℝ) / 2) ^ mu n ≤ (1 / 2) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (lt_mu n).le
    refine ⟨n, ?_⟩
    unfold theta
    linarith
  have hspec := fun m ↦ branch_spec (c := c) (f := f) hn₀ m
  -- A point in every set of the branch.
  obtain ⟨w, hw⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun m ↦ K ∩ branch K c f n₀ m)
    (fun m ↦ inter_subset_inter_right K (branch_succ_subset m))
    (fun m ↦ by
      by_contra hem
      have h0 := (hspec m).2.2
      rw [not_nonempty_iff_eq_empty.1 hem, measureReal_empty] at h0
      exact absurd (theta_pos (n₀ + m)) (not_lt.2 h0))
    (by simpa [branch] using hK) (fun m ↦ hK.isClosed.inter (hspec m).1)
  rw [mem_iInter] at hw
  refine ⟨w, (hw 0).1, ?_⟩
  -- From the stage `n₀` on, every marker of `w` on the branch is followed by the code.
  have h1 : ∀ m, w ∈ marker (n₀ + m) (f (n₀ + m)) → w ∈ hit c (n₀ + m) (f (n₀ + m)) := by
    intro m hmark
    have hm := (hw (m + 1)).2
    by_cases hb : f (n₀ + m) ∈ bad K c (n₀ + m)
    · rw [branch_succ_of_mem hb] at hm
      by_contra hhit
      exact hm.2 ⟨hmark, hhit⟩
    · rw [branch_succ_of_notMem hb] at hm
      exact hm.2
  have h2 : ∀ m, f (n₀ + m) ∉ bad K c (n₀ + m) → w ∈ hit c (n₀ + m) (f (n₀ + m)) := by
    intro m hb
    have hm := (hw (m + 1)).2
    rw [branch_succ_of_notMem hb] at hm
    exact hm.2
  ext i
  unfold decode
  cases hci : c i
  · rw [decide_eq_false_iff_not]
    intro hev
    obtain ⟨n, ⟨hnb, hn⟩, hnev⟩ :=
      ((hf'.and_eventually (eventually_ge_atTop (max n₀ (i + 1)))).and_eventually hev).exists
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (le_of_max_le_left hn)
    have hin : i < n₀ + m := le_of_max_le_right hn
    have hhit := h2 m hnb
    have := hnev ⟨hin, hit_subset_marker _ _ _ hhit⟩
    rw [apply_of_mem_hit hhit hin, hci] at this
    exact Bool.false_ne_true this
  · simp only [decide_eq_true_eq]
    filter_upwards [eventually_ge_atTop n₀] with n hn hmark
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [apply_of_mem_hit (h1 m hmark.2) hmark.1, hci]

/-- **Lemma 2 (the coding lemma).** -/
theorem codingLemma : CodingLemma :=
  ⟨fun n ↦ 2 ^ (3 * mu n + n), decode, measurable_decode, fun _ hK hKpos c ↦
    exists_slalom_decode hK hKpos c⟩

end AddUN
