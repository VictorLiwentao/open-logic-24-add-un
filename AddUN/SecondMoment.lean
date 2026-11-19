/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.CantorMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A second-moment bound for the coin-tossing measure

This file proves the counting step of the coding lemma (Lemma 2 of
`notes/partial-results.md`, paragraph "Width").

Let `K` be a measurable set. For each `k` in a finite set `J` let `E k` be an event and `R k` a
cylinder on a block `B k` of `L` coordinates. The blocks are pairwise disjoint and no `E k`
depends on a coordinate in a block. Suppose that every `K ∩ E k` has measure at least `θ` and
that `R k` takes less than half of its share `2⁻ᴸ` of `K ∩ E k`. Then `J` has at most
`4 / (2⁻ᴸ θ²)` elements. This is `second_moment`.
-/

@[expose] public section

open Set MeasureTheory

namespace MeasureTheory

/-- Real-valued form of `cantorMeasure_inter_cylinder`. -/
lemma cantorMeasure_real_inter_cylinderOn {E : Set (ℕ → Bool)} (B : Finset ℕ) (v : ℕ → Bool)
    (hE : Determined (↑B)ᶜ E) :
    cantorMeasure.real (E ∩ cylinderOn B v) = cantorMeasure.real E * (1 / 2) ^ B.card := by
  simp [measureReal_def, cantorMeasure_inter_cylinder B v hE, ENNReal.toReal_mul]

/-- Real-valued form of `cantorMeasure_cylinderOn`. -/
lemma cantorMeasure_real_cylinderOn (B : Finset ℕ) (v : ℕ → Bool) :
    cantorMeasure.real (cylinderOn B v) = (1 / 2) ^ B.card := by
  simp [measureReal_def, cantorMeasure_cylinderOn B v]

/-- The indicator function of a set, with real values. -/
noncomputable def ind (S : Set (ℕ → Bool)) (w : ℕ → Bool) : ℝ := S.indicator (fun _ ↦ 1) w

lemma integrable_ind {S : Set (ℕ → Bool)} (hS : MeasurableSet S) :
    Integrable (ind S) cantorMeasure :=
  (integrable_const (1 : ℝ)).indicator hS

lemma integral_ind {S : Set (ℕ → Bool)} (hS : MeasurableSet S) :
    ∫ w, ind S w ∂cantorMeasure = cantorMeasure.real S := by
  simpa [ind] using integral_indicator_const (μ := cantorMeasure) (1 : ℝ) hS

/-- The integral of a product of two functions of the form `ρ 1_E - 1_{E ∩ R}`. -/
lemma integral_mul_aux {E E' R R' : Set (ℕ → Bool)} (hE : MeasurableSet E)
    (hE' : MeasurableSet E') (hR : MeasurableSet R) (hR' : MeasurableSet R') (ρ : ℝ) :
    Integrable (fun w ↦ (ρ * ind E w - ind (E ∩ R) w) * (ρ * ind E' w - ind (E' ∩ R') w))
        cantorMeasure ∧
      ∫ w, (ρ * ind E w - ind (E ∩ R) w) * (ρ * ind E' w - ind (E' ∩ R') w) ∂cantorMeasure =
        ρ ^ 2 * cantorMeasure.real (E ∩ E') - ρ * cantorMeasure.real (E ∩ E' ∩ R') -
          ρ * cantorMeasure.real (E ∩ E' ∩ R) + cantorMeasure.real (E ∩ E' ∩ R ∩ R') := by
  have hfun : (fun w ↦ (ρ * ind E w - ind (E ∩ R) w) * (ρ * ind E' w - ind (E' ∩ R') w)) =
      fun w ↦ ρ ^ 2 * ind (E ∩ E') w - ρ * ind (E ∩ E' ∩ R') w - ρ * ind (E ∩ E' ∩ R) w +
        ind (E ∩ E' ∩ R ∩ R') w := by
    funext w
    by_cases h1 : w ∈ E <;> by_cases h2 : w ∈ E' <;> by_cases h3 : w ∈ R <;>
      by_cases h4 : w ∈ R' <;> simp [ind, h1, h2, h3, h4] <;> ring
  have i1 := (integrable_ind (hE.inter hE')).const_mul (ρ ^ 2)
  have i2 := (integrable_ind ((hE.inter hE').inter hR')).const_mul ρ
  have i3 := (integrable_ind ((hE.inter hE').inter hR)).const_mul ρ
  have i4 := integrable_ind (((hE.inter hE').inter hR).inter hR')
  rw [hfun]
  refine ⟨((i1.sub i2).sub i3).add i4, ?_⟩
  rw [integral_add (f := fun w ↦ ρ ^ 2 * ind (E ∩ E') w - ρ * ind (E ∩ E' ∩ R') w -
      ρ * ind (E ∩ E' ∩ R) w) ((i1.sub i2).sub i3) i4,
    integral_sub (f := fun w ↦ ρ ^ 2 * ind (E ∩ E') w - ρ * ind (E ∩ E' ∩ R') w) (i1.sub i2) i3,
    integral_sub i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_ind (hE.inter hE'),
    integral_ind ((hE.inter hE').inter hR'), integral_ind ((hE.inter hE').inter hR),
    integral_ind (((hE.inter hE').inter hR).inter hR')]

/-- **The second-moment bound.** See the module docstring. -/
theorem second_moment {K : Set (ℕ → Bool)} (hK : MeasurableSet K) (J : Finset ℕ)
    (E : ℕ → Set (ℕ → Bool)) (B : ℕ → Finset ℕ) (v : ℕ → Bool) (L : ℕ) (s : Set ℕ) {θ : ℝ}
    (hθ : 0 < θ) (hE : ∀ k ∈ J, MeasurableSet (E k)) (hdet : ∀ k ∈ J, Determined s (E k))
    (hs : ∀ k ∈ J, Disjoint s (B k : Set ℕ))
    (hB : ∀ k ∈ J, ∀ k' ∈ J, k ≠ k' → Disjoint (B k) (B k')) (hL : ∀ k ∈ J, (B k).card = L)
    (hθK : ∀ k ∈ J, θ ≤ cantorMeasure.real (K ∩ E k))
    (hbad : ∀ k ∈ J, cantorMeasure.real (K ∩ E k ∩ cylinderOn (B k) v) ≤
      (1 / 2) ^ L / 2 * cantorMeasure.real (K ∩ E k)) :
    (J.card : ℝ) * (1 / 2) ^ L * θ ^ 2 ≤ 4 := by
  set ρ : ℝ := (1 / 2) ^ L with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  let R : ℕ → Set (ℕ → Bool) := fun k ↦ cylinderOn (B k) v
  have hR : ∀ k, MeasurableSet (R k) := fun k ↦ measurableSet_cylinderOn _ _
  let ξ : ℕ → (ℕ → Bool) → ℝ := fun k w ↦ ρ * ind (E k) w - ind (E k ∩ R k) w
  let ζ : ℕ → (ℕ → Bool) → ℝ := fun k w ↦ ρ * ind (K ∩ E k) w - ind (K ∩ E k ∩ R k) w
  -- The integral of `ζ k`.
  have hζi : ∀ k ∈ J, Integrable (ζ k) cantorMeasure := fun k hk ↦
    ((integrable_ind (hK.inter (hE k hk))).const_mul ρ).sub
      (integrable_ind ((hK.inter (hE k hk)).inter (hR k)))
  have hζ : ∀ k ∈ J, ∫ w, ζ k w ∂cantorMeasure =
      ρ * cantorMeasure.real (K ∩ E k) - cantorMeasure.real (K ∩ E k ∩ R k) := fun k hk ↦ by
    simp only [ζ]
    rw [integral_sub ((integrable_ind (hK.inter (hE k hk))).const_mul ρ)
      (integrable_ind ((hK.inter (hE k hk)).inter (hR k))), integral_const_mul,
      integral_ind (hK.inter (hE k hk)), integral_ind ((hK.inter (hE k hk)).inter (hR k))]
  -- The products `ξ k * ξ k'`: the cross terms vanish by independence.
  have hint : ∀ k ∈ J, ∀ k' ∈ J, Integrable (fun w ↦ ξ k w * ξ k' w) cantorMeasure :=
    fun k hk k' hk' ↦ (integral_mul_aux (hE k hk) (hE k' hk') (hR k) (hR k') ρ).1
  have hcross : ∀ k ∈ J, ∀ k' ∈ J, k ≠ k' → ∫ w, ξ k w * ξ k' w ∂cantorMeasure = 0 := by
    intro k hk k' hk' hne
    have hd : Determined s (E k ∩ E k') := (hdet k hk).inter (hdet k' hk')
    have i1 : cantorMeasure.real (E k ∩ E k' ∩ R k') = cantorMeasure.real (E k ∩ E k') * ρ := by
      rw [cantorMeasure_real_inter_cylinderOn (B k') v
        (hd.mono (hs k' hk').subset_compl_right), hL k' hk']
    have i2 : cantorMeasure.real (E k ∩ E k' ∩ R k) = cantorMeasure.real (E k ∩ E k') * ρ := by
      rw [cantorMeasure_real_inter_cylinderOn (B k) v
        (hd.mono (hs k hk).subset_compl_right), hL k hk]
    have i3 : cantorMeasure.real (E k ∩ E k' ∩ R k ∩ R k') =
        cantorMeasure.real (E k ∩ E k' ∩ R k) * ρ := by
      rw [cantorMeasure_real_inter_cylinderOn (B k') v
        ((hd.mono (hs k' hk').subset_compl_right).inter (determined_cylinderOn (B k) v
          (Finset.disjoint_coe.2 (hB k hk k' hk' hne)).subset_compl_right)), hL k' hk']
    rw [(integral_mul_aux (hE k hk) (hE k' hk') (hR k) (hR k') ρ).2, i3, i2, i1]
    ring
  have hdiag : ∀ k ∈ J, ∫ w, ξ k w * ξ k w ∂cantorMeasure ≤ ρ := by
    intro k hk
    have i1 : cantorMeasure.real (E k ∩ R k) = cantorMeasure.real (E k) * ρ := by
      rw [cantorMeasure_real_inter_cylinderOn (B k) v
        ((hdet k hk).mono (hs k hk).subset_compl_right), hL k hk]
    have hq0 : 0 ≤ cantorMeasure.real (E k) := measureReal_nonneg
    have hq1 : cantorMeasure.real (E k) ≤ 1 := measureReal_le_one
    rw [(integral_mul_aux (hE k hk) (hE k hk) (hR k) (hR k) ρ).2, inter_self, inter_assoc (E k),
      inter_self, i1]
    nlinarith [mul_nonneg hρ0 (sub_nonneg.2 hq1), mul_nonneg (mul_nonneg hq0 hρ0) hρ0]
  -- The second moment of the sum.
  have hsq : ∀ w, (∑ k ∈ J, ξ k w) ^ 2 = ∑ k ∈ J, ∑ k' ∈ J, ξ k w * ξ k' w := fun w ↦ by
    rw [sq, Finset.sum_mul_sum]
  have hsqi : Integrable (fun w ↦ (∑ k ∈ J, ξ k w) ^ 2) cantorMeasure := by
    simp_rw [hsq]
    exact integrable_finsetSum _ fun k hk ↦ integrable_finsetSum _ fun k' hk' ↦ hint k hk k' hk'
  have hmom : ∫ w, (∑ k ∈ J, ξ k w) ^ 2 ∂cantorMeasure ≤ J.card * ρ := by
    simp_rw [hsq]
    rw [integral_finsetSum _ fun k hk ↦ integrable_finsetSum _ fun k' hk' ↦ hint k hk k' hk']
    calc ∑ k ∈ J, ∫ w, ∑ k' ∈ J, ξ k w * ξ k' w ∂cantorMeasure
        = ∑ k ∈ J, ∫ w, ξ k w * ξ k w ∂cantorMeasure := Finset.sum_congr rfl fun k hk ↦ by
          rw [integral_finsetSum _ fun k' hk' ↦ hint k hk k' hk',
            Finset.sum_eq_single k (fun k' hk' hne ↦ hcross k hk k' hk' hne.symm)
              (fun h ↦ absurd hk h)]
      _ ≤ ∑ _k ∈ J, ρ := Finset.sum_le_sum hdiag
      _ = J.card * ρ := by simp
  -- A pointwise bound, integrated.
  have ht : 0 < 2 / θ := by positivity
  have hpt : ∀ w, ∑ k ∈ J, ζ k w ≤ 2 / θ / 2 + (∑ k ∈ J, ξ k w) ^ 2 / (2 * (2 / θ)) := by
    intro w
    by_cases hw : w ∈ K
    · have e : ∀ k, ζ k w = ξ k w := fun k ↦ by
        by_cases h1 : w ∈ E k <;> by_cases h2 : w ∈ R k <;> simp [ζ, ξ, ind, hw, h1, h2]
      simp_rw [e]
      have h0 : 0 ≤ (∑ k ∈ J, ξ k w - 2 / θ) ^ 2 / (2 * (2 / θ)) := by positivity
      have e2 : (∑ k ∈ J, ξ k w - 2 / θ) ^ 2 / (2 * (2 / θ)) =
          2 / θ / 2 + (∑ k ∈ J, ξ k w) ^ 2 / (2 * (2 / θ)) - ∑ k ∈ J, ξ k w := by
        field_simp
        ring
      linarith
    · have e : ∀ k, ζ k w = 0 := fun k ↦ by
        simp [ζ, ind, hw]
      simp_rw [e]
      simp only [Finset.sum_const_zero]
      positivity
  have hgi : Integrable (fun w ↦ 2 / θ / 2 + (∑ k ∈ J, ξ k w) ^ 2 / (2 * (2 / θ)))
      cantorMeasure := (integrable_const (2 / θ / 2)).add (hsqi.div_const (2 * (2 / θ)))
  have hmono := integral_mono (integrable_finsetSum _ hζi) hgi hpt
  rw [integral_finsetSum _ hζi, integral_add (f := fun _ ↦ 2 / θ / 2)
    (g := fun w ↦ (∑ k ∈ J, ξ k w) ^ 2 / (2 * (2 / θ))) (integrable_const _)
    (hsqi.div_const _), integral_const, integral_div] at hmono
  have hlow : (J.card : ℝ) * (ρ / 2 * θ) ≤ ∑ k ∈ J, ∫ w, ζ k w ∂cantorMeasure := by
    calc (J.card : ℝ) * (ρ / 2 * θ) = ∑ _k ∈ J, ρ / 2 * θ := by simp
      _ ≤ ∑ k ∈ J, ∫ w, ζ k w ∂cantorMeasure := Finset.sum_le_sum fun k hk ↦ by
        rw [hζ k hk]
        have h1 := hbad k hk
        have h2 : ρ / 2 * θ ≤ ρ / 2 * cantorMeasure.real (K ∩ E k) :=
          mul_le_mul_of_nonneg_left (hθK k hk) (by positivity)
        linarith
  have h5 : (∫ w, (∑ k ∈ J, ξ k w) ^ 2 ∂cantorMeasure) / (2 * (2 / θ)) ≤
      J.card * ρ / (2 * (2 / θ)) := div_le_div_of_nonneg_right hmom (by positivity)
  have h6 : 2 / θ / 2 = 1 / θ := by field_simp
  have h7 : (J.card : ℝ) * ρ / (2 * (2 / θ)) = J.card * ρ * θ / 4 := by
    field_simp
    ring
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  have h8 : (J.card : ℝ) * ρ * θ / 4 ≤ 1 / θ := by linarith
  rw [le_div_iff₀ hθ] at h8
  linarith
end MeasureTheory
