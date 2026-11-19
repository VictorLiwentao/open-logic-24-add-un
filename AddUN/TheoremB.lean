/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.Localisation
public import AddUN.Transfer

/-!
# Theorem B from the coding lemma

This file proves the hard direction of Theorem B of `notes/partial-results.md`,
`add 𝒰𝒩 ≤ add 𝒩`, from the coding lemma (Lemma 2 of the note). The coding lemma is the
hypothesis `CodingLemma`.

The proof follows the section "Proof of Theorem B" of the note. Take a cofinal family `𝒞` of
null sets of size `cof 𝒩` and list the given universally null set `A` as `e G`, `G ∈ 𝒞`,
without repetition. For each `G ∈ 𝒞` choose a compact set `K` of positive measure disjoint
from `G`. The coding lemma for `K` and the code `e G`, together with Lemma 1, gives a function
`f G` in a family `F` of size at most `add 𝒩` and a point `w G ∈ K` with `φ (f G) (w G) = e G`.
For `g ∈ F` the set `{w G | f G = g}` is mapped injectively into `A` by `φ g`, so it is
universally null by Lemma 3. The union of these sets meets the complement of every `G ∈ 𝒞`,
so it is not null.

In `CodingLemma` each map `φ f` is measurable on the whole space. The note uses a Borel map on
a Borel domain. The two forms give the same proof, because Lemma 3 holds for both.
-/

@[expose] public section

open Set Filter Cardinal MeasureTheory IdealInvariant

namespace AddUN

/-- **The coding lemma** (Lemma 2 of `notes/partial-results.md`). There are a width `h` and
measurable maps `φ f` of the Cantor space, one for each `f : ℕ → ℕ`, such that for every
compact set `K` of positive measure and every point `c` there is a slalom `S` of width `h` with
this property: if `f n ∉ S n` for infinitely many `n`, then `φ f w = c` for some `w ∈ K`. -/
def CodingLemma : Prop :=
  ∃ (h : ℕ → ℕ) (φ : (ℕ → ℕ) → (ℕ → Bool) → (ℕ → Bool)),
    (∀ f, Measurable (φ f)) ∧
      ∀ K : Set (ℕ → Bool), IsCompact K → cantorMeasure K ≠ 0 → ∀ c : ℕ → Bool,
        ∃ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ h n) ∧
          ∀ f : ℕ → ℕ, (∃ᶠ n in atTop, f n ∉ S n) → ∃ w ∈ K, φ f w = c

/-- The hard direction of Theorem B, from the coding lemma: if there is a universally null set
of cardinality `cof 𝒩`, then `add 𝒰𝒩 ≤ add 𝒩`. -/
theorem add_universallyNull_le_add_null_of_codingLemma (hC : CodingLemma)
    (A : Set (ℕ → Bool)) (hA : IsUniversallyNull A) (hcard : #A = cof 𝒩) :
    add 𝒰𝒩 ≤ add 𝒩 := by
  obtain ⟨h, φ, hφ, hcode⟩ := hC
  obtain ⟨F, hF, hloc⟩ := exists_unlocalised_family h
  obtain ⟨𝒞, h𝒞, hcof, h𝒞card⟩ := exists_cofinal_mk_eq_cof 𝒩
  obtain ⟨e⟩ : Nonempty (𝒞 ≃ A) := Cardinal.eq.1 (h𝒞card.trans hcard.symm)
  -- For each `G ∈ 𝒞` choose `f G ∈ F` and a point `w G ∉ G` that `φ (f G)` sends to `e G`.
  have key : ∀ G : 𝒞, ∃ f ∈ F, ∃ w : ℕ → Bool, w ∉ G.1 ∧ φ f w = e G := fun G ↦ by
    obtain ⟨K, hK, hKpos, hKG⟩ := exists_isCompact_disjoint_of_null (h𝒞 G.2)
    obtain ⟨S, hS, hSf⟩ := hcode K hK hKpos (e G)
    obtain ⟨f, hfF, hf⟩ := hloc S hS
    obtain ⟨w, hwK, hw⟩ := hSf f hf
    exact ⟨f, hfF, w, fun hwG ↦ disjoint_left.1 hKG hwK hwG, hw⟩
  choose f hfF w hwG hw using key
  -- The points chosen for a fixed `g ∈ F` form a universally null set.
  let Xf : (ℕ → ℕ) → Set (ℕ → Bool) := fun g ↦ {x | ∃ G : 𝒞, f G = g ∧ w G = x}
  have hX : ∀ g, IsUniversallyNull (Xf g) := fun g ↦ by
    refine hA.of_injOn (hφ g) ?_ ?_
    · rintro _ ⟨G, rfl, rfl⟩ _ ⟨G', hG', rfl⟩ heq
      have hee : (e G : ℕ → Bool) = e G' := by
        rw [← hw G, ← hw G', hG']
        exact heq
      rw [e.injective (Subtype.ext hee)]
    · rintro _ ⟨_, ⟨G, rfl, rfl⟩, rfl⟩
      rw [hw G]
      exact (e G).2
  -- Their union is not null, because it meets the complement of every member of `𝒞`.
  refine (add_le (I := 𝒰𝒩) (𝒜 := Xf '' F) ?_ fun hUN ↦ ?_).trans (mk_image_le.trans hF)
  · rintro _ ⟨g, -, rfl⟩
    exact hX g
  · obtain ⟨G, hG, hsub⟩ := hcof _ (universallyNull_subset_null hUN)
    exact hwG ⟨G, hG⟩ (hsub ⟨Xf (f ⟨G, hG⟩), ⟨_, hfF _, rfl⟩, ⟨G, hG⟩, rfl, rfl⟩)

/-- Theorem B follows from the coding lemma and `add 𝒩 ≤ add 𝒰𝒩`. -/
theorem theoremB_of_codingLemma (hC : CodingLemma) (hle : GotoCor513) : TheoremB :=
  fun A hA hcard ↦
    le_antisymm (add_universallyNull_le_add_null_of_codingLemma hC A hA hcard) hle

end AddUN
