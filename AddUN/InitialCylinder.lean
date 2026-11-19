/-
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import AddUN.CantorMeasure

/-!
# Initial cylinders of the Cantor space

An *initial cylinder* is a set of the form `cylinderOn (Finset.range n) v`: the points that
agree with `v` on the first `n` coordinates. The initial cylinders form a π-system that
generates the σ-algebra of the Cantor space. So two finite measures that agree on the initial
cylinders are equal (`Measure.ext_of_initialCylinders`).
-/

@[expose] public section

open Set

namespace MeasureTheory

/-- The family of initial cylinders of the Cantor space. -/
def initialCylinders : Set (Set (ℕ → Bool)) :=
  {S | ∃ (n : ℕ) (v : ℕ → Bool), S = cylinderOn (Finset.range n) v}

lemma isPiSystem_initialCylinders : IsPiSystem initialCylinders := by
  rintro _ ⟨n, v, rfl⟩ _ ⟨m, v', rfl⟩ ⟨w, hw, hw'⟩
  refine ⟨max n m, w, ?_⟩
  ext y
  simp only [mem_inter_iff, mem_cylinderOn, Finset.mem_range] at hw hw' ⊢
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases lt_max_iff.1 hi with h | h
    · rw [h1 i h, hw i h]
    · rw [h2 i h, hw' i h]
  · intro h
    exact ⟨fun i hi ↦ (h i (lt_max_of_lt_left hi)).trans (hw i hi),
      fun i hi ↦ (h i (lt_max_of_lt_right hi)).trans (hw' i hi)⟩

/-- The initial cylinders generate the σ-algebra of the Cantor space. -/
lemma generateFrom_initialCylinders :
    (inferInstance : MeasurableSpace (ℕ → Bool)) =
      MeasurableSpace.generateFrom initialCylinders := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · -- Every coordinate map is measurable for the generated σ-algebra.
    refine iSup_le fun i ↦ ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    intro s _
    have hcoord : ∀ b : Bool, MeasurableSet[MeasurableSpace.generateFrom initialCylinders]
        {w : ℕ → Bool | w i = b} := fun b ↦ by
      have h : {w : ℕ → Bool | w i = b} =
          ⋃ (u : Fin (i + 1) → Bool) (_ : u (Fin.last i) = b),
            cylinderOn (Finset.range (i + 1)) fun j ↦ if h : j < i + 1 then u ⟨j, h⟩ else false := by
        ext w
        simp only [mem_ofPred_eq, mem_iUnion, mem_cylinderOn, Finset.mem_range, exists_prop]
        constructor
        · intro hw
          exact ⟨fun j ↦ w j, hw, fun j hj ↦ by simp [hj]⟩
        · rintro ⟨u, hu, hwu⟩
          rw [hwu i (Nat.lt_succ_self i), dif_pos (Nat.lt_succ_self i), ← hu]
          rfl
      rw [h]
      exact .iUnion fun u ↦ .iUnion fun _ ↦ MeasurableSpace.measurableSet_generateFrom ⟨_, _, rfl⟩
    have hs : (fun w : ℕ → Bool ↦ w i) ⁻¹' s = ⋃ (b : Bool) (_ : b ∈ s), {w | w i = b} := by
      ext w
      simp
    change MeasurableSet[MeasurableSpace.generateFrom initialCylinders]
      ((fun w : ℕ → Bool ↦ w i) ⁻¹' s)
    rw [hs]
    exact .iUnion fun b ↦ .iUnion fun _ ↦ hcoord b
  · rintro _ ⟨n, v, rfl⟩
    exact measurableSet_cylinderOn _ _

/-- Two finite measures on the Cantor space that agree on the initial cylinders are equal. -/
theorem Measure.ext_of_initialCylinders {μ ν : Measure (ℕ → Bool)} [IsFiniteMeasure μ]
    (h : ∀ (n : ℕ) (v : ℕ → Bool),
      μ (cylinderOn (Finset.range n) v) = ν (cylinderOn (Finset.range n) v)) : μ = ν :=
  ext_of_generate_finite _ generateFrom_initialCylinders isPiSystem_initialCylinders
    (by rintro _ ⟨n, v, rfl⟩; exact h n v) (by simpa [cylinderOn] using h 0 fun _ ↦ false)

end MeasureTheory
