import ASGinzburg.RightModuleMinimality

/-!
# Minimal differentials vanish after Hom into a vertex simple

Positive-degree products vanish in s_i. Every map into s_i annihilates the
source radical, so actual minimal differentials induce zero Hom differentials.
This prepares Ext computations; it is not an Ext comparison theorem.
-/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- Every positive-degree product in the vertex simple is zero. -/
theorem positiveActionSpan_simple_eq_bot (i j : ℤ) :
    A.positiveActionSpan (A.simpleRightModule i) j = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨l, hl, x, a, rfl⟩
    by_cases hj : j = i
    · have hli : l ≠ i := by omega
      haveI : Subsingleton ((A.rightModuleEvaluation l).obj (A.simpleRightModule i)) :=
        ModuleCat.isZero_iff_subsingleton.mp (A.simpleRightModule_off_diagonal i l hli)
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx, map_zero]
      exact Submodule.zero_mem _
    · haveI : Subsingleton ((A.simpleRightModule i).obj.obj (op (⟨j⟩ : A.Obj))) :=
        ModuleCat.isZero_iff_subsingleton.mp (A.simpleRightModule_off_diagonal i j hj)
      have hy : (A.simpleRightModule i).obj.map
          (show (⟨j⟩ : A.Obj) ⟶ ⟨l⟩ from a).op x = 0 := Subsingleton.elim _ _
      rw [hy]
      exact Submodule.zero_mem _
  · exact bot_le

/-- Morphisms into a vertex simple annihilate the source radical. -/
theorem radical_inclusion_comp_simple_eq_zero (i : ℤ) {M : A.RightModule}
    (f : M ⟶ A.simpleRightModule i) :
    (A.rightModuleRadical M).inclusion ≫ f = 0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  ext x
  have h := A.positiveActionSpan_map_mem f X.unop.index x.property
  rw [A.positiveActionSpan_simple_eq_bot] at h
  exact h

/-- Applying Hom(-,s_i) to a minimal differential gives a zero differential. -/
theorem minimalMorphism_comp_simple_eq_zero {M N : A.RightModule} (f : M ⟶ N)
    (hf : A.IsMinimalMorphism f) (i : ℤ) (g : N ⟶ A.simpleRightModule i) : f ≫ g = 0 := by
  rw [← A.minimalMorphismLift_inclusion f hf, Category.assoc,
    A.radical_inclusion_comp_simple_eq_zero i g, comp_zero]

end ASGinzburg.ZAlgebra
