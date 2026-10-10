import ASGinzburg.RightTopBasisPresentation
import ASGinzburg.RightSmallCoproductRadicals

/-! The actual basis-of-top projective presentation preserves a cover
height upper bound, and its genuine kernel inherits that same bound. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightTopBasisIndex_le_of_height_bound (M : A.RightModule) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((A.rightModuleEvaluation i).obj M))
    (g : A.rightTopBasisIndex M) : g.1 ≤ b := by
  by_contra h
  letI : Subsingleton ((A.rightModuleEvaluation g.1).obj M) :=
    ModuleCat.isZero_iff_subsingleton.mp (hb g.1 (by omega))
  letI : Subsingleton (A.RightModuleTopSpace M g.1) := ⟨fun x y => by
    obtain ⟨x,rfl⟩ := (A.positiveActionSpan M g.1).mkQ_surjective x
    obtain ⟨y,rfl⟩ := (A.positiveActionSpan M g.1).mkQ_surjective y
    exact congrArg (A.positiveActionSpan M g.1).mkQ (Subsingleton.elim x y)⟩
  exact (Module.Free.chooseBasis k (A.RightModuleTopSpace M g.1)).ne_zero g.2
    (Subsingleton.elim _ _)

theorem rightTopBasisFreeModule_isZero_above_of_height_bound
    (M : A.RightModule) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((A.rightModuleEvaluation i).obj M))
    (i : ℤ) (hi : b < i) :
    IsZero ((A.rightModuleEvaluation i).obj (A.rightTopBasisFreeModule M)) := by
  classical
  let g := fun g : A.rightTopBasisIndex M => A.representable g.1
  letI : ∀ a : A.rightTopBasisIndex M,
      Subsingleton ((A.rightModuleEvaluation i).obj (g a)) := fun a => by
    refine ⟨fun x y => ?_⟩
    have ha := A.rightTopBasisIndex_le_of_height_bound M b hb a
    change A.Hom i a.1 at x y
    rw [A.positive (by omega) x, A.positive (by omega) y]
  letI : Subsingleton (⨁ a, (A.rightModuleEvaluation i).obj (g a)) := inferInstance
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => (A.rightSmallCoproductComponentIso g i).toLinearEquiv.injective
    (Subsingleton.elim _ _)⟩

theorem rightTopBasisFreeModuleπ_kernel_isZero_above_of_height_bound
    (M : A.RightModule) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((A.rightModuleEvaluation i).obj M))
    (i : ℤ) (hi : b < i) :
    IsZero ((A.rightModuleEvaluation i).obj (kernel (A.rightTopBasisFreeModuleπ M))) := by
  apply IsZero.of_mono ((A.rightModuleEvaluation i).map (kernel.ι (A.rightTopBasisFreeModuleπ M)))
  exact A.rightTopBasisFreeModule_isZero_above_of_height_bound M b hb i hi

end ASGinzburg.ZAlgebra
