import ASGinzburg.FiniteProjectiveDuality
import ASGinzburg.HomotopyOpposite
import ASGinzburg.HomotopyEquivalence
import ASGinzburg.FullSubcategoryEquivalence
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) {I : Type*}

noncomputable def finiteProjectiveComplexADualEquivalence (c : ComplexShape I) :
    (HomologicalComplex A.RightFiniteProjective c)ᵒᵖ ≌
      HomologicalComplex A.LeftFiniteProjective c.symm := by
  letI : A.finiteProjectiveADualEquivalence.functor.Additive :=
    A.rightFiniteProjectiveADualFunctorAdditive
  exact (HomologicalComplex.opEquivalence A.RightFiniteProjective c).trans
    (A.finiteProjectiveADualEquivalence.mapHomologicalComplex c.symm)

noncomputable def finiteProjectiveHomotopyADualEquivalence (c : ComplexShape I) :
    (HomotopyCategory A.RightFiniteProjective c)ᵒᵖ ≌
      HomotopyCategory A.LeftFiniteProjective c.symm := by
  letI : A.finiteProjectiveADualEquivalence.functor.Additive :=
    A.rightFiniteProjectiveADualFunctorAdditive
  exact (ASGinzburg.homotopyOpEquivalence A.RightFiniteProjective c).trans
    (ASGinzburg.homotopyMapEquivalence A.finiteProjectiveADualEquivalence c.symm)
end ASGinzburg.ZAlgebra

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable (C : Type u) [Category.{v} C] [Preadditive C] (c : ComplexShape ℤ)

/-- Actual complexes which are zero outside a finite interval of degrees. -/
def boundedHomotopyProperty : ObjectProperty (HomotopyCategory C c) :=
  fun X => ∃ a b : ℤ, ∀ n, n < a ∨ b < n → IsZero (X.as.X n)

abbrev BoundedHomotopyCategory := (boundedHomotopyProperty C c).FullSubcategory
end ASGinzburg

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (c : ComplexShape ℤ)

theorem finiteProjectiveHomotopyADualEquivalence_bounded
    {X : (HomotopyCategory A.RightFiniteProjective c)ᵒᵖ}
    (h : ASGinzburg.boundedHomotopyProperty A.RightFiniteProjective c X.unop) :
    ASGinzburg.boundedHomotopyProperty A.LeftFiniteProjective c.symm
      ((A.finiteProjectiveHomotopyADualEquivalence c).functor.obj X) := by
  obtain ⟨a,b,h⟩ := h
  refine ⟨a,b,?_⟩
  intro n hn
  exact A.rightFiniteProjectiveADualFunctor.map_isZero ((h n hn).op)

theorem finiteProjectiveHomotopyADualEquivalence_inverse_bounded
    {X : HomotopyCategory A.LeftFiniteProjective c.symm}
    (h : ASGinzburg.boundedHomotopyProperty A.LeftFiniteProjective c.symm X) :
    ASGinzburg.boundedHomotopyProperty A.RightFiniteProjective c
      ((A.finiteProjectiveHomotopyADualEquivalence c).inverse.obj X).unop := by
  obtain ⟨a,b,h⟩ := h
  refine ⟨a,b,?_⟩
  intro n hn
  exact (A.leftFiniteProjectiveADualFunctor.rightOp.map_isZero (h n hn)).unop
noncomputable def boundedFiniteProjectiveADualEquivalence :
    (ASGinzburg.BoundedHomotopyCategory A.RightFiniteProjective c)ᵒᵖ ≌
      ASGinzburg.BoundedHomotopyCategory A.LeftFiniteProjective c.symm :=
  (ASGinzburg.fullSubcategoryOpEquivalence
    (ASGinzburg.boundedHomotopyProperty A.RightFiniteProjective c)).trans
    (ASGinzburg.restrictEquivalence (A.finiteProjectiveHomotopyADualEquivalence c)
      (ASGinzburg.boundedHomotopyProperty A.RightFiniteProjective c).op
      (ASGinzburg.boundedHomotopyProperty A.LeftFiniteProjective c.symm)
      (fun _ h => A.finiteProjectiveHomotopyADualEquivalence_bounded c h)
      (fun _ h => A.finiteProjectiveHomotopyADualEquivalence_inverse_bounded c h))
end ASGinzburg.ZAlgebra
