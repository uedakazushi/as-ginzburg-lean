import ASGinzburg.HomotopyDegreeReverse
import ASGinzburg.FiniteProjectiveComplexDuality
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable (C : Type u) [Category.{v} C] [Preadditive C]

theorem reverseCochainHomotopyFunctor_bounded {X : HomotopyCategory C (ComplexShape.up ℤ)}
    (h : boundedHomotopyProperty C (ComplexShape.up ℤ) X) :
    boundedHomotopyProperty C (ComplexShape.down ℤ) ((reverseCochainHomotopyFunctor C).obj X) := by
  obtain ⟨a,b,h⟩ := h
  refine ⟨-b,-a,?_⟩
  intro n hn
  exact h (-n) (by omega)

theorem reverseChainHomotopyFunctor_bounded {X : HomotopyCategory C (ComplexShape.down ℤ)}
    (h : boundedHomotopyProperty C (ComplexShape.down ℤ) X) :
    boundedHomotopyProperty C (ComplexShape.up ℤ) ((reverseChainHomotopyFunctor C).obj X) := by
  obtain ⟨a,b,h⟩ := h
  refine ⟨-b,-a,?_⟩
  intro n hn
  exact h (-n) (by omega)

def boundedReverseDegreeEquivalence :
    BoundedHomotopyCategory C (ComplexShape.up ℤ) ≌ BoundedHomotopyCategory C (ComplexShape.down ℤ) :=
  restrictEquivalence (reverseDegreeHomotopyEquivalence C)
    (boundedHomotopyProperty C (ComplexShape.up ℤ))
    (boundedHomotopyProperty C (ComplexShape.down ℤ))
    (fun _ h => reverseCochainHomotopyFunctor_bounded C h)
    (fun _ h => reverseChainHomotopyFunctor_bounded C h)
end ASGinzburg

namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- Termwise A-dual followed by degree reversal, with inverse the left A-dual. -/
noncomputable def boundedCochainFiniteProjectiveADualEquivalence :
    (ASGinzburg.BoundedHomotopyCategory A.RightFiniteProjective (ComplexShape.up ℤ))ᵒᵖ ≌
      ASGinzburg.BoundedHomotopyCategory A.LeftFiniteProjective (ComplexShape.up ℤ) :=
  (A.boundedFiniteProjectiveADualEquivalence (ComplexShape.up ℤ)).trans
    (ASGinzburg.boundedReverseDegreeEquivalence A.LeftFiniteProjective).symm
end ASGinzburg.ZAlgebra
