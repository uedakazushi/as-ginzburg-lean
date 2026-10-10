import work.ASGinzburgDraft.BalancedTensorEnvelopingFunctorNaturality
import ASGinzburg.AlgebraEnvelopingTensorTotal
import Mathlib.Algebra.Homology.Additive

/-! The actual balanced enveloping tensor of the double resolution
agrees with the ordinary balanced tensor bicomplex, through its natural
component isomorphisms. -/
namespace ASGinzburg
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {I₁ I₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (P : HomologicalComplex (ModuleCat.{max v w} Rᵐᵒᵖ) c₁)
variable (Q : HomologicalComplex (ModuleCat.{max v w} R) c₂)

attribute [local instance] regularEnvelopingModule regularEnvelopingScalarTower

noncomputable def balancedTensorEnvelopingBicomplexIso :
    ((((balancedTensorLeftFunctor k (AlgebraEnvelopingRing k R) R).mapHomologicalComplex c₂).mapHomologicalComplex
      c₁).obj (tensorRightEnvelopingBicomplex k R P Q)) ≅
    (((balancedTensorBifunctor k R).mapBifunctorHomologicalComplex c₁ c₂).obj P).obj Q := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i₁ => ?_) ?_
  · refine HomologicalComplex.Hom.isoOfComponents
      (fun i₂ => balancedTensorEnvelopingModuleIso k R (P.X i₁) (Q.X i₂)) ?_
    intro i j hij
    simpa using balancedTensorEnvelopingModuleIso_naturality k R (𝟙 (P.X i₁)) (Q.d i j)
  · intro i j hij
    ext n
    simpa using balancedTensorEnvelopingModuleIso_naturality k R (P.d i j) (𝟙 (Q.X n))

end ASGinzburg
