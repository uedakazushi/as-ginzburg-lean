import work.ASGinzburgDraft.AlgebraEnvelopingTensorRestriction
import work.ASGinzburgDraft.AlgebraEnvelopingTensorTotal
import Mathlib.Algebra.Homology.Additive

/-! The underlying vector-space bicomplex of the genuine enveloping
tensor bicomplex agrees with tensoring the restricted factor complexes. -/
namespace ASGinzburg
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {I₁ I₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (P : HomologicalComplex (ModuleCat.{w} Rᵐᵒᵖ) c₁)
variable (Q : HomologicalComplex (ModuleCat.{z} R) c₂)

noncomputable def tensorRightEnvelopingBicomplexRestrictScalarsIso :
    (((ModuleCat.restrictScalars (algebraMap k (AlgebraEnvelopingRing k R)ᵐᵒᵖ)).mapHomologicalComplex c₂).mapHomologicalComplex c₁).obj (tensorRightEnvelopingBicomplex k R P Q) ≅
    (((moduleTensorBifunctor k).mapBifunctorHomologicalComplex c₁ c₂).obj
      (((ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).mapHomologicalComplex c₁).obj P)).obj
        (((ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex c₂).obj Q) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i₁ => ?_) ?_
  · refine HomologicalComplex.Hom.isoOfComponents
      (fun i₂ => tensorRightEnvelopingRestrictScalarsIso k R (P.X i₁) (Q.X i₂)) ?_
    intro i j hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · intro i j hij
    ext n x
    rfl

end ASGinzburg
