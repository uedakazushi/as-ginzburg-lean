import ASGinzburg.AlgebraEnvelopingQuotientTensorRightModule
import ASGinzburg.BalancedTensorRightFieldModuleChange

/-! The natural field action on the actual right quotient agrees
with the field action induced by its bundled right-module structure.
The comparison also holds for the actual tensor functor and Tor. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (J : Ideal R) [J.IsTwoSided]

attribute [local instance] idealQuotientRightScalarTower

theorem idealQuotientRightInducedField_eq :
    (Module.compHom (R ⧸ J)ᵐᵒᵖ (algebraMap k Rᵐᵒᵖ) : Module k (R ⧸ J)ᵐᵒᵖ) =
      (inferInstance : Module k (R ⧸ J)ᵐᵒᵖ) :=
  algebraModuleCompHomField_eq k Rᵐᵒᵖ (R ⧸ J)ᵐᵒᵖ

noncomputable def idealQuotientRightCanonicalFieldIso :
    (ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).obj (idealQuotientRightObject J) ≅
      ModuleCat.of k (R ⧸ J)ᵐᵒᵖ :=
  algebraModuleRestrictScalarsIso k Rᵐᵒᵖ (R ⧸ J)ᵐᵒᵖ

noncomputable def balancedTensorRightIdealQuotientCanonicalFieldIso :
    balancedTensorRightFunctor.{u,v,v,w} k R (idealQuotientRightObject J) ≅
      balancedTensorRightFunctor.{u,v,v,w} k R (R ⧸ J)ᵐᵒᵖ :=
  balancedTensorRightFunctorCanonicalFieldIso k R (R ⧸ J)ᵐᵒᵖ

noncomputable def balancedTensorTorIdealQuotientCanonicalFieldIso (n : ℕ) :
    balancedTensorTorFunctor.{u,v,v,w} k R (idealQuotientRightObject J) n ≅
      balancedTensorTorFunctor.{u,v,v,w} k R (R ⧸ J)ᵐᵒᵖ n :=
  balancedTensorTorRightCanonicalFieldIso k R (R ⧸ J)ᵐᵒᵖ n

end ASGinzburg
