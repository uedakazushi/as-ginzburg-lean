import ASGinzburg.BalancedTensorLeftFieldModuleChange
import ASGinzburg.BalancedTensorTor

/-! Equality transport of the fixed right factor's field module
preserves the actual balanced tensor functor and its derived Tor. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module Rᵐᵒᵖ M]

noncomputable def balancedTensorRightFunctorFieldModuleChangeIso
    (P Q : Module k M) (h : P = Q) :
    @balancedTensorRightFunctor.{u,v,w,z} k _ R _ _ M _ P _ ≅
      @balancedTensorRightFunctor.{u,v,w,z} k _ R _ _ M _ Q _ := by
  cases h
  exact Iso.refl _

noncomputable def balancedTensorTorRightFieldModuleChangeIso
    (P Q : Module k M) (h : P = Q) (n : ℕ) :
    @balancedTensorTorFunctor.{u,v,w,z} k _ R _ _ M _ P _ n ≅
      @balancedTensorTorFunctor.{u,v,w,z} k _ R _ _ M _ Q _ n := by
  cases h
  exact Iso.refl _

variable [fieldModule : Module k M] [IsScalarTower k Rᵐᵒᵖ M]

noncomputable def balancedTensorRightFunctorCanonicalFieldIso :
    @balancedTensorRightFunctor.{u,v,w,z} k _ R _ _ M _
      (Module.compHom M (algebraMap k Rᵐᵒᵖ)) _ ≅
      balancedTensorRightFunctor.{u,v,w,z} k R M :=
  balancedTensorRightFunctorFieldModuleChangeIso k R M
    (Module.compHom M (algebraMap k Rᵐᵒᵖ)) fieldModule
    (algebraModuleCompHomField_eq k Rᵐᵒᵖ M)

noncomputable def balancedTensorTorRightCanonicalFieldIso (n : ℕ) :
    @balancedTensorTorFunctor.{u,v,w,z} k _ R _ _ M _
      (Module.compHom M (algebraMap k Rᵐᵒᵖ)) _ n ≅
      balancedTensorTorFunctor.{u,v,w,z} k R M n :=
  balancedTensorTorRightFieldModuleChangeIso k R M
    (Module.compHom M (algebraMap k Rᵐᵒᵖ)) fieldModule
    (algebraModuleCompHomField_eq k Rᵐᵒᵖ M) n

end ASGinzburg
