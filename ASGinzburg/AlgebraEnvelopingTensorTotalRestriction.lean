import ASGinzburg.AlgebraEnvelopingTensorBicomplexRestriction
import ASGinzburg.BicomplexTotalFunctor
import ASGinzburg.NatTotalExists

/-! Actual scalar restriction commutes with the enveloping tensor total,
including its canonical diagonal coproducts and its signed differentials. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
variable (Q : ChainComplex (ModuleCat.{z} R) ℕ)

noncomputable def tensorRightEnvelopingTotalRestrictScalarsIso :
    ((ModuleCat.restrictScalars (algebraMap k (AlgebraEnvelopingRing k R)ᵐᵒᵖ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (tensorRightEnvelopingTotal k R P Q (ComplexShape.down ℕ)) ≅
      mapBifunctor
        (((ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P)
        (((ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Q) (moduleTensorBifunctor k) (ComplexShape.down ℕ) := by
  let G := ModuleCat.restrictScalars (algebraMap k (AlgebraEnvelopingRing k R)ᵐᵒᵖ)
  let K := tensorRightEnvelopingBicomplex k R P Q
  letI : ∀ n, PreservesColimit
      (Discrete.functor (K.toGradedObject.mapObjFun
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n)) G :=
    fun _ => inferInstance
  exact bicomplexTotalFunctorIso G K (ComplexShape.down ℕ) ≪≫
    HomologicalComplex₂.total.mapIso
      (tensorRightEnvelopingBicomplexRestrictScalarsIso k R P Q) (ComplexShape.down ℕ)

end ASGinzburg
