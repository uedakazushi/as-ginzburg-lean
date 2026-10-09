import ASGinzburg.FoundationTotalRecoveryIso

/-! The recovery isomorphism is natural in the original presheaf;
its inverse is the genuine unit for the two finite-ring functors. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

theorem foundationRightTotalRecoveryIso_natural
    {M N : A.FoundationRightModule Q} (f : M ⟶ N) :
    (A.foundationRingRightComponentRecovery Q).map ((A.foundationRightTotalFunctor Q).map f) ≫
      (A.foundationRightTotalRecoveryIso Q N).hom=
      (A.foundationRightTotalRecoveryIso Q M).hom ≫ f := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

noncomputable def foundationRightTotalRecoveryNatIso :
    A.foundationRightTotalFunctor Q ⋙ A.foundationRingRightComponentRecovery Q ≅
      𝟭 (A.FoundationRightModule Q) :=
  NatIso.ofComponents (A.foundationRightTotalRecoveryIso Q)
    (fun f => A.foundationRightTotalRecoveryIso_natural Q f)

noncomputable def foundationRightTotalUnitIso :
    𝟭 (A.FoundationRightModule Q) ≅
      A.foundationRightTotalFunctor Q ⋙ A.foundationRingRightComponentRecovery Q :=
  (A.foundationRightTotalRecoveryNatIso Q).symm

end ASGinzburg.ZAlgebra
