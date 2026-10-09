import ASGinzburg.GinzburgSimpleFiniteProjectiveResolution
import ASGinzburg.FiniteProjectiveResolutionExtColimits

/-! Genuine Ginzburg regularity implies the required actual Ext/colimit
exchange for each right simple through its derived finite projective
resolution; the exchange is not an added hypothesis. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u w t
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def GinzburgRegular.simpleExtPreservesExactColimits {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) (J : Type w) [Category.{t} J]
    [HasColimitsOfShape J (Q.unrolledJacobianZAlgebra k φ).RightModule]
    [HasColimitsOfShape J (ModuleCat.{u} k)] [HasExactColimitsOfShape J (ModuleCat.{u} k)]
    (n : ℕ) : PreservesColimitsOfShape J
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleExtCovariant
        ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height v)) n) :=
  (Q.unrolledJacobianZAlgebra k φ).rightFiniteProjectiveResolutionExtPreservesExactColimits 3
    (h.simple_hasRightFiniteProjectiveResolutionLength Q k v) J n

noncomputable def GinzburgRegular.simpleExtPreservesCoproducts {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) (I : Type) (n : ℕ) :
    PreservesColimitsOfShape (Discrete I)
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleExtCovariant
        ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height v)) n) := by
  letI : HasExactColimitsOfShape (Discrete I) (ModuleCat.{u} k) := moduleCatExactCoproducts I
  exact h.simpleExtPreservesExactColimits Q k v (Discrete I) n

noncomputable def GinzburgRegular.simpleExtCoproductIso {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) {I : Type} (n : ℕ)
    (F : I → (Q.unrolledJacobianZAlgebra k φ).RightModule) :
    ModuleCat.of k (Abelian.Ext.{u}
      ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height v)) (∐ F) n) ≅
      ∐ fun i => ModuleCat.of k (Abelian.Ext.{u}
        ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height v)) (F i) n) := by
  letI := h.simpleExtPreservesCoproducts Q k v I n
  exact PreservesCoproduct.iso
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleExtCovariant
      ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height v)) n) F

end ASGinzburg.CutQuiver
