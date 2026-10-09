import ASGinzburg.OppositeGinzburgCochainIso
import ASGinzburg.GinzburgMinimalResolutionExt

/-! Ginzburg regularity supplies a genuine minimal resolution on the
reflected opposite Jacobian algebra. Identification with the original
left-module category and the dual complex remains a separate obligation. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def GinzburgRegular.oppositeMinimalASResolution {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.opposite.LiftVertex) :
    (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).ASResolution
      Q.opposite v :=
  (GinzburgRegular.opposite Q k h).minimalASResolution Q.opposite k v

theorem GinzburgRegular.opposite_exists_ASResolution {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.opposite.LiftVertex) :
    Nonempty ((Q.opposite.unrolledJacobianZAlgebra k
      (Q.oppositePotentialEquiv k φ)).ASResolution Q.opposite v) :=
  ⟨h.oppositeMinimalASResolution Q k v⟩

end ASGinzburg.CutQuiver
