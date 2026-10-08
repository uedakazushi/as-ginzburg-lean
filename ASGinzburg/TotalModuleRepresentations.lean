import ASGinzburg.TotalAlgebraLift
import ASGinzburg.TotalComponentActions
import Mathlib.Algebra.Algebra.Opposite

/-! Honest algebra representations on the left and right total spaces. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- Genuine left action of the full total algebra on a concrete left-module total space. -/
noncomputable def leftTotalRepresentation (M : A.LeftModule) :
    A.totalAlgebra →ₙₐ[k] Module.End k (A.leftModuleTotalSpace M) :=
  A.totalAlgebraLift (A.leftTotalComponentRepresentation M)
    (fun _ _ _ a b => (A.leftModuleTotalAction_comp M a b).symm)
    (fun _ _ _ _ a b h => A.leftModuleTotalAction_comp_off M a b h)

@[simp] theorem leftTotalRepresentation_component (M : A.LeftModule) {i j : ℤ}
    (a : A.Hom i j) :
    A.leftTotalRepresentation M (A.totalAlgebraComponent a) = A.leftModuleTotalAction M a :=
  A.totalAlgebraLiftLinear_component _ a

/-- A right action is a homomorphism into the opposite endomorphism algebra. -/
noncomputable def rightTotalComponentOppositeRepresentation (M : A.RightModule) (i j : ℤ) :
    A.Hom i j →ₗ[k] (Module.End k (A.rightModuleTotalSpace M))ᵐᵒᵖ :=
  (MulOpposite.opLinearEquiv k).toLinearMap.comp (A.rightTotalComponentRepresentation M i j)

noncomputable def rightTotalRepresentation (M : A.RightModule) :
    A.totalAlgebra →ₙₐ[k] (Module.End k (A.rightModuleTotalSpace M))ᵐᵒᵖ :=
  A.totalAlgebraLift (A.rightTotalComponentOppositeRepresentation M)
    (fun _ _ _ a b => MulOpposite.unop_injective (A.rightModuleTotalAction_comp M a b).symm)
    (fun _ _ _ _ a b h => MulOpposite.unop_injective
      (A.rightModuleTotalAction_comp_off M a b h))

@[simp] theorem rightTotalRepresentation_component (M : A.RightModule) {i j : ℤ}
    (a : A.Hom i j) :
    (A.rightTotalRepresentation M (A.totalAlgebraComponent a)).unop =
      A.rightModuleTotalAction M a :=
  congrArg MulOpposite.unop (A.totalAlgebraLiftLinear_component _ a)

end ASGinzburg.ZAlgebra
