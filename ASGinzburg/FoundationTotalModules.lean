import ASGinzburg.FoundationTotalActionLaws
import Mathlib.Algebra.Module.RingHom

/-! The existing finite foundation presheaf gives a genuine module over
the opposite of its actual convolution algebra, without unitization or
replacement of the original component actions. -/
namespace ASGinzburg.ZAlgebra
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

noncomputable def foundationRightTotalOppRepresentation (M : A.FoundationRightModule Q) :
    A.FoundationAlgebra Q →ₐ[k] (Module.End k (A.foundationRightTotalSpace Q M))ᵐᵒᵖ where
  toFun x := MulOpposite.op (A.foundationRightTotalAction Q M x)
  map_zero' := congrArg MulOpposite.op (A.foundationRightTotalRepresentation Q M).map_zero
  map_one' := congrArg MulOpposite.op (A.foundationRightTotalAction_one Q M)
  map_add' x y := congrArg MulOpposite.op (A.foundationRightTotalAction_add Q M x y)
  map_mul' x y := congrArg MulOpposite.op (A.foundationRightTotalAction_mul Q M x y)
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one,foundationRightTotalAction_smul,
      foundationRightTotalAction_one]
    rfl

noncomputable def foundationRightTotalUnitalRepresentation (M : A.FoundationRightModule Q) :
    (A.FoundationAlgebra Q)ᵐᵒᵖ →ₐ[k] Module.End k (A.foundationRightTotalSpace Q M) :=
  AlgHom.opComm (A.foundationRightTotalOppRepresentation Q M)

noncomputable def foundationRightTotalModuleStructure (M : A.FoundationRightModule Q) :
    Module (A.FoundationAlgebra Q)ᵐᵒᵖ (A.foundationRightTotalSpace Q M) :=
  Module.compHom _ (A.foundationRightTotalUnitalRepresentation Q M).toRingHom

noncomputable def foundationRightTotalModule (M : A.FoundationRightModule Q) :
    ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ := by
  letI := A.foundationRightTotalModuleStructure Q M
  exact ModuleCat.of (A.FoundationAlgebra Q)ᵐᵒᵖ (A.foundationRightTotalSpace Q M)

theorem foundationRightTotalModule_smul (M : A.FoundationRightModule Q)
    (a : A.FoundationAlgebra Q) (m : A.foundationRightTotalModule Q M) :
    MulOpposite.op a • m=A.foundationRightTotalAction Q M a m := rfl

end ASGinzburg.ZAlgebra
