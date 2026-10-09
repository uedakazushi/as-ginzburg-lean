import ASGinzburg.PeriodCutRightRepresentation

/-! Each actual corner-cover module gives an ordinary unital right
module over the native cut ring, with its original compatible k action. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutRightActionHom (M : (E.cornerCoverZAlgebra Q).RightModule) :
    (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ →+*
      Module.End k (E.CornerModuleTotalSpace Q M) where
  toFun r := (E.cutRightRepresentation Q M r.unop).unop
  map_zero' := by rw [MulOpposite.unop_zero,map_zero,MulOpposite.unop_zero]
  map_one' := by rw [MulOpposite.unop_one,map_one,MulOpposite.unop_one]
  map_add' r s := by rw [MulOpposite.unop_add,map_add,MulOpposite.unop_add]
  map_mul' r s := by rw [MulOpposite.unop_mul,map_mul,MulOpposite.unop_mul]

noncomputable instance cutRightRingModule (M : (E.cornerCoverZAlgebra Q).RightModule) :
    Module (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ
      (E.CornerModuleTotalSpace Q M) :=
  Module.compHom _ (E.cutRightActionHom Q M)

theorem cutRightRingModule_smul (M : (E.cornerCoverZAlgebra Q).RightModule)
    (r : (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ)
    (v : E.CornerModuleTotalSpace Q M) :
    r • v=(E.cutRightRepresentation Q M r.unop).unop v := rfl

noncomputable instance cutRightRingModuleScalarComm
    (M : (E.cornerCoverZAlgebra Q).RightModule) :
    SMulCommClass k (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ
      (E.CornerModuleTotalSpace Q M) where
  smul_comm c r v := ((E.cutRightActionHom Q M r).map_smul c v).symm

noncomputable instance cutRightRingModuleScalarTower
    (M : (E.cornerCoverZAlgebra Q).RightModule) :
    IsScalarTower k (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ
      (E.CornerModuleTotalSpace Q M) where
  smul_assoc c r v := by
    change (E.cutRightRepresentation Q M (c • r).unop).unop v=
      c • (E.cutRightRepresentation Q M r.unop).unop v
    rw [MulOpposite.unop_smul,map_smul,MulOpposite.unop_smul,LinearMap.smul_apply]

noncomputable def cornerRightRingModule (M : (E.cornerCoverZAlgebra Q).RightModule) :
    ModuleCat.{v} (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ :=
  ModuleCat.of _ (E.CornerModuleTotalSpace Q M)

theorem cutRightRingModule_homogeneous_smul
    (M : (E.cornerCoverZAlgebra Q).RightModule) (m : ℕ)
    (r : E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) m)
    (v : E.CornerModuleTotalSpace Q M) :
    (MulOpposite.op (E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val:ℤ)) m r)) • v=
      E.cutHomogeneousRightOperator Q M m r v := by
  rw [E.cutRightRingModule_smul,MulOpposite.unop_op,E.cutRightRepresentation_homogeneous]

end ASGinzburg.ZAlgebra.PeriodIso
