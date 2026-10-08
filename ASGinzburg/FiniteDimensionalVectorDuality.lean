import ASGinzburg.ModuleVectorDuality
import ASGinzburg.FiniteDimensionalExtDuality

namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

def rightFiniteDimensionalVectorDualFunctor : A.RightFiniteDimensionalᵒᵖ ⥤ A.LeftFiniteDimensional where
  obj M := ⟨A.rightModuleVectorDual M.unop.obj,A.rightModuleVectorDual_finite M.unop.property⟩
  map f := A.rightModuleVectorDualMap f.unop
  map_id M := A.rightModuleVectorDualFunctor.map_id (op M.unop.obj)
  map_comp f g := A.rightModuleVectorDualFunctor.map_comp
    (A.rightFiniteDimensionalProperty.ι.map f.unop).op (A.rightFiniteDimensionalProperty.ι.map g.unop).op

def leftFiniteDimensionalVectorDualFunctor : A.LeftFiniteDimensionalᵒᵖ ⥤ A.RightFiniteDimensional where
  obj M := ⟨A.leftModuleVectorDual M.unop.obj,A.leftModuleVectorDual_finite M.unop.property⟩
  map f := A.leftModuleVectorDualMap f.unop
  map_id M := A.leftModuleVectorDualFunctor.map_id (op M.unop.obj)
  map_comp f g := A.leftModuleVectorDualFunctor.map_comp
    (A.leftFiniteDimensionalProperty.ι.map f.unop).op (A.leftFiniteDimensionalProperty.ι.map g.unop).op

noncomputable def rightFiniteDimensionalVectorBidualNatIso :
    A.rightFiniteDimensionalVectorDualFunctor.rightOp ⋙ A.leftFiniteDimensionalVectorDualFunctor ≅
      𝟭 A.RightFiniteDimensional :=
  NatIso.ofComponents (fun M => by
    letI := A.rightModuleVectorBidualEvaluation_isIso M.property
    exact A.rightFiniteDimensionalProperty.isoMk
      (X := ((A.rightFiniteDimensionalVectorDualFunctor.rightOp ⋙ A.leftFiniteDimensionalVectorDualFunctor).obj M)) (Y := M) (asIso (A.rightModuleVectorBidualEvaluation M.obj)).symm)
    (by
      intro M N f
      letI := A.rightModuleVectorBidualEvaluation_isIso M.property
      letI := A.rightModuleVectorBidualEvaluation_isIso N.property
      change A.leftModuleVectorDualMap (A.rightModuleVectorDualMap f) ≫
          inv (A.rightModuleVectorBidualEvaluation N.obj) =
        inv (A.rightModuleVectorBidualEvaluation M.obj) ≫ f
      rw [IsIso.comp_inv_eq,Category.assoc,IsIso.eq_inv_comp]
      exact (A.rightModuleVectorBidualEvaluation_natural f).symm)

noncomputable def leftFiniteDimensionalVectorBidualNatIso :
    A.leftFiniteDimensionalVectorDualFunctor.rightOp ⋙ A.rightFiniteDimensionalVectorDualFunctor ≅
      𝟭 A.LeftFiniteDimensional :=
  NatIso.ofComponents (fun M => by
    letI := A.leftModuleVectorBidualEvaluation_isIso M.property
    exact A.leftFiniteDimensionalProperty.isoMk
      (X := ((A.leftFiniteDimensionalVectorDualFunctor.rightOp ⋙ A.rightFiniteDimensionalVectorDualFunctor).obj M)) (Y := M) (asIso (A.leftModuleVectorBidualEvaluation M.obj)).symm)
    (by
      intro M N f
      letI := A.leftModuleVectorBidualEvaluation_isIso M.property
      letI := A.leftModuleVectorBidualEvaluation_isIso N.property
      change A.rightModuleVectorDualMap (A.leftModuleVectorDualMap f) ≫
          inv (A.leftModuleVectorBidualEvaluation N.obj) =
        inv (A.leftModuleVectorBidualEvaluation M.obj) ≫ f
      rw [IsIso.comp_inv_eq,Category.assoc,IsIso.eq_inv_comp]
      exact (A.leftModuleVectorBidualEvaluation_natural f).symm)

noncomputable def finiteDimensionalVectorDualEquivalence : A.RightFiniteDimensionalᵒᵖ ≌ A.LeftFiniteDimensional :=
  CategoryTheory.Equivalence.mk A.rightFiniteDimensionalVectorDualFunctor A.leftFiniteDimensionalVectorDualFunctor.rightOp
    (NatIso.op A.rightFiniteDimensionalVectorBidualNatIso) A.leftFiniteDimensionalVectorBidualNatIso

instance rightFiniteDimensionalVectorDualFunctorAdditive : A.rightFiniteDimensionalVectorDualFunctor.Additive where
  map_add := by
    intro M N f g
    let fb : op M.unop.obj ⟶ op N.unop.obj := (A.rightFiniteDimensionalProperty.ι.map f.unop).op
    let gb : op M.unop.obj ⟶ op N.unop.obj := (A.rightFiniteDimensionalProperty.ι.map g.unop).op
    exact A.rightModuleVectorDualFunctor.map_add (f := fb) (g := gb)
instance rightFiniteDimensionalVectorDualFunctorLinear : A.rightFiniteDimensionalVectorDualFunctor.Linear k where
  map_smul := by
    intro M N f r
    let fb : op M.unop.obj ⟶ op N.unop.obj := (A.rightFiniteDimensionalProperty.ι.map f.unop).op
    exact A.rightModuleVectorDualFunctor.map_smul r fb

instance leftFiniteDimensionalVectorDualFunctorAdditive : A.leftFiniteDimensionalVectorDualFunctor.Additive where
  map_add := by
    intro M N f g
    let fb : op M.unop.obj ⟶ op N.unop.obj := (A.leftFiniteDimensionalProperty.ι.map f.unop).op
    let gb : op M.unop.obj ⟶ op N.unop.obj := (A.leftFiniteDimensionalProperty.ι.map g.unop).op
    exact A.leftModuleVectorDualFunctor.map_add (f := fb) (g := gb)
instance leftFiniteDimensionalVectorDualFunctorLinear : A.leftFiniteDimensionalVectorDualFunctor.Linear k where
  map_smul := by
    intro M N f r
    let fb : op M.unop.obj ⟶ op N.unop.obj := (A.leftFiniteDimensionalProperty.ι.map f.unop).op
    exact A.leftModuleVectorDualFunctor.map_smul r fb

noncomputable def leftFiniteDimensionalVectorDualEquivalence : A.LeftFiniteDimensionalᵒᵖ ≌ A.RightFiniteDimensional :=
  CategoryTheory.Equivalence.mk A.leftFiniteDimensionalVectorDualFunctor A.rightFiniteDimensionalVectorDualFunctor.rightOp
    (NatIso.op A.leftFiniteDimensionalVectorBidualNatIso) A.rightFiniteDimensionalVectorBidualNatIso

end ASGinzburg.ZAlgebra
