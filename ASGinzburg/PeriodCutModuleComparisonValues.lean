import ASGinzburg.PeriodCutModuleObjectComparison

/-! At a coordinate object the actual component comparison is the canonical inclusion. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cornerComponentEquiv_transport_val
    (M : (E.cornerCoverZAlgebra Q).RightModule) (x y : Q.LiftVertex) (hxy : x=y)
    (h : op (E.cornerCoordinateObject Q x)=op (E.cornerCoordinateObject Q y))
    (v : E.CornerModuleSpace Q M x) :
    (E.cornerComponentEquiv Q M y ((M.obj.mapIso (eqToIso h)).toLinearEquiv v)).val=
      DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x v := by
  subst y
  have hh : h=rfl := Subsingleton.elim _ _
  rw [hh]
  simp only [eqToIso_refl,Functor.mapIso_refl]
  rfl

theorem cornerAtObjectEquiv_coordinate_val
    (M : (E.cornerCoverZAlgebra Q).RightModule) (x : Q.LiftVertex)
    (v : E.CornerModuleSpace Q M x) :
    (E.cornerAtObjectEquiv Q M (E.cornerCoordinateObject Q x) v).val=
      DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x v := by
  dsimp only [cornerAtObjectEquiv,LinearEquiv.trans_apply,cornerCoordinateObject]
  exact E.cornerComponentEquiv_transport_val Q M x
    (Q.heightEquiv.symm (Q.heightEquiv x)) (Q.heightEquiv.symm_apply_apply x).symm _ v

end ASGinzburg.ZAlgebra.PeriodIso
