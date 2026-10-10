import ASGinzburg.PeriodCutRegularLeftProducts
import ASGinzburg.PeriodCutRegularBiproduct

/-! Actual left multiplication by a vertex idempotent is precisely the
vertex projection followed by inclusion in the proved regular biproduct. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cutRegularVertexLeftMap (i : Q.Vertex) (t : ℤ) :
    E.cutRegularLeftHomogeneousMap Q 0
      (E.cutMatrixComponent (fun t : Q.Vertex => (t.val:ℤ)) 0 i i (E.cutGradedId (i.val:ℤ))) t ≫
        eqToHom (congrArg (fun q => (E.cutRegularGradedRightModule Q).shifted q) (add_zero t))=
      E.cutRegularRepresentableProjection Q t i ≫ E.cutRegularRepresentableInclusion Q t i := by
  apply Subtype.ext
  change (eqToHom (congrArg (fun q => (E.cutRegularGradedRightModule Q).shifted q)
    (add_zero t))).val.comp
      (E.cutRegularLeftHomogeneousLinearMap Q 0
        (E.cutMatrixComponent (fun t : Q.Vertex => (t.val:ℤ)) 0 i i (E.cutGradedId (i.val:ℤ))))=
    (E.cornerRepresentableValueMap Q (i,t)).comp (E.cornerRepresentableActionMap Q (i,t))
  rw [CutGradedRightModule.shifted_eqToHom_val,LinearMap.id_comp]
  apply LinearMap.ext
  intro r
  change E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) i*r=
    E.cornerRepresentableValueMap Q (i,t) (E.cornerRepresentableActionMap Q (i,t) r)
  exact (E.cornerRepresentableValueMap_actionMap Q (i,t) r).symm
  all_goals omega

end ASGinzburg.ZAlgebra.PeriodIso
