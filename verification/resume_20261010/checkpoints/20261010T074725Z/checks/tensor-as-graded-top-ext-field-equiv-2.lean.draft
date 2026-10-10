import ASGinzburg.ASCutRegularTopExt

/-! The genuine graded top Ext into the shifted regular module is one
copy of the field, from the original AS table and vertex decomposition. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
set_option maxHeartbeats 300000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutGradedRegularExt_top_evaluation
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    Abelian.Ext.{v} (hAS.cutGradedSimple A Q (i,0))
      (((hAS.periodIso A Q).cutRegularGradedRightModule Q).shifted (-1)) 3 →ₗ[k]
      Abelian.Ext.{v} (A.simpleRightModule (Q.height (i,0)))
        (A.representable (Q.height (i,-1))) 3 :=
  (LinearMap.proj i).comp (hAS.cutGradedRegularExtLinearEquiv A Q i 3 (-1)).toLinearMap

 theorem ASRegular.cutGradedRegularExt_top_evaluation_bijective
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    Function.Bijective (hAS.cutGradedRegularExt_top_evaluation A Q i) := by
  let e := hAS.cutGradedRegularExtLinearEquiv A Q i 3 (-1)
  let ev := hAS.cutRegularVertexTopExtEquiv A Q i
  change Function.Bijective (fun x => ev (e x))
  exact ev.bijective.comp e.bijective

noncomputable def ASRegular.cutGradedRegularTopExtFieldEquiv
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    Abelian.Ext.{v} (hAS.cutGradedSimple A Q (i,0))
      (((hAS.periodIso A Q).cutRegularGradedRightModule Q).shifted (-1)) 3 ≃ₗ[k] k :=
  hAS.cutGradedRegularTopExtEquiv A Q i

end ASGinzburg.ZAlgebra
