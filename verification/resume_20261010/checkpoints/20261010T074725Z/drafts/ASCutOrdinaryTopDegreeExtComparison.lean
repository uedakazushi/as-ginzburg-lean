import work.ASGinzburgDraft.ASCutOrdinaryRegularTopQuotientFinite
import work.ASGinzburgDraft.OrdinaryRingDualTopExtIso
import ASGinzburg.ASCutRegularTopExt
import work.ASGinzburgDraft.OrdinaryRingDualCanonicalFieldStructures

/-! Actual internal top-degree maps to both graded and ordinary Ext,
using the genuine connecting maps of the original AS resolutions. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
attribute [local instance 2000] ordinaryRingDualExtStandardDerivedCategory
attribute [local instance 2500] ModuleCat.linearOverField
attribute [local instance] exactExtModule
attribute [local instance 4000] ordinaryRingDualUnbundledAddCommGroup

noncomputable def ASRegular.cutOrdinaryTopDegreeToGradedExt
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    (hAS.cutOrdinarySimpleResolutionTermData A Q i 3).ringDualGrade (-1) →ₗ[k]
      Abelian.Ext.{v} (hAS.cutGradedSimple A Q (i,0))
        (((hAS.periodIso A Q).cutRegularGradedRightModule Q).shifted (-1)) 3 := by
  let E := hAS.periodIso A Q
  let G := hAS.cutGradedSimpleProjectiveResolution A Q (i,0)
  let N := (E.cutRegularGradedRightModule Q).shifted (-1)
  letI := HasDerivedCategory.standard (E.CutGradedRightModule Q)
  let h₄ := hAS.cutGradedSimpleProjectiveResolution_isZero_ge_four A Q (i,0) 0
  let e := E.cutOrdinaryRingDualShiftedHomEquiv Q (G.complex.X 3) (-1)
  let T := G.homToActualExtThree (k := k) h₄ N
  exact { toFun := fun f => T (e f)
          map_add' := fun f g => by rw [e.map_add, T.map_add]
          map_smul' := fun c f => by rw [e.map_smul, T.map_smul]; rfl }

 theorem ASRegular.cutOrdinaryTopDegreeToGradedExt_surjective
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    Function.Surjective (hAS.cutOrdinaryTopDegreeToGradedExt A Q i) := by
  let E := hAS.periodIso A Q
  let G := hAS.cutGradedSimpleProjectiveResolution A Q (i,0)
  let N := (E.cutRegularGradedRightModule Q).shifted (-1)
  letI := HasDerivedCategory.standard (E.CutGradedRightModule Q)
  let h₄ := hAS.cutGradedSimpleProjectiveResolution_isZero_ge_four A Q (i,0) 0
  let e := E.cutOrdinaryRingDualShiftedHomEquiv Q (G.complex.X 3) (-1)
  intro z
  obtain ⟨f,hf⟩ := G.homToActualExtThree_surjective (k := k) h₄ N z
  refine ⟨e.symm f, ?_⟩
  change G.homToActualExtThree (k := k) h₄ N (e (e.symm f)) = z
  exact (congrArg (G.homToActualExtThree (k := k) h₄ N) (e.toEquiv.apply_symm_apply f)).trans hf

end ASGinzburg.ZAlgebra
