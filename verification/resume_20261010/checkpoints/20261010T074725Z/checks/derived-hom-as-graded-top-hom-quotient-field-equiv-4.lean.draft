import work.ASGinzburgDraft.ProjectiveResolutionTopExtHomQuotientIso
import ASGinzburg.ASCutRegularTopExt
import ASGinzburg.ASCutGradedResolutions
import work.ASGinzburgDraft.PeriodCutGradedHomCanonicalFieldStructures

/-! The genuine shifted regular final Hom quotient of the native AS
resolution is one copy of the field, through actual Ext-three. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
attribute [local instance 4000] PeriodIso.cutOrdinaryRingDualTopHomAddCommGroup
attribute [local instance 4000] PeriodIso.cutOrdinaryRingDualTopHomFieldModule
attribute [local instance] exactExtModule
universe u v
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutGradedRegularTopHomQuotientFieldEquiv
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    (((hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).complex.X 3 ⟶
        (((hAS.periodIso A Q).cutRegularGradedRightModule Q).shifted (-1))) ⧸
      LinearMap.range (Linear.leftComp k
        (((hAS.periodIso A Q).cutRegularGradedRightModule Q).shifted (-1))
        ((hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).complex.d 3 2))) ≃ₗ[k] k := by
  let E := hAS.periodIso A Q
  let G := hAS.cutGradedSimpleProjectiveResolution A Q (i,0)
  let N := (E.cutRegularGradedRightModule Q).shifted (-1)
  letI := HasDerivedCategory.standard (E.CutGradedRightModule Q)
  let h₄ := hAS.cutGradedSimpleProjectiveResolution_isZero_ge_four A Q (i,0) 0
  let e₁ : ((G.complex.X 3 ⟶ N) ⧸
      LinearMap.range (Linear.leftComp k N (G.complex.d 3 2))) ≃ₗ[k]
      Abelian.Ext.{v} (hAS.cutGradedSimple A Q (i,0)) N 3 :=
    G.topHomQuotientActualExtThreeLinearEquiv (k := k) h₄ N
  let e₂ : Abelian.Ext.{v} (hAS.cutGradedSimple A Q (i,0)) N 3 ≃ₗ[k] k :=
    hAS.cutGradedRegularTopExtEquiv A Q i
  exact e₁.trans e₂

end ASGinzburg.ZAlgebra
