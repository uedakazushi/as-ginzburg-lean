import ASGinzburg.ZAlgebraRightModuleVertexExt
import ASGinzburg.ASCutCornerCoverRecovery
import ASGinzburg.ASDualityDimension

/-! The original AS assumptions give the exact vertex Ext table on the
actual R corner cover. No Ext table is added as an assumption. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutCornerVertexExtLinearEquiv (hAS : A.ASRegular Q)
    (i j : ℤ) (n : ℕ) :
    CategoryTheory.Abelian.Ext.{v} ((hAS.cutCornerCover A Q).simpleRightModule i)
      ((hAS.cutCornerCover A Q).representable j) n ≃ₗ[k]
        CategoryTheory.Abelian.Ext.{v} (A.simpleRightModule i) (A.representable j) n :=
  (hAS.cutCornerCoverRecovery A Q).vertexExtLinearEquiv i j n

theorem ASRegular.cutCornerAsExtTotalRank (hAS : A.ASRegular Q) (v : Q.LiftVertex) :
    (hAS.cutCornerCover A Q).asExtTotalRank Q v=1 :=
  ((hAS.cutCornerCoverRecovery A Q).asExtTotalRank_eq Q v).trans (hAS.2 v)

noncomputable def ASRegular.cutCornerExtThreeEquiv (hAS : A.ASRegular Q)
    (v : Q.LiftVertex) :
    CategoryTheory.Abelian.Ext.{v}
      ((hAS.cutCornerCover A Q).simpleRightModule (Q.height (Q.tau v)))
      ((hAS.cutCornerCover A Q).representable (Q.height v)) 3 ≃ₗ[k] k :=
  (hAS.cutCornerVertexExtLinearEquiv A Q _ _ 3).trans (hAS.extThreeEquiv A Q v)

theorem ASRegular.cutCornerExt_other_eq_zero (hAS : A.ASRegular Q)
    (v w : Q.LiftVertex) (n : ℕ) (hne : (n,w)≠(3,Q.tau v))
    (e : CategoryTheory.Abelian.Ext.{v}
      ((hAS.cutCornerCover A Q).simpleRightModule (Q.height w))
      ((hAS.cutCornerCover A Q).representable (Q.height v)) n) : e=0 := by
  apply (hAS.cutCornerVertexExtLinearEquiv A Q _ _ n).injective
  rw [map_zero]
  exact hAS.ext_other_eq_zero A Q v w n hne _

end ASGinzburg.ZAlgebra
