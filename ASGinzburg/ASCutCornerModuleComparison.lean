import ASGinzburg.ASCutCornerCoverRecovery
import ASGinzburg.ZAlgebraRightModuleExtEquivalence

/-! From the original AS assumptions, modules over the actual R corner
cover are linearly equivalent to original A modules, with actual Ext. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutCornerRightModuleEquivalence (hAS : A.ASRegular Q) :
    (hAS.cutCornerCover A Q).RightModule ≌ A.RightModule :=
  (hAS.cutCornerCoverRecovery A Q).rightModuleEquivalence

instance ASRegular.cutCornerRightModuleFunctorAdditive (hAS : A.ASRegular Q) :
    (hAS.cutCornerRightModuleEquivalence A Q).functor.Additive :=
  (hAS.cutCornerCoverRecovery A Q).rightModuleEquivalenceFunctorAdditive

instance ASRegular.cutCornerRightModuleFunctorLinear (hAS : A.ASRegular Q) :
    (hAS.cutCornerRightModuleEquivalence A Q).functor.Linear k :=
  (hAS.cutCornerCoverRecovery A Q).rightModuleEquivalenceFunctorLinear

instance ASRegular.cutCornerRightModuleInverseAdditive (hAS : A.ASRegular Q) :
    (hAS.cutCornerRightModuleEquivalence A Q).symm.functor.Additive :=
  (hAS.cutCornerCoverRecovery A Q).rightModuleEquivalenceInverseAdditive

noncomputable def ASRegular.cutCornerExtLinearEquiv (hAS : A.ASRegular Q)
    (M N : (hAS.cutCornerCover A Q).RightModule) (n : ℕ) :
    Abelian.Ext.{v} M N n ≃ₗ[k]
      Abelian.Ext.{v} ((hAS.cutCornerRightModuleEquivalence A Q).functor.obj M)
        ((hAS.cutCornerRightModuleEquivalence A Q).functor.obj N) n :=
  (hAS.cutCornerCoverRecovery A Q).rightModuleExtLinearEquiv M N n

noncomputable def ASRegular.cutCornerImageSimpleResolution (hAS : A.ASRegular Q)
    (v : Q.LiftVertex) :
    ProjectiveResolution ((hAS.cutCornerRightModuleEquivalence A Q).inverse.obj
      (A.simpleRightModule (Q.height v))) :=
  equivalenceProjectiveResolution (hAS.cutCornerRightModuleEquivalence A Q).symm
    (hAS.projectiveResolution A Q v)

theorem ASRegular.cutCornerImageSimpleResolution_isZero_ge_four (hAS : A.ASRegular Q)
    (v : Q.LiftVertex) (n : ℕ) :
    IsZero ((hAS.cutCornerImageSimpleResolution A Q v).complex.X (n+4)) :=
  equivalenceProjectiveResolution_isZero (hAS.cutCornerRightModuleEquivalence A Q).symm
    (hAS.projectiveResolution A Q v) (n+4)
      (hAS.projectiveResolution_isZero_ge_four A Q v n)

end ASGinzburg.ZAlgebra
