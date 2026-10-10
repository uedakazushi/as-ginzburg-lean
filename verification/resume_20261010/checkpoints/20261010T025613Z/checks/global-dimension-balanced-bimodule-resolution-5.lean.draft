import work.ASGinzburgDraft.EnvelopingBalancedTensorProjectiveFunctor
import work.ASGinzburgDraft.EnvelopingBalancedTensorForgetComparison
import work.ASGinzburgDraft.AlgebraEnvelopingRestrictedRegular
import work.ASGinzburgDraft.ModuleCatRestrictionHomology
import work.ASGinzburgDraft.ProjectiveResolutionMapAfterRestriction

/-! Tensoring an actual enveloping projective resolution of R gives
an actual right-module projective resolution. Exactness follows by
restricting to left R, where R is projective, and tensoring the genuine
homotopy equivalence to its single-term resolution. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]

omit [IsScalarTower k Rᵐᵒᵖ M] in
theorem envelopingBalancedTensor_map_augmentation_quasiIso
    (Q : ProjectiveResolution (regularEnvelopingModuleCat k R)) :
    QuasiIso (((envelopingBalancedTensorRightFunctor.{u,v,w,v} k R M).mapHomologicalComplex
      (ComplexShape.down ℕ)).map Q.π) := by
  let F := envelopingBalancedTensorRightFunctor.{u,v,w,v} k R M
  let H := ModuleCat.restrictScalars.{max w v} (algebraMap k Rᵐᵒᵖ)
  let L := envelopingLeftRestrictionFunctor.{u,v,v} k R
  let G := balancedTensorRightFunctor.{u,v,w,v} k R M
  letI := moduleCatRestrictionPreservesHomology.{u,v,max w v} (algebraMap k Rᵐᵒᵖ)
  letI := moduleCatRestrictionReflectsIsomorphisms.{u,v,max w v} (algebraMap k Rᵐᵒᵖ)
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π) H).mp
  change QuasiIso (((F ⋙ H).mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π)
  let e := NatIso.mapHomologicalComplex
    (envelopingBalancedTensorForgetIso.{u,v,w,v} k R M) (ComplexShape.down ℕ)
  haveI : QuasiIso (((L ⋙ G).mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π) :=
    projectiveResolution_map_augmentation_after_restriction L G Q
  have h := e.hom.naturality Q.π
  haveI : QuasiIso ((((F ⋙ H).mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π) ≫
      e.hom.app ((ChainComplex.single₀ _).obj (regularEnvelopingModuleCat k R))) := by
    rw [h]
    infer_instance
  exact quasiIso_of_comp_right _
    (e.hom.app ((ChainComplex.single₀ _).obj (regularEnvelopingModuleCat k R)))

noncomputable def envelopingBalancedTensorProjectiveResolution
    (Q : ProjectiveResolution (regularEnvelopingModuleCat k R)) :
    ProjectiveResolution ((envelopingBalancedTensorRightFunctor.{u,v,w,v} k R M).obj
      (regularEnvelopingModuleCat k R)) where
  complex := ((envelopingBalancedTensorRightFunctor.{u,v,w,v} k R M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj Q.complex
  projective n := by
    change Projective ((envelopingBalancedTensorRightFunctor.{u,v,w,v} k R M).obj (Q.complex.X n))
    exact Functor.projective_obj_of_projective
      (envelopingBalancedTensorRightFunctor.{u,v,w,v} k R M) (Q.projective n)
  π := ((envelopingBalancedTensorRightFunctor.{u,v,w,v} k R M).mapHomologicalComplex
    (ComplexShape.down ℕ)).map Q.π ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (envelopingBalancedTensorRightFunctor.{u,v,w,v} k R M) (ComplexShape.down ℕ) 0).hom.app
        (regularEnvelopingModuleCat k R)
  quasiIso := by
    haveI := envelopingBalancedTensor_map_augmentation_quasiIso k R M Q
    infer_instance

end ASGinzburg
