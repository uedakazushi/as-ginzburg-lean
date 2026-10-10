import ASGinzburg.AlgebraEnvelopingTensorAugmentation
import ASGinzburg.AlgebraEnvelopingTensorTotalRestrictionMaps
import ASGinzburg.ModuleFieldTensorResolution
import ASGinzburg.BifunctorTotalResolutionFormula

/-! The genuine enveloping total augmentation restricts to the actual
vector-space homotopy contraction, through canonical comparison maps. -/
namespace ASGinzburg
open CategoryTheory HomologicalComplex
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {M : ModuleCat.{w} Rᵐᵒᵖ} {N : ModuleCat.{z} R}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)

set_option backward.isDefEq.respectTransparency false in
theorem tensorRightEnvelopingAugmentation_restrictScalars :
    ((ModuleCat.restrictScalars (algebraMap k (AlgebraEnvelopingRing k R)ᵐᵒᵖ)).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (tensorRightEnvelopingAugmentation k R P Q) ≫
      (singleMapHomologicalComplex
        (ModuleCat.restrictScalars (algebraMap k (AlgebraEnvelopingRing k R)ᵐᵒᵖ))
        (ComplexShape.down ℕ) 0).hom.app
          (((tensorRightEnvelopingBifunctor k R).obj M).obj N) ≫
      (ChainComplex.single₀ (ModuleCat.{max w z} k)).map
        (tensorRightEnvelopingRestrictScalarsIso k R M N).hom =
    (tensorRightEnvelopingTotalRestrictScalarsIso k R P.complex Q.complex).hom ≫
      (moduleFieldTensorResolutionHomotopyEquiv k R P Q).hom := by
  let G := ModuleCat.restrictScalars (algebraMap k (AlgebraEnvelopingRing k R)ᵐᵒᵖ)
  let e := tensorRightEnvelopingTotalRestrictScalarsIso k R P.complex Q.complex
  let Pk := moduleFieldRestrictionResolution k Rᵐᵒᵖ P
  let Qk := moduleFieldRestrictionResolution k R Q
  letI := moduleCatField_projective k
    ((ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).obj M)
  letI := moduleCatField_projective k
    ((ModuleCat.restrictScalars (algebraMap k R)).obj N)
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change G.map ((tensorRightEnvelopingAugmentation k R P Q).f 0) ≫
      (tensorRightEnvelopingRestrictScalarsIso k R M N).hom =
    e.hom.f 0 ≫ (moduleFieldTensorResolutionHomotopyEquiv k R P Q).hom.f 0
  letI : IsIso (e.inv.f 0) := (HomologicalComplex.Hom.isoApp e 0).isIso_inv
  apply (cancel_epi (e.inv.f 0)).1
  have hi : e.inv.f 0 ≫ e.hom.f 0 = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun φ => φ.f 0) e.inv_hom_id
  simp only [← Category.assoc, hi, Category.id_comp]
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  have hzero : i = 0 ∧ j = 0 := by simpa using hij
  rcases hzero with ⟨rfl, rfl⟩
  have hh := bifunctorTotalResolutionHomotopyEquiv_ι_zero (moduleTensorBifunctor k) Pk Qk
  change ιMapBifunctor Pk.complex Qk.complex (moduleTensorBifunctor k)
      (ComplexShape.down ℕ) 0 0 0 (by simp) ≫
      (moduleFieldTensorResolutionHomotopyEquiv k R P Q).hom.f 0 = _ at hh
  simp only [← Category.assoc]
  rw [ι_tensorRightEnvelopingTotalRestrictScalarsIso_inv_f]
  simp only [Category.assoc]
  rw [← Category.assoc
    (G.map (ιMapBifunctor P.complex Q.complex (tensorRightEnvelopingBifunctor k R)
      (ComplexShape.down ℕ) 0 0 0 hij))
    (G.map ((tensorRightEnvelopingAugmentation k R P Q).f 0))
    (tensorRightEnvelopingRestrictScalarsIso k R M N).hom]
  rw [← G.map_comp, tensorRightEnvelopingAugmentation_ι_zero]
  change _ = ιMapBifunctor Pk.complex Qk.complex (moduleTensorBifunctor k)
    (ComplexShape.down ℕ) 0 0 0 hij ≫
      (moduleFieldTensorResolutionHomotopyEquiv k R P Q).hom.f 0
  rw [hh]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end ASGinzburg
