import ASGinzburg.AlgebraEnvelopingTensorAugmentationRestriction

/-! Two genuine ordinary module resolutions tensor to a genuine right
enveloping-module resolution. The augmentation is proved acyclic by the
canonical total comparison, vector-space homotopy contraction, and exact,
faithful scalar restriction; no acyclicity assumption is added. -/
namespace ASGinzburg
open CategoryTheory HomologicalComplex
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {M : ModuleCat.{w} Rᵐᵒᵖ} {N : ModuleCat.{z} R}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)

theorem tensorRightEnvelopingAugmentation_quasiIso :
    QuasiIso (tensorRightEnvelopingAugmentation k R P Q) := by
  let G := ModuleCat.restrictScalars (algebraMap k (AlgebraEnvelopingRing k R)ᵐᵒᵖ)
  letI : G.ReflectsIsomorphisms := by
    constructor
    intro X Y f hf
    letI := hf
    letI : IsIso ((CategoryTheory.forget (ModuleCat (AlgebraEnvelopingRing k R)ᵐᵒᵖ)).map f) := by
      change IsIso ((CategoryTheory.forget (ModuleCat k)).map (G.map f))
      infer_instance
    exact isIso_of_reflects_iso f (CategoryTheory.forget (ModuleCat (AlgebraEnvelopingRing k R)ᵐᵒᵖ))
  apply (quasiIso_map_iff_of_preservesHomology
    (tensorRightEnvelopingAugmentation k R P Q) G).mp
  let a := (G.mapHomologicalComplex (ComplexShape.down ℕ)).map
    (tensorRightEnvelopingAugmentation k R P Q)
  let s := (singleMapHomologicalComplex G (ComplexShape.down ℕ) 0).app
    (((tensorRightEnvelopingBifunctor k R).obj M).obj N)
  let t := (ChainComplex.single₀ (ModuleCat.{max w z} k)).mapIso
    (tensorRightEnvelopingRestrictScalarsIso k R M N)
  let b := s.hom ≫ t.hom
  letI : IsIso b := by dsimp [b]; infer_instance
  letI : QuasiIso (a ≫ b) := by
    change QuasiIso ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (tensorRightEnvelopingAugmentation k R P Q) ≫
      (singleMapHomologicalComplex G (ComplexShape.down ℕ) 0).hom.app
        (((tensorRightEnvelopingBifunctor k R).obj M).obj N) ≫
      (ChainComplex.single₀ (ModuleCat.{max w z} k)).map
        (tensorRightEnvelopingRestrictScalarsIso k R M N).hom)
    rw [tensorRightEnvelopingAugmentation_restrictScalars]
    infer_instance
  exact quasiIso_of_comp_right a b

variable [Small.{w} Rᵐᵒᵖ] [Small.{z} R]

noncomputable def tensorRightEnvelopingResolution :
    ProjectiveResolution (((tensorRightEnvelopingBifunctor k R).obj M).obj N) where
  complex := tensorRightEnvelopingTotal k R P.complex Q.complex (ComplexShape.down ℕ)
  π := tensorRightEnvelopingAugmentation k R P Q
  projective n := by
    letI : ∀ i, Module.Projective Rᵐᵒᵖ (P.complex.X i) := fun i => by
      letI := P.projective i
      infer_instance
    letI : ∀ i, Module.Projective R (Q.complex.X i) := fun i => by
      letI := Q.projective i
      infer_instance
    exact tensorRightEnvelopingTotal_projective k R P.complex Q.complex (ComplexShape.down ℕ) n
  quasiIso := tensorRightEnvelopingAugmentation_quasiIso k R P Q

theorem tensorRightEnvelopingResolution_finite
    [∀ i, Module.Finite Rᵐᵒᵖ (P.complex.X i)] [∀ i, Module.Finite R (Q.complex.X i)] (n : ℕ) :
    Module.Finite (AlgebraEnvelopingRing k R)ᵐᵒᵖ
      ((tensorRightEnvelopingResolution k R P Q).complex.X n) :=
  tensorRightEnvelopingTotal_finite k R P.complex Q.complex n

end ASGinzburg
