import ASGinzburg.RightModuleExt

/-! An actual isomorphism of augmentation targets retargets a genuine
mathlib projective resolution without changing any differential. -/
namespace ASGinzburg
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

noncomputable def projectiveResolutionTargetIso {X Y : C} (P : ProjectiveResolution X)
    (e : X ≅ Y) : ProjectiveResolution Y where
  complex := P.complex
  projective := P.projective
  π := P.π ≫ (ChainComplex.single₀ C).map e.hom
  quasiIso := by infer_instance

end ASGinzburg
