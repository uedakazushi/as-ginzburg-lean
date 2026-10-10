import ASGinzburg.EquivalenceProjectiveResolution

/-! A genuine projective resolution may change its augmentation target
along an actual isomorphism, retaining every resolution term. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]

noncomputable def projectiveResolutionChangeTarget {X Y : C}
    (P : ProjectiveResolution X) (e : X ≅ Y) : ProjectiveResolution Y where
  complex := P.complex
  projective := P.projective
  π := P.π ≫ (ChainComplex.single₀ C).map e.hom
  quasiIso := by infer_instance

end ASGinzburg
