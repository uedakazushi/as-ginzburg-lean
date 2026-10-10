import ASGinzburg.FourTermProjectiveResolution
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.Finiteness.Basic

/-! Four actual finite, projective module objects and a genuine exact
resolution. Finiteness refers to their original ring action. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {R : Type u} [Ring R] {X : ModuleCat.{v} R}

/-- A four-term projective resolution whose four objects are finitely
generated over the actual coefficient ring. -/
structure FiniteFourTermProjectiveResolution (X : ModuleCat.{v} R)
    extends FourTermProjectiveResolution X where
  finite₀ : Module.Finite R P₀
  finite₁ : Module.Finite R P₁
  finite₂ : Module.Finite R P₂
  finite₃ : Module.Finite R P₃

namespace FiniteFourTermProjectiveResolution
variable (F : FiniteFourTermProjectiveResolution X)

theorem term_finite (n : ℕ) :
    Module.Finite R (F.toFourTermProjectiveResolution.term n) := by
  rcases n with _ | _ | _ | _ | n
  · exact F.finite₀
  · exact F.finite₁
  · exact F.finite₂
  · exact F.finite₃
  · letI : Subsingleton (F.toFourTermProjectiveResolution.term (n+4)) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_zero (ModuleCat R))
    infer_instance

noncomputable def toProjectiveResolution : ProjectiveResolution X :=
  F.toFourTermProjectiveResolution.toProjectiveResolution

theorem toProjectiveResolution_term_finite (n : ℕ) :
    Module.Finite R (F.toProjectiveResolution.complex.X n) :=
  F.term_finite n

theorem toProjectiveResolution_isZero_ge_four (n : ℕ) :
    IsZero (F.toProjectiveResolution.complex.X (n+4)) :=
  F.toFourTermProjectiveResolution.complex_isZero_ge_four n

end FiniteFourTermProjectiveResolution
end ASGinzburg
