import ASGinzburg.FiniteProjectiveDuality
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Finiteness.Basic

/-! The actual principal module R e of an idempotent is a finite projective
module, as a concrete retract of the regular module. These are the
projective summands used in homogeneous top-basis covers. -/
namespace ASGinzburg
open CategoryTheory
universe u
variable (R : Type u) [Ring R]

def principalIdempotentOperator (e : R) : R →ₗ[R] R :=
  (LinearMap.id : R →ₗ[R] R).smulRight e

def principalIdempotentModule (e : R) : ModuleCat.{u} R :=
  ModuleCat.of R (LinearMap.range (principalIdempotentOperator R e))

def principalIdempotentInclusion (e : R) : principalIdempotentModule R e ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom (LinearMap.range (principalIdempotentOperator R e)).subtype

def principalIdempotentProjection (e : R) : ModuleCat.of R R ⟶ principalIdempotentModule R e :=
  ModuleCat.ofHom (principalIdempotentOperator R e).rangeRestrict

theorem principalIdempotentProjection_retract (e : R) (he : e*e=e) :
    principalIdempotentInclusion R e ≫ principalIdempotentProjection R e = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨r, hr⟩ := x.property
  change x.val*e = x.val
  change r*e = x.val at hr
  rw [← hr, mul_assoc, he]

theorem principalIdempotentModule_projective (e : R) (he : e*e=e) :
    Projective (principalIdempotentModule R e) :=
  projective_of_retract {
    i := principalIdempotentInclusion R e
    r := principalIdempotentProjection R e
    retract := principalIdempotentProjection_retract R e he
  }

instance principalIdempotentModule_finite (e : R) :
    Module.Finite R (principalIdempotentModule R e) :=
  Module.Finite.range (principalIdempotentOperator R e)

def principalIdempotentGenerator (e : R) : principalIdempotentModule R e :=
  ⟨e, ⟨1, one_mul e⟩⟩

theorem principalIdempotentModule_generator (e : R)
    (x : principalIdempotentModule R e) :
    ∃ r : R, r • principalIdempotentGenerator R e = x := by
  obtain ⟨r, hr⟩ := x.property
  exact ⟨r, Subtype.ext hr⟩

end ASGinzburg
