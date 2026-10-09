import ASGinzburg.RightModuleExt
import Mathlib.Algebra.Homology.Additive

/-! An additive actual equivalence transports a genuine mathlib projective
resolution, including its actual complex, augmentation and quasi-isomorphism. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe v w u u'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{w} D] [Abelian D]
variable (E : C ≌ D) [E.functor.Additive]

noncomputable def equivalenceProjectiveResolution {X : C} (P : ProjectiveResolution X) :
    ProjectiveResolution (E.functor.obj X) :=
  E.functor.mapProjectiveResolution P

theorem equivalenceProjectiveResolution_isZero {X : C} (P : ProjectiveResolution X) (n : ℕ)
    (h : IsZero (P.complex.X n)) :
    IsZero ((equivalenceProjectiveResolution E P).complex.X n) := by
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (E.functor.obj (P.complex.X n)) = 0
  rw [← E.functor.map_id, h.eq_of_src (𝟙 _) 0, E.functor.map_zero]

end ASGinzburg
