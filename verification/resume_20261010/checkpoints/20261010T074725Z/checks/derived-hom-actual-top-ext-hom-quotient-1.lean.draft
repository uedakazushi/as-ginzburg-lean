import work.ASGinzburgDraft.ProjectiveResolutionTopExtLinearMap
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The actual top Hom quotient maps surjectively to actual Ext-three,
so genuine finite-dimensionality of that quotient gives finite actual Ext. -/
namespace CategoryTheory.ProjectiveResolution
open CategoryTheory.Limits
universe u v t w
variable {k : Type t} [Field k] {C : Type u} [Category.{v} C]
  [Abelian C] [Linear k C] [HasDerivedCategory.{w} C] [HasExt.{v} C]
variable {X : C} (P : ProjectiveResolution X)
attribute [local instance] ASGinzburg.exactExtModule

noncomputable def topHomQuotientToActualExtThree (h₄ : IsZero (P.complex.X 4)) (N : C) :
    ((P.complex.X 3 ⟶ N) ⧸ LinearMap.range (P.homDifferential (k := k) N 2).hom) →ₗ[k]
      Abelian.Ext.{v} X N 3 :=
  (LinearMap.range (P.homDifferential (k := k) N 2).hom).liftQ
    (P.homToActualExtThree (k := k) h₄ N) (by
      rintro f ⟨g,rfl⟩
      exact LinearMap.mem_ker.mpr (P.homToActualExtThree_boundary_eq_zero h₄ N g))

 theorem topHomQuotientToActualExtThree_surjective (h₄ : IsZero (P.complex.X 4)) (N : C) :
    Function.Surjective (P.topHomQuotientToActualExtThree (k := k) h₄ N) := by
  intro e
  obtain ⟨f,hf⟩ := P.homToActualExtThree_surjective (k := k) h₄ N e
  refine ⟨(LinearMap.range (P.homDifferential (k := k) N 2).hom).mkQ f, ?_⟩
  exact hf

 theorem actualExtThree_finite_of_topHomQuotient_finite
    (h₄ : IsZero (P.complex.X 4)) (N : C)
    [Module.Finite k ((P.complex.X 3 ⟶ N) ⧸
      LinearMap.range (P.homDifferential (k := k) N 2).hom)] :
    Module.Finite k (Abelian.Ext.{v} X N 3) :=
  Module.Finite.of_surjective (P.topHomQuotientToActualExtThree (k := k) h₄ N)
    (P.topHomQuotientToActualExtThree_surjective (k := k) h₄ N)

end CategoryTheory.ProjectiveResolution
