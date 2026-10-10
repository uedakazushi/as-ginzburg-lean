import work.ASGinzburgDraft.ProjectiveResolutionTopExtHomQuotient
import work.ASGinzburgDraft.ProjectiveResolutionTopExtKernel

/-! The genuine final Hom quotient is field-linearly isomorphic to
actual Ext-three through the actual long-exact-sequence map. -/
namespace CategoryTheory.ProjectiveResolution
open CategoryTheory.Limits
universe u v t w
variable {k : Type t} [Field k] {C : Type u} [Category.{v} C]
  [Abelian C] [Linear k C] [HasDerivedCategory.{w} C] [HasExt.{v} C]
variable {X : C} (P : ProjectiveResolution X)
attribute [local instance] ASGinzburg.exactExtModule

 theorem topHomQuotientToActualExtThree_injective (h₄ : IsZero (P.complex.X 4)) (N : C) :
    Function.Injective (P.topHomQuotientToActualExtThree (k := k) h₄ N) := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro z hz
  let B := LinearMap.range (P.homDifferential (k := k) N 2).hom
  obtain ⟨f,rfl⟩ := B.mkQ_surjective z
  have hf : P.homToActualExtThree (k := k) h₄ N f = 0 := hz
  obtain ⟨g,hg⟩ := (P.homToActualExtThree_eq_zero_iff (k := k) h₄ N f).mp hf
  exact (Submodule.Quotient.mk_eq_zero B).mpr ⟨g,hg⟩

noncomputable def topHomQuotientActualExtThreeLinearEquiv
    (h₄ : IsZero (P.complex.X 4)) (N : C) :
    ((P.complex.X 3 ⟶ N) ⧸ LinearMap.range (P.homDifferential (k := k) N 2).hom) ≃ₗ[k]
      Abelian.Ext.{v} X N 3 :=
  LinearEquiv.ofBijective (P.topHomQuotientToActualExtThree (k := k) h₄ N)
    ⟨P.topHomQuotientToActualExtThree_injective (k := k) h₄ N,
      P.topHomQuotientToActualExtThree_surjective (k := k) h₄ N⟩

end CategoryTheory.ProjectiveResolution
