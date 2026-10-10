import ASGinzburg.ProjectiveResolutionHomComplex
import ASGinzburg.LinearExtTransport

/-! The actual three successive connecting morphisms give a genuine
surjective field-linear map from the final Hom term to actual Ext-three. -/
namespace CategoryTheory.ProjectiveResolution
open CategoryTheory.Limits
universe u v t w
variable {k : Type t} [Field k] {C : Type u} [Category.{v} C]
  [Abelian C] [Linear k C] [HasDerivedCategory.{w} C] [HasExt.{v} C]
variable {X : C} (P : ProjectiveResolution X)
attribute [local instance] ASGinzburg.exactExtModule

noncomputable def homToActualExtThree (h₄ : IsZero (P.complex.X 4)) (N : C) :
    (P.complex.X 3 ⟶ N) →ₗ[k] Abelian.Ext.{v} X N 3 where
  toFun f := P.shortExact₀.extClass.comp
    (P.shortExact₁.extClass.comp
      ((P.shortExact₂ h₄).extClass.comp (Abelian.Ext.mk₀ f) (by rfl)) (by rfl)) (by rfl)
  map_add' f g := by
    rw [Abelian.Ext.mk₀_add, Abelian.Ext.comp_add, Abelian.Ext.comp_add, Abelian.Ext.comp_add]
  map_smul' c f := by
    rw [ASGinzburg.exactExt_mk₀_smul k, ASGinzburg.exactExt_comp_smul k,
      ASGinzburg.exactExt_comp_smul k, ASGinzburg.exactExt_comp_smul k]
    rfl

 theorem homToActualExtThree_surjective (h₄ : IsZero (P.complex.X 4)) (N : C) :
    Function.Surjective (P.homToActualExtThree (k := k) h₄ N) := by
  intro e
  obtain ⟨x,hx⟩ := Abelian.Ext.contravariant_sequence_exact₃ P.shortExact₀ N e
    (Abelian.Ext.eq_zero_of_projective _) (show 1+2=3 from rfl)
  obtain ⟨y,hy⟩ := Abelian.Ext.contravariant_sequence_exact₃ P.shortExact₁ N x
    (Abelian.Ext.eq_zero_of_projective _) (show 1+1=2 from rfl)
  obtain ⟨z,hz⟩ := Abelian.Ext.contravariant_sequence_exact₃ (P.shortExact₂ h₄) N y
    (Abelian.Ext.eq_zero_of_projective _) (show 1+0=1 from rfl)
  refine ⟨Abelian.Ext.homEquiv₀ z, ?_⟩
  change P.shortExact₀.extClass.comp
    (P.shortExact₁.extClass.comp
      ((P.shortExact₂ h₄).extClass.comp (Abelian.Ext.mk₀ (Abelian.Ext.homEquiv₀ z)) (by rfl)) (by rfl)) (by rfl) = e
  rw [Abelian.Ext.mk₀_homEquiv₀_apply, hz, hy, hx]

 theorem homToActualExtThree_boundary_eq_zero (h₄ : IsZero (P.complex.X 4))
    (N : C) (g : P.complex.X 2 ⟶ N) :
    P.homToActualExtThree (k := k) h₄ N (P.complex.d 3 2 ≫ g) = 0 := by
  change P.shortExact₀.extClass.comp
    (P.shortExact₁.extClass.comp
      ((P.shortExact₂ h₄).extClass.comp (Abelian.Ext.mk₀ (P.complex.d 3 2 ≫ g)) (by rfl)) (by rfl)) (by rfl) = 0
  rw [← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.comp_assoc_of_second_deg_zero,
    (P.shortExact₂ h₄).extClass_comp, Abelian.Ext.zero_comp,
    Abelian.Ext.comp_zero, Abelian.Ext.comp_zero]

end CategoryTheory.ProjectiveResolution
