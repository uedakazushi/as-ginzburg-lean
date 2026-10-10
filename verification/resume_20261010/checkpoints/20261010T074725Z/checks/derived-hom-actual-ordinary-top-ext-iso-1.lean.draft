import work.ASGinzburgDraft.OrdinaryRingDualTopExtFinite
import work.ASGinzburgDraft.OrdinaryRingDualTopQuotientType
import work.ASGinzburgDraft.ProjectiveResolutionTopExtKernel

/-! The actual raw ordinary ring-dual top cokernel is field-linearly
isomorphic to actual Ext-three via the genuine connecting maps. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {X : ModuleCat.{v} R} (P : ProjectiveResolution X)
attribute [local instance 2000] ordinaryRingDualExtStandardDerivedCategory
attribute [local instance 2500] ModuleCat.linearOverField
attribute [local instance 3000] ordinaryRingDualExtHomModule
attribute [local instance] exactExtModule

 theorem ordinaryRingDualToActualExtThree_eq_zero_iff (h₄ : IsZero (P.complex.X 4))
    (f : ordinaryRingDual R (P.complex.X 3)) :
    ordinaryRingDualToActualExtThree k R P h₄ f = 0 ↔
      ∃ g : ordinaryRingDual R (P.complex.X 2), ordinaryRingDualMap R (P.complex.d 3 2) g = f := by
  constructor
  · intro hf
    obtain ⟨g,hg⟩ := (P.homToActualExtThree_eq_zero_iff (k := k) h₄ (ModuleCat.of R R)
      (ordinaryRingDualCategoricalHomFieldEquiv k R (P.complex.X 3) f)).mp hf
    refine ⟨g.hom, ?_⟩
    exact congrArg ModuleCat.Hom.hom hg
  · rintro ⟨g,rfl⟩
    exact ordinaryRingDualToActualExtThree_boundary_eq_zero k R P h₄ g

 theorem ordinaryRingDualTopQuotientToActualExtThree_injective (h₄ : IsZero (P.complex.X 4)) :
    Function.Injective (ordinaryRingDualTopQuotientToActualExtThree k R P h₄) := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro z hz
  let B := LinearMap.range (ordinaryRingDualMapField (k := k) (P.complex.d 3 2))
  obtain ⟨f,rfl⟩ := B.mkQ_surjective z
  have hf : ordinaryRingDualToActualExtThree k R P h₄ f = 0 := hz
  obtain ⟨g,hg⟩ := (ordinaryRingDualToActualExtThree_eq_zero_iff k R P h₄ f).mp hf
  exact (Submodule.Quotient.mk_eq_zero B).mpr ⟨g,hg⟩

noncomputable def ordinaryRingDualTopActualExtThreeLinearEquiv (h₄ : IsZero (P.complex.X 4)) :
    ordinaryRingDualTopQuotient k R (P.complex.d 3 2) ≃ₗ[k]
      Abelian.Ext.{v} X (ModuleCat.of R R) 3 :=
  LinearEquiv.ofBijective (ordinaryRingDualTopQuotientToActualExtThree k R P h₄)
    ⟨ordinaryRingDualTopQuotientToActualExtThree_injective k R P h₄,
      ordinaryRingDualTopQuotientToActualExtThree_surjective k R P h₄⟩

end ASGinzburg
