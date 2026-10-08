import ASGinzburg.FiniteDimensionalAbelian
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

def rightModuleWindowProperty (l r : ℤ) : ObjectProperty A.RightModule :=
  fun M => ∀ i : ℤ, (i < l ∨ r < i) → IsZero ((A.rightModuleEvaluation i).obj M)

def rightFiniteWindowProperty (l r : ℤ) : ObjectProperty A.RightFiniteDimensional :=
  fun M => A.rightModuleWindowProperty l r M.obj
abbrev RightFiniteWindow (l r : ℤ) := (A.rightFiniteWindowProperty l r).FullSubcategory

theorem rightModuleWindow_of_mono {M N : A.RightModule} (f : M ⟶ N) [Mono f]
    {l r : ℤ} (hN : A.rightModuleWindowProperty l r N) : A.rightModuleWindowProperty l r M := by
  intro i hi
  exact (hN i hi).of_mono ((A.rightModuleEvaluation i).map f)

theorem rightModuleWindow_of_epi {M N : A.RightModule} (f : M ⟶ N) [Epi f]
    {l r : ℤ} (hM : A.rightModuleWindowProperty l r M) : A.rightModuleWindowProperty l r N := by
  intro i hi
  exact (hM i hi).of_epi ((A.rightModuleEvaluation i).map f)

theorem rightModuleWindow_of_shortExact {S : ShortComplex A.RightModule}
    (hS : S.ShortExact) {l r : ℤ} (h₁ : A.rightModuleWindowProperty l r S.X₁)
    (h₃ : A.rightModuleWindowProperty l r S.X₃) : A.rightModuleWindowProperty l r S.X₂ := by
  intro i hi
  have E := hS.exact.map (A.rightModuleEvaluation i)
  exact E.isZero_X₂ ((h₁ i hi).eq_zero_of_src _) ((h₃ i hi).eq_zero_of_tgt _)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
theorem rightFiniteWindowProperty_closedUnderLimits (l r : ℤ) (J : Type)
    [SmallCategory J] [FinCategory J] : ClosedUnderLimitsOfShape J (A.rightFiniteWindowProperty l r) := by
  intro F c hc hF i hi
  let E := A.rightFiniteDimensionalProperty.ι ⋙ A.rightModuleEvaluation i
  haveI : PreservesLimit F E := by dsimp [E]; infer_instance
  have hD : IsZero (F ⋙ E) := by
    rw [IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext j
    exact (hF j i hi).eq_of_src _ _
  exact (isLimitOfPreserves E hc).isZero_pt hD

attribute [-instance] ModuleCat.instHasLimitsOfSize in
theorem rightFiniteWindowProperty_closedUnderColimits (l r : ℤ) (J : Type)
    [SmallCategory J] [FinCategory J] : ClosedUnderColimitsOfShape J (A.rightFiniteWindowProperty l r) := by
  intro F c hc hF i hi
  let E := A.rightFiniteDimensionalProperty.ι ⋙ A.rightModuleEvaluation i
  haveI : PreservesColimit F E := by dsimp [E]; infer_instance
  have hD : IsZero (F ⋙ E) := by
    rw [IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext j
    exact (hF j i hi).eq_of_src _ _
  exact (isColimitOfPreserves E hc).isZero_pt hD

noncomputable instance rightFiniteWindowHasLimitsOfShape (l r : ℤ) (J : Type)
    [SmallCategory J] [FinCategory J] : HasLimitsOfShape J (A.RightFiniteWindow l r) :=
  hasLimitsOfShape_of_closedUnderLimits (A.rightFiniteWindowProperty_closedUnderLimits l r J)
noncomputable instance rightFiniteWindowHasColimitsOfShape (l r : ℤ) (J : Type)
    [SmallCategory J] [FinCategory J] : HasColimitsOfShape J (A.RightFiniteWindow l r) :=
  hasColimitsOfShape_of_closedUnderColimits (A.rightFiniteWindowProperty_closedUnderColimits l r J)
noncomputable instance rightFiniteWindowInclusionCreatesLimitsOfShape (l r : ℤ) (J : Type)
    [SmallCategory J] [FinCategory J] : CreatesLimitsOfShape J (A.rightFiniteWindowProperty l r).ι :=
  createsLimitsOfShapeFullSubcategoryInclusion (A.rightFiniteWindowProperty_closedUnderLimits l r J)
noncomputable instance rightFiniteWindowInclusionCreatesColimitsOfShape (l r : ℤ) (J : Type)
    [SmallCategory J] [FinCategory J] : CreatesColimitsOfShape J (A.rightFiniteWindowProperty l r).ι :=
  createsColimitsOfShapeFullSubcategoryInclusion (A.rightFiniteWindowProperty_closedUnderColimits l r J)
noncomputable instance rightFiniteWindowHasFiniteProducts (l r : ℤ) : HasFiniteProducts (A.RightFiniteWindow l r) where
  out _ := inferInstance

set_option maxHeartbeats 1600000 in
noncomputable instance rightFiniteWindowCoimageImageComparisonIsIso (l r : ℤ)
    {M N : A.RightFiniteWindow l r} (f : M ⟶ N) : IsIso (Abelian.coimageImageComparison f) := by
  haveI : IsIso ((A.rightFiniteWindowProperty l r).ι.map (Abelian.coimageImageComparison f)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso
      (Abelian.PreservesCoimageImageComparison.iso (A.rightFiniteWindowProperty l r).ι f).hom]
    infer_instance
  exact isIso_of_reflects_iso _ (A.rightFiniteWindowProperty l r).ι

noncomputable instance rightFiniteWindowAbelian (l r : ℤ) : Abelian (A.RightFiniteWindow l r) :=
  Abelian.ofCoimageImageComparisonIsIso
noncomputable instance rightFiniteWindowInclusionPreservesFiniteLimits (l r : ℤ) :
    PreservesFiniteLimits (A.rightFiniteWindowProperty l r).ι where
  preservesFiniteLimits _ := inferInstance
noncomputable instance rightFiniteWindowInclusionPreservesFiniteColimits (l r : ℤ) :
    PreservesFiniteColimits (A.rightFiniteWindowProperty l r).ι where
  preservesFiniteColimits _ := inferInstance

end ASGinzburg.ZAlgebra
