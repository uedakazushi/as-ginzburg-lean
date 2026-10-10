import ASGinzburg.GradedFourTermExactnessReflection
import ASGinzburg.PeriodCutOrdinaryGradedNakayama
import ASGinzburg.BalancedTensorLeftAdjunction

/-! Genuine native semisimple reduction detects exactness of an actual
bounded graded four-term complex of projectives over the cut algebra. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))
local notation "R" => E.CutGradedRing (fun i : Q.Vertex => (Fin.val i:ℤ))
local notation "F" => balancedTensorLeftFunctor k R (R ⧸ E.cutGradedJacobson Q)

theorem cutGradedTensor_fourTerm_exact_reflect
    (P₀ P₁ P₂ P₃ : GradedOrdinaryModuleData k Rᵐᵒᵖ
      (E.cutIntegerOppositeHomogeneousSpace Q)) (b : ℤ)
    (hb₀ : P₀.BoundedBelow b) (hb₁ : P₁.BoundedBelow b)
    (hb₂ : P₂.BoundedBelow b) (hb₃ : P₃.BoundedBelow b)
    (f₀ : P₀.ringModule ⟶ P₁.ringModule)
    (f₁ : P₁.ringModule ⟶ P₂.ringModule)
    (f₂ : P₂.ringModule ⟶ P₃.ringModule)
    (h₀ : f₀ ≫ f₁ = 0) (h₁ : f₁ ≫ f₂ = 0)
    (hf₀ : P₀.PreservesGrade P₁ f₀) (hf₁ : P₁.PreservesGrade P₂ f₁)
    (hf₂ : P₂.PreservesGrade P₃ f₂)
    [Projective P₁.ringModule] [Projective P₂.ringModule] [Projective P₃.ringModule]
    [Mono ((F).map f₀)] [Epi ((F).map f₂)]
    (hF₀ : ((ShortComplex.mk f₀ f₁ h₀).map F).Exact)
    (hF₁ : ((ShortComplex.mk f₁ f₂ h₁).map F).Exact) :
    Mono f₀ ∧ (ShortComplex.mk f₀ f₁ h₀).Exact ∧
      (ShortComplex.mk f₁ f₂ h₁).Exact ∧ Epi f₂ := by
  have hDetect : ∀ N : GradedOrdinaryModuleData k Rᵐᵒᵖ
      (E.cutIntegerOppositeHomogeneousSpace Q), N.BoundedBelow b →
      IsZero ((F).obj N.ringModule) → IsZero N.ringModule :=
    fun N hN hT => E.ordinaryGradedData_isZero_of_tensor_semisimple Q N b hN hT
  exact gradedFourTerm_exact_of_functor_exact F hDetect P₀ P₁ P₂ P₃
    hb₀ hb₁ hb₂ hb₃ f₀ f₁ f₂ h₀ h₁ hf₀ hf₁ hf₂ hF₀ hF₁

end ASGinzburg.ZAlgebra.PeriodIso
