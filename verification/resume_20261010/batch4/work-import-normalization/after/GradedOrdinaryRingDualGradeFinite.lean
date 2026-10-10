import ASGinzburg.GradedOrdinaryFiniteHomogeneousGenerators
import ASGinzburg.GradedOrdinaryRingDualComponentMaps
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Each actual homogeneous ring-dual component is finite dimensional
when the source is finitely generated and the ring grading is locally finite. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {G : ℤ → Submodule k R} (M : GradedOrdinaryModuleData k R G)

noncomputable def ringDualGradeEvaluation {I : Type v} (d : I → ℤ)
    (x : I → M.ringModule) (hx : ∀ i, x i ∈ M.grade (d i)) (q : ℤ) :
    M.ringDualGrade q →ₗ[k] (∀ i : I, G (d i + q)) where
  toFun f i := ⟨f.val (x i), f.property (d i) (x i) (hx i)⟩
  map_add' f g := by funext i; apply Subtype.ext; rfl
  map_smul' c f := by
    funext i
    apply Subtype.ext
    exact ordinaryRingDual_field_smul_apply M.ringModule c f.val (x i)

 theorem ringDualGradeEvaluation_injective {I : Type v} (d : I → ℤ)
    (x : I → M.ringModule) (hx : ∀ i, x i ∈ M.grade (d i))
    (hs : Submodule.span R (Set.range x) = ⊤) (q : ℤ) :
    Function.Injective (M.ringDualGradeEvaluation d x hx q) := by
  intro f g h
  apply Subtype.ext
  apply LinearMap.ext_on_range hs
  intro i
  exact congrArg Subtype.val (congrFun h i)

 theorem ringDualGrade_finite [Module.Finite R M.ringModule]
    [∀ q : ℤ, Module.Finite k (G q)] (q : ℤ) : Module.Finite k (M.ringDualGrade q) := by
  obtain ⟨I,hI,d,x,hx,hs⟩ := M.exists_finite_homogeneous_generating_family
  letI : Fintype I := hI
  exact Module.Finite.of_injective (M.ringDualGradeEvaluation d x hx q)
    (M.ringDualGradeEvaluation_injective d x hx hs q)

end ASGinzburg.GradedOrdinaryModuleData
