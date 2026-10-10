import work.ASGinzburgDraft.GradedOrdinaryCokernelData
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! A cokernel-preserving functor that detects zero on actual bounded
ordinary graded modules reflects epimorphisms of grade-preserving maps.
The proof uses the genuine inherited cokernel grading. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v w z
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {S : Type w} [Ring S] {A : ℤ → Submodule k R} {b : ℤ}
variable (F : ModuleCat.{v} R ⥤ ModuleCat.{z} S) [F.Additive] [PreservesFiniteColimits F]

theorem gradedMap_epi_of_functor_epi
    (hDetect : ∀ N : GradedOrdinaryModuleData k R A, N.BoundedBelow b →
      IsZero (F.obj N.ringModule) → IsZero N.ringModule)
    (P M : GradedOrdinaryModuleData k R A) (hb : M.BoundedBelow b)
    (f : P.ringModule ⟶ M.ringModule) (hf : P.PreservesGrade M f)
    [Epi (F.map f)] : Epi f := by
  have hTC : IsZero (F.obj (cokernel f)) :=
    (PreservesCokernel.iso F f).isZero_iff.mpr (isZero_cokernel_of_epi (F.map f))
  have hT : IsZero (F.obj (P.cokernelModule M f)) :=
    (F.mapIso (P.cokernelIsoCokernelModule M f)).isZero_iff.mp hTC
  have hC : IsZero (P.cokernelModule M f) :=
    hDetect (P.cokernelData M f hf) (P.cokernelData_boundedBelow M f hf b hb) hT
  have hZero : IsZero (cokernel f) := (P.cokernelIsoCokernelModule M f).isZero_iff.mpr hC
  exact CategoryTheory.Abelian.epi_of_cokernel_π_eq_zero f
    (hZero.eq_of_tgt (cokernel.π f) 0)

end ASGinzburg
