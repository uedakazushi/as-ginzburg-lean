import ASGinzburg.GradedOrdinaryKernelData
import ASGinzburg.ProjectiveSplitKernelFunctor

/-! The actual graded kernel of a projective epimorphism is projective. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R}

theorem kernelData_projective (M N : GradedOrdinaryModuleData k R A)
    (g : M.ringModule ⟶ N.ringModule) (hg : M.PreservesGrade N g)
    [Epi g] [Projective M.ringModule] [Projective N.ringModule] :
    Projective (M.kernelData N g hg).ringModule := by
  letI := projective_kernel_of_projective_epi g
  exact ASGinzburg.projective_of_retract
    (Retract.ofIso (M.kernelIsoKernelModule N g).symm)

end ASGinzburg.GradedOrdinaryModuleData
