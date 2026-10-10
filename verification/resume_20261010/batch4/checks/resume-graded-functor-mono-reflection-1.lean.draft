import work.ASGinzburgDraft.ProjectiveEpiKernelPreservation
import ASGinzburg.GradedOrdinaryKernelData

/-! A bounded graded zero detector reflects monicity for an actual
epimorphism onto a projective module, using its preserved split kernel. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v w z
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {S : Type w} [Ring S] {A : ℤ → Submodule k R} {b : ℤ}
variable (F : ModuleCat.{v} R ⥤ ModuleCat.{z} S) [F.Additive]

theorem gradedProjectiveEpi_mono_of_functor_mono
    (hDetect : ∀ N : GradedOrdinaryModuleData k R A, N.BoundedBelow b →
      IsZero (F.obj N.ringModule) → IsZero N.ringModule)
    (M N : GradedOrdinaryModuleData k R A) (hb : M.BoundedBelow b)
    (g : M.ringModule ⟶ N.ringModule) (hg : M.PreservesGrade N g)
    [Epi g] [Projective N.ringModule] [Mono (F.map g)] : Mono g := by
  letI := additiveFunctor_preserves_projective_epi_kernel F g
  have hTK : IsZero (F.obj (kernel g)) :=
    (PreservesKernel.iso F g).isZero_iff.mpr (isZero_kernel_of_mono (F.map g))
  have hT : IsZero (F.obj (M.kernelModule N g)) :=
    (F.mapIso (M.kernelIsoKernelModule N g)).isZero_iff.mp hTK
  have hK : IsZero (M.kernelModule N g) :=
    hDetect (M.kernelData N g hg) (M.kernelData_boundedBelow N g hg b hb) hT
  have hZero : IsZero (kernel g) := (M.kernelIsoKernelModule N g).isZero_iff.mpr hK
  exact CategoryTheory.Abelian.mono_of_kernel_ι_eq_zero g
    (hZero.eq_of_src (kernel.ι g) 0)

end ASGinzburg
