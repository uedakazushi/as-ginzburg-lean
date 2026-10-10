import ASGinzburg.GradedOrdinaryKernelData
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! The actual factor through the concrete kernel inherits the grading;
its epimorphism condition is precisely actual exactness. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R}
variable (P M N : GradedOrdinaryModuleData k R A)
variable (f : P.ringModule ⟶ M.ringModule) (g : M.ringModule ⟶ N.ringModule)
variable (hfg : f ≫ g = 0)

def kernelFactor : P.ringModule ⟶ M.kernelModule N g :=
  ModuleCat.ofHom (f.hom.codRestrict (LinearMap.ker g.hom)
    (fun x => congrArg (fun t : P.ringModule ⟶ N.ringModule => t.hom x) hfg))

theorem kernelFactor_preservesGrade
    (hf : P.PreservesGrade M f) (hg : M.PreservesGrade N g) :
    P.PreservesGrade (M.kernelData N g hg) (P.kernelFactor M N f g hfg) :=
  fun q x hx => hf q x hx

theorem kernelFactor_inclusion :
    P.kernelFactor M N f g hfg ≫ M.kernelInclusion N g = f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem kernelFactor_epi_iff_exact :
    Epi (P.kernelFactor M N f g hfg) ↔ (ShortComplex.mk f g hfg).Exact := by
  rw [ModuleCat.epi_iff_surjective, ShortComplex.moduleCat_exact_iff]
  constructor
  · intro h x hx
    obtain ⟨y,hy⟩ := h ⟨x,hx⟩
    exact ⟨y,congrArg Subtype.val hy⟩
  · intro h x
    obtain ⟨y,hy⟩ := h x.val x.property
    exact ⟨y,Subtype.ext hy⟩

theorem kernelFactor_eq_kernel_lift :
    P.kernelFactor M N f g hfg =
      kernel.lift g f hfg ≫ (M.kernelIsoKernelModule N g).hom := by
  apply (cancel_mono (M.kernelInclusion N g)).mp
  rw [P.kernelFactor_inclusion M N f g hfg,Category.assoc,
    M.kernelIsoKernelModule_hom_inclusion N g,kernel.lift_ι]

end ASGinzburg.GradedOrdinaryModuleData
