import ASGinzburg.GradedOrdinaryKernelFactor
import ASGinzburg.ProjectiveEpiKernelPreservation
import ASGinzburg.ProjectiveResolutionSyzygies

/-! Under any additive functor the actual split kernel inclusion stays
monic, and replacing a differential by its kernel factor preserves the
preceding mapped exactness condition. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v w z
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {S : Type w} [Ring S] {A : ℤ → Submodule k R}
variable (F : ModuleCat.{v} R ⥤ ModuleCat.{z} S) [F.Additive]

theorem functor_kernelInclusion_mono (M N : GradedOrdinaryModuleData k R A)
    (g : M.ringModule ⟶ N.ringModule) [Epi g] [Projective N.ringModule] :
    Mono (F.map (M.kernelInclusion N g)) := by
  letI := additiveFunctor_preserves_projective_epi_kernel F g
  haveI : Mono (F.map (kernel.ι g)) := by
    rw [← kernelComparison_comp_ι g F]
    infer_instance
  change Mono (F.map (ModuleCat.ofHom (LinearMap.ker g.hom).subtype))
  rw [← ModuleCat.kernelIsoKer_inv_kernel_ι g,F.map_comp]
  infer_instance

theorem comp_kernelFactor_eq_zero
    (L P M N : GradedOrdinaryModuleData k R A)
    (q : L.ringModule ⟶ P.ringModule) (f : P.ringModule ⟶ M.ringModule)
    (g : M.ringModule ⟶ N.ringModule) (hqf : q ≫ f = 0) (hfg : f ≫ g = 0) :
    q ≫ P.kernelFactor M N f g hfg = 0 := by
  apply (cancel_mono (M.kernelInclusion N g)).mp
  rw [Category.assoc,P.kernelFactor_inclusion M N f g hfg,hqf,zero_comp]

theorem functor_exact_kernelFactor
    (L P M N : GradedOrdinaryModuleData k R A)
    (q : L.ringModule ⟶ P.ringModule) (f : P.ringModule ⟶ M.ringModule)
    (g : M.ringModule ⟶ N.ringModule) (hqf : q ≫ f = 0) (hfg : f ≫ g = 0)
    [Epi g] [Projective N.ringModule]
    (hExact : ((ShortComplex.mk q f hqf).map F).Exact) :
    ((ShortComplex.mk q (P.kernelFactor M N f g hfg)
      (comp_kernelFactor_eq_zero L P M N q f g hqf hfg)).map F).Exact := by
  letI := functor_kernelInclusion_mono F M N g
  have hEq : F.map (P.kernelFactor M N f g hfg) ≫ F.map (M.kernelInclusion N g) =
      F.map f := by
    rw [← F.map_comp,P.kernelFactor_inclusion M N f g hfg]
  apply (ASGinzburg.exact_comp_mono_iff (F.map q)
    (F.map (P.kernelFactor M N f g hfg)) (F.map (M.kernelInclusion N g)) _).mpr
  simpa only [hEq] using hExact

end ASGinzburg.GradedOrdinaryModuleData
