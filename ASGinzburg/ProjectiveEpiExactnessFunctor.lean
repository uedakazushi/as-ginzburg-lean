import ASGinzburg.ProjectiveEpiKernelPreservation

/-! If a mapped complex is exact and its last map is an epimorphism
onto a projective, the mapped actual kernel factor is epimorphic. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type w} [Category.{z} D] [Abelian D]

theorem additiveFunctor_epi_kernel_lift_of_projective_epi
    (F : C ⥤ D) [F.Additive] {P M N : C}
    (f : P ⟶ M) (g : M ⟶ N) (hfg : f ≫ g = 0) [Epi g] [Projective N]
    (hExact : ((ShortComplex.mk f g hfg).map F).Exact) :
    Epi (F.map (kernel.lift g f hfg)) := by
  letI := additiveFunctor_preserves_projective_epi_kernel F g
  have hEq : F.map (kernel.lift g f hfg) ≫ kernelComparison g F =
      kernel.lift (F.map g) (F.map f) (by rw [← F.map_comp,hfg,F.map_zero]) := by
    apply (cancel_mono (kernel.ι (F.map g))).mp
    simp only [Category.assoc,kernelComparison_comp_ι,← F.map_comp,kernel.lift_ι]
  haveI : Epi (kernel.lift (F.map g) (F.map f)
      (by rw [← F.map_comp,hfg,F.map_zero])) :=
    (((ShortComplex.mk f g hfg).map F).exact_iff_epi_kernel_lift).mp hExact
  haveI : Epi (F.map (kernel.lift g f hfg) ≫ kernelComparison g F) := hEq ▸ inferInstance
  exact (epi_comp_iff_of_isIso (F.map (kernel.lift g f hfg))
    (kernelComparison g F)).mp inferInstance

end ASGinzburg
