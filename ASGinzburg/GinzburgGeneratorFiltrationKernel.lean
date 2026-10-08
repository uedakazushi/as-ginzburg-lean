import ASGinzburg.GinzburgGeneratorUpperFiltration

/-! The actual long exact sequence gives a monomorphism from the loop
layer onto the kernel of the next connecting map. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem GinzburgRegular.middleGeneratorQuotient_mono {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (c : ℤ) :
    Mono (Q.ginzburgGeneratorFilteredQuotientHomology k φ u v (-1) c (-1)) := by
  apply (Q.ginzburgGeneratorFiltrationHomology_exact₂ k φ u v (-1) c (-1)).mono_g
  exact (h.generatorFilteredZeroHomology_isZero Q k u v c (-1) (by norm_num)).eq_of_src _ _

noncomputable def ginzburgGeneratorLoopToDualHomology (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgAssociatedGradedHomology k φ u v (-2) c (-2) ⟶
      Q.ginzburgAssociatedGradedHomology k φ u v (-1) c (-1) := by
  have f : Q.ginzburgAssociatedGradedHomology k φ u v (-2) c (-2) ⟶
      Q.ginzburgGeneratorFilteredHomology k φ u v (-1) c (-1) :=
    Q.ginzburgGeneratorFiltrationConnecting k φ u v (-2) c (-2)
  exact f ≫ Q.ginzburgGeneratorFilteredQuotientHomology k φ u v (-1) c (-1)

theorem ginzburgGeneratorLoopToDualHomology_comp (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgGeneratorLoopToDualHomology k φ u v c ≫
      Q.ginzburgGeneratorFiltrationConnecting k φ u v (-1) c (-1)=0 := by
  unfold ginzburgGeneratorLoopToDualHomology
  rw [Category.assoc,Q.ginzburgGeneratorFilteredQuotientHomology_comp_connecting,
    comp_zero]

noncomputable def ginzburgGeneratorLoopDualShortComplex (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) : ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.mk (Q.ginzburgGeneratorLoopToDualHomology k φ u v c)
    (Q.ginzburgGeneratorFiltrationConnecting k φ u v (-1) c (-1))
    (Q.ginzburgGeneratorLoopToDualHomology_comp k φ u v c)

theorem GinzburgRegular.loopToDualHomology_mono {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (c : ℤ) :
    Mono (Q.ginzburgGeneratorLoopToDualHomology k φ u v c) := by
  letI := h.lowestGeneratorConnecting_isIso Q k u v c
  letI := h.middleGeneratorQuotient_mono Q k u v c
  exact mono_comp _ _

theorem GinzburgRegular.loopDualShortComplex_exact {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (c : ℤ) :
    (Q.ginzburgGeneratorLoopDualShortComplex k φ u v c).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  rcases (ShortComplex.moduleCat_exact_iff _).mp
    (Q.ginzburgGeneratorFiltrationHomology_exact₃ k φ u v (-1) c (-1)) x hx with ⟨y,hy⟩
  let e := h.lowestGeneratorConnectingIso Q k u v c
  refine ⟨e.inv y,?_⟩
  change Q.ginzburgGeneratorFilteredQuotientHomology k φ u v (-1) c (-1)
    (Q.ginzburgGeneratorFiltrationConnecting k φ u v (-2) c (-2) (e.inv y))=x
  have he : Q.ginzburgGeneratorFiltrationConnecting k φ u v (-2) c (-2) (e.inv y)=y := by
    change e.hom (e.inv y)=y
    simpa only [ModuleCat.comp_apply,ModuleCat.id_apply] using
      congrArg (fun f => f y) e.inv_hom_id
  rw [he]
  exact hy

noncomputable def GinzburgRegular.loopToDualHomology_isKernel {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (c : ℤ) :
    IsLimit (KernelFork.ofι (Q.ginzburgGeneratorLoopToDualHomology k φ u v c)
      (Q.ginzburgGeneratorLoopToDualHomology_comp k φ u v c)) := by
  letI := h.loopToDualHomology_mono Q k u v c
  haveI : Mono (Q.ginzburgGeneratorLoopDualShortComplex k φ u v c).f :=
    h.loopToDualHomology_mono Q k u v c
  exact (h.loopDualShortComplex_exact Q k u v c).fIsKernel

end ASGinzburg.CutQuiver
