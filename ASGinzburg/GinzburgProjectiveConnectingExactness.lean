import ASGinzburg.GinzburgProjectiveConnectingMaps
import ASGinzburg.GinzburgGeneratorHomologyComplex

/-! The actual projective connecting morphisms compose to zero; genuine
Ginzburg regularity implies monicity and exactness in RightModule. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgLoopDualProjectiveComponent_comp (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgLoopDualProjectiveComponent k φ x v ≫
      Q.ginzburgDualOriginalProjectiveComponent k φ x v = 0 := by
  unfold ginzburgLoopDualProjectiveComponent ginzburgDualOriginalProjectiveComponent
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  rw [← Category.assoc (Q.ginzburgGeneratorLoopToDualHomology k φ x.1 v.1 (v.2-x.2))
    (Q.ginzburgGeneratorDualToOriginalHomology k φ x.1 v.1 (v.2-x.2)),
    ginzburgGeneratorLoopDualOriginal_comp]
  simp

noncomputable def ginzburgProjectiveConnectingComponentShortComplex (φ : Q.Potential k)
    (x v : Q.LiftVertex) : ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.mk (Q.ginzburgLoopDualProjectiveComponent k φ x v)
    (Q.ginzburgDualOriginalProjectiveComponent k φ x v)
    (Q.ginzburgLoopDualProjectiveComponent_comp k φ x v)

theorem GinzburgRegular.loopDualProjectiveComponent_mono {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (x v : Q.LiftVertex) :
    Mono (Q.ginzburgLoopDualProjectiveComponent k φ x v) := by
  unfold ginzburgLoopDualProjectiveComponent
  haveI := h.loopToDualHomology_mono Q k x.1 v.1 (v.2-x.2)
  infer_instance

theorem GinzburgRegular.projectiveConnectingComponentShortComplex_exact {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (x v : Q.LiftVertex) :
    (Q.ginzburgProjectiveConnectingComponentShortComplex k φ x v).Exact := by
  let S := ShortComplex.mk
    (Q.ginzburgGeneratorLoopToDualHomology k φ x.1 v.1 (v.2-x.2))
    (Q.ginzburgGeneratorDualToOriginalHomology k φ x.1 v.1 (v.2-x.2))
    (Q.ginzburgGeneratorLoopDualOriginal_comp k φ x.1 v.1 (v.2-x.2))
  have hs : S.Exact := by
    simpa only [S,ginzburgGeneratorDualToOriginalHomology,
      show (-1:ℤ)+1=0 by norm_num,ginzburgGeneratorLoopDualShortComplex] using
      h.loopDualShortComplex_exact Q k x.1 v.1 (v.2-x.2)
  apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    (Q.ginzburgLayerProjectiveComponentIso k φ x v (-2))
    (Q.ginzburgLayerProjectiveComponentIso k φ x v (-1))
    (Q.ginzburgUpperProjectiveComponentIso k φ x v)
    (S₁:=S) (S₂:=Q.ginzburgProjectiveConnectingComponentShortComplex k φ x v)
    (by simp [S,ginzburgProjectiveConnectingComponentShortComplex,
      ginzburgLoopDualProjectiveComponent])
    (by simp [S,ginzburgProjectiveConnectingComponentShortComplex,
      ginzburgDualOriginalProjectiveComponent]))).mp hs

theorem ginzburgLoopDualProjectiveMap_comp (φ : Q.Potential k) (v : Q.LiftVertex) :
    Q.ginzburgLoopDualProjectiveMap k φ v ≫
      Q.ginzburgDualOriginalProjectiveMap k φ v = 0 := by
  let A := Q.unrolledJacobianZAlgebra k φ
  apply A.rightModuleProperty.ι.map_injective
  apply NatTrans.ext
  funext X
  let x := Q.heightEquiv.symm X.unop.index
  have hx : Q.height x=X.unop.index := by
    rw [← Q.heightEquiv_apply]
    exact Q.heightEquiv.apply_symm_apply _
  have he := Q.ginzburgLoopDualProjectiveComponent_comp k φ x v
  rw [← ginzburgLoopDualProjectiveMap_component,← ginzburgDualOriginalProjectiveMap_component] at he
  change (Q.ginzburgLoopDualProjectiveMap k φ v).app X ≫
    (Q.ginzburgDualOriginalProjectiveMap k φ v).app X = 0
  change (Q.ginzburgLoopDualProjectiveMap k φ v).app (Opposite.op ⟨Q.height x⟩) ≫
    (Q.ginzburgDualOriginalProjectiveMap k φ v).app (Opposite.op ⟨Q.height x⟩) = 0 at he
  rw [hx] at he
  exact he

noncomputable def ginzburgProjectiveConnectingShortComplex (φ : Q.Potential k)
    (v : Q.LiftVertex) : ShortComplex (Q.unrolledJacobianZAlgebra k φ).RightModule :=
  ShortComplex.mk (Q.ginzburgLoopDualProjectiveMap k φ v)
    (Q.ginzburgDualOriginalProjectiveMap k φ v)
    (Q.ginzburgLoopDualProjectiveMap_comp k φ v)

theorem GinzburgRegular.loopDualProjectiveMap_mono {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    Mono (Q.ginzburgLoopDualProjectiveMap k φ v) := by
  apply ((Q.unrolledJacobianZAlgebra k φ).rightModule_mono_iff _).mpr
  intro i
  let x := Q.heightEquiv.symm i
  have hx : Q.height x=i := by
    rw [← Q.heightEquiv_apply]
    exact Q.heightEquiv.apply_symm_apply i
  rw [← hx,ginzburgLoopDualProjectiveMap_component]
  exact h.loopDualProjectiveComponent_mono Q k x v

theorem GinzburgRegular.projectiveConnectingShortComplex_exact {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    (Q.ginzburgProjectiveConnectingShortComplex k φ v).Exact := by
  apply ((Q.unrolledJacobianZAlgebra k φ).rightModule_exact_iff _).mpr
  intro i
  let x := Q.heightEquiv.symm i
  have hx : Q.height x=i := by
    rw [← Q.heightEquiv_apply]
    exact Q.heightEquiv.apply_symm_apply i
  rw [← hx]
  simpa only [ginzburgProjectiveConnectingShortComplex,ShortComplex.map,
    ginzburgLoopDualProjectiveMap_component,ginzburgDualOriginalProjectiveMap_component,
    ginzburgProjectiveConnectingComponentShortComplex] using
    h.projectiveConnectingComponentShortComplex_exact Q k x v

end ASGinzburg.CutQuiver
