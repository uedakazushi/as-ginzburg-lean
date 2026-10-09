import ASGinzburg.CyclicHessianReversal
import ASGinzburg.PathWordLastArrow

/-! Actual cyclic Hessian entries are supported on composable paths,
so they give actual path-valued linear maps on the original potential space. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem cyclicHessianWord_potential_mem (a b : Q.Arrow) (φ : Q.Potential k) :
    cyclicHessianWord a b φ.val ∈ Q.pathWordSpace k (Q.target a) (Q.source b) := by
  apply (Finsupp.mem_supported' k _).mpr
  intro w hw
  rw [cyclicHessianWord_apply]
  apply (Finsupp.mem_supported' k _).mp (Q.cyclicDerivative_potential_mem k a φ)
  rintro ⟨p,hp⟩
  obtain ⟨q,hq,_⟩ := p.exists_prefix_of_toList_append w b hp
  exact hw ⟨q,hq⟩

noncomputable def pathCyclicHessian (a b : Q.Arrow) :
    Q.Potential k →ₗ[k] Q.PathComponent k (Q.target a) (Q.source b) :=
  (Q.pathWordEquiv k (Q.target a) (Q.source b)).symm.toLinearMap.comp
    (((cyclicHessianWord a b).comp (Q.potentialSpace k).subtype).codRestrict
      (Q.pathWordSpace k (Q.target a) (Q.source b))
      (fun φ => Q.cyclicHessianWord_potential_mem k a b φ))

theorem pathWordMap_pathCyclicHessian (a b : Q.Arrow) (φ : Q.Potential k) :
    Q.pathWordMap k (Q.target a) (Q.source b) (Q.pathCyclicHessian k a b φ)=
      cyclicHessianWord a b φ.val := by
  rw [←Q.pathWordEquiv_coe]
  change ((Q.pathWordEquiv k (Q.target a) (Q.source b))
    ((Q.pathWordEquiv k (Q.target a) (Q.source b)).symm _)).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end ASGinzburg.CutQuiver
