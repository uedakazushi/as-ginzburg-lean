import ASGinzburg.LiftedModuleIndexing
import ASGinzburg.RightModuleHomology

/-! Equality, monicity, epicity and exactness of existing right modules
are detected by their actual evaluations at all lifted-vertex heights. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem rightModuleHom_ext_lift {M N : A.RightModule} {f g : M ⟶ N}
    (h : ∀ x : Q.LiftVertex,
      (A.rightModuleEvaluation (Q.height x)).map f=(A.rightModuleEvaluation (Q.height x)).map g) :
    f=g := by
  apply A.rightModuleProperty.ι.map_injective
  apply NatTrans.ext
  funext X
  let x := Q.heightEquiv.symm X.unop.index
  have hx : Q.height x=X.unop.index := by
    rw [← Q.heightEquiv_apply]
    exact Q.heightEquiv.apply_symm_apply _
  have he := h x
  change f.hom.app (Opposite.op ⟨Q.height x⟩)=g.hom.app (Opposite.op ⟨Q.height x⟩) at he
  rw [hx] at he
  exact he

theorem rightModule_mono_iff_lift {M N : A.RightModule} (f : M ⟶ N) :
    Mono f ↔ ∀ x : Q.LiftVertex, Mono ((A.rightModuleEvaluation (Q.height x)).map f) := by
  rw [A.rightModule_mono_iff]
  constructor
  · intro h x; exact h (Q.height x)
  · intro h i
    let x := Q.heightEquiv.symm i
    have hx : Q.height x=i := by
      rw [← Q.heightEquiv_apply]
      exact Q.heightEquiv.apply_symm_apply _
    rw [← hx]
    exact h x

theorem rightModule_epi_iff_lift {M N : A.RightModule} (f : M ⟶ N) :
    Epi f ↔ ∀ x : Q.LiftVertex, Epi ((A.rightModuleEvaluation (Q.height x)).map f) := by
  rw [A.rightModule_epi_iff]
  constructor
  · intro h x; exact h (Q.height x)
  · intro h i
    let x := Q.heightEquiv.symm i
    have hx : Q.height x=i := by
      rw [← Q.heightEquiv_apply]
      exact Q.heightEquiv.apply_symm_apply _
    rw [← hx]
    exact h x

theorem rightModule_exact_iff_lift (S : ShortComplex A.RightModule) :
    S.Exact ↔ ∀ x : Q.LiftVertex, (S.map (A.rightModuleEvaluation (Q.height x))).Exact := by
  rw [A.rightModule_exact_iff]
  constructor
  · intro h x; exact h (Q.height x)
  · intro h i
    let x := Q.heightEquiv.symm i
    have hx : Q.height x=i := by
      rw [← Q.heightEquiv_apply]
      exact Q.heightEquiv.apply_symm_apply _
    rw [← hx]
    exact h x

end ASGinzburg.ZAlgebra
