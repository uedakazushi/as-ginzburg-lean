import ASGinzburg.SimpleRightModules

/-! An actual epimorphism from P_i onto a nonzero module supported at i
induces the canonical vertex simple, by its true radical/cokernel. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
variable (i : ℤ) (S : A.RightModule) (β : A.representable i⟶S)
variable (hoff : ∀ j : ℤ, j≠i → IsZero ((A.rightModuleEvaluation j).obj S))

include hoff in
theorem vertexPresentation_radical_zero : (A.representableRadical i).inclusion ≫ β=0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change β.app X x.val=0
  by_cases hxi : X.unop.index < i
  · haveI : Subsingleton (S.obj.obj X) :=
      ModuleCat.isZero_iff_subsingleton.mp (hoff X.unop.index (ne_of_lt hxi))
    exact Subsingleton.elim _ _
  · have hx : x.val=0 := by
      simpa only [representableRadical,if_neg hxi,Submodule.mem_bot] using x.property
    rw [hx,map_zero]

noncomputable def vertexPresentationDesc : A.simpleRightModule i⟶S :=
  cokernel.desc (A.representableRadical i).inclusion β
    (A.vertexPresentation_radical_zero i S β hoff)

theorem vertexPresentationDesc_fac : A.simpleRightModuleπ i ≫
    A.vertexPresentationDesc i S β hoff=β := cokernel.π_desc _ _ _

noncomputable def vertexPresentationIso [Epi β] (hβ : β≠0) : S≅A.simpleRightModule i := by
  let f := A.vertexPresentationDesc i S β hoff
  haveI : Epi (A.simpleRightModuleπ i ≫ f) := by
    rw [A.vertexPresentationDesc_fac]
    infer_instance
  haveI : Epi f := epi_of_epi (A.simpleRightModuleπ i) f
  have hf : f≠0 := by
    intro hf
    apply hβ
    rw [← A.vertexPresentationDesc_fac i S β hoff]
    change A.simpleRightModuleπ i ≫ f=0
    rw [hf,comp_zero]
  haveI : IsIso f := isIso_of_epi_of_nonzero hf
  exact (asIso f).symm

theorem vertexPresentationIso_fac [Epi β] (hβ : β≠0) :
    β ≫ (A.vertexPresentationIso i S β hoff hβ).hom=A.simpleRightModuleπ i := by
  calc
    _ = (A.simpleRightModuleπ i ≫ A.vertexPresentationDesc i S β hoff) ≫
        (A.vertexPresentationIso i S β hoff hβ).hom :=
      congrArg (fun t => t ≫ (A.vertexPresentationIso i S β hoff hβ).hom)
        (A.vertexPresentationDesc_fac i S β hoff).symm
    _ = _ := by
      change (A.simpleRightModuleπ i ≫ (A.vertexPresentationIso i S β hoff hβ).inv) ≫
        (A.vertexPresentationIso i S β hoff hβ).hom=A.simpleRightModuleπ i
      simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

end ASGinzburg.ZAlgebra
