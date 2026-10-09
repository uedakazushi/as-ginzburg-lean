import ASGinzburg.FoundationProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-! The actual foundation linear-module category has enough projectives
and genuine Hom-universe Ext, by explicit component element covers. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem foundation_epi_iff {M N : A.FoundationRightModule Q} (f : M ⟶ N) :
    Epi f ↔ ∀ i : Q.Vertex, Epi ((A.foundationRightEvaluation Q i).map f) := by
  constructor
  · intro h i
    letI := h
    infer_instance
  · intro h
    apply (linearPresheafProperty k (A.FoundationRightObj Q)).ι.epi_of_epi_map
    haveI : ∀ X, Epi (((linearPresheafProperty k (A.FoundationRightObj Q)).ι.map f).app X) :=
      fun X => h X
    exact NatTrans.epi_of_epi_app _

abbrev foundationGenerators (M : A.FoundationRightModule Q) :=
  Σ i : Q.Vertex, (A.foundationRightEvaluation Q i).obj M

noncomputable def foundationFreeRightModule (M : A.FoundationRightModule Q) :
    A.FoundationRightModule Q :=
  ∐ fun g : A.foundationGenerators Q M => A.foundationRepresentable Q g.1

noncomputable def foundationFreeRightModuleπ (M : A.FoundationRightModule Q) :
    A.foundationFreeRightModule Q M ⟶ M :=
  Sigma.desc (fun g => (A.foundationRepresentableYonedaEquiv Q g.1 M).symm g.2)

noncomputable instance foundationFreeRightModuleProjective (M : A.FoundationRightModule Q) :
    Projective (A.foundationFreeRightModule Q M) := by
  dsimp [foundationFreeRightModule]
  exact A.foundation_coproduct_projective Q _

noncomputable instance foundationFreeRightModuleπEpi (M : A.FoundationRightModule Q) :
    Epi (A.foundationFreeRightModuleπ Q M) := by
  apply (A.foundation_epi_iff Q _).mpr
  intro i
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro x
  let g : A.foundationGenerators Q M := ⟨i,x⟩
  refine ⟨(A.foundationRightEvaluation Q i).map
    (Sigma.ι (fun g : A.foundationGenerators Q M => A.foundationRepresentable Q g.1) g)
      (A.id (i.val : ℤ)),?_⟩
  have h := Sigma.ι_desc (fun g =>
    (A.foundationRepresentableYonedaEquiv Q g.1 M).symm g.2) g
  have h' := congrArg (A.foundationRepresentableYonedaEquiv Q i M) h
  rw [A.foundationRepresentableYonedaEquiv_comp,LinearEquiv.apply_symm_apply] at h'
  exact h'

noncomputable instance foundationEnoughProjectives : EnoughProjectives (A.FoundationRightModule Q) where
  presentation M := ⟨{ p := A.foundationFreeRightModule Q M
                       f := A.foundationFreeRightModuleπ Q M }⟩

instance foundationHasExt : HasExt.{v} (A.FoundationRightModule Q) :=
  hasExt_of_enoughProjectives (A.FoundationRightModule Q)

end ASGinzburg.ZAlgebra
