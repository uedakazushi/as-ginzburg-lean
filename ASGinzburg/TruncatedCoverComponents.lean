import ASGinzburg.TruncatedRepresentableRestrictions

/-!
# The diagonal cover is an isomorphism and postcomposition is injective
-/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem simpleRightModuleπ_component_isIso (i : ℤ) :
    IsIso ((A.rightModuleEvaluation i).map (A.simpleRightModuleπ i)) := by
  have H := ((A.representableRadical i).quotientShortExact).map_of_exact (A.rightModuleEvaluation i)
  apply H.isIso_g_iff.mpr
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  apply Subtype.ext
  have hx : x.val = 0 := by simpa [representableRadical] using x.property
  have hy : y.val = 0 := by simpa [representableRadical] using y.property
  exact hx.trans hy.symm

theorem rightTruncatedRepresentableSimpleCover_component_isIso (l i : ℤ) (hli : l ≤ i) :
    IsIso ((A.rightModuleEvaluation i).map (A.rightTruncatedRepresentableSimpleCover l i hli)) := by
  let E := A.rightModuleEvaluation i
  letI := A.rightTruncatedRepresentableπ_component_isIso l i i hli
  letI := A.simpleRightModuleπ_component_isIso i
  have h : E.map (A.rightTruncatedRepresentableπ l i) ≫ E.map (A.rightTruncatedRepresentableSimpleCover l i hli) =
      E.map (A.simpleRightModuleπ i) := by
    rw [← E.map_comp,A.rightTruncatedRepresentableπ_simpleCover]
  have heq : E.map (A.rightTruncatedRepresentableSimpleCover l i hli) =
      inv (E.map (A.rightTruncatedRepresentableπ l i)) ≫ E.map (A.simpleRightModuleπ i) := by
    apply (cancel_epi (E.map (A.rightTruncatedRepresentableπ l i))).mp
    simpa using h
  rw [heq]
  infer_instance

theorem rightTruncatedRepresentable_postcomp_injective (l i : ℤ) {M N : A.RightModule}
    (hM : ∀ j, j < l → IsZero ((A.rightModuleEvaluation j).obj M))
    (hN : ∀ j, j < l → IsZero ((A.rightModuleEvaluation j).obj N))
    (g : M ⟶ N) [Mono ((A.rightModuleEvaluation i).map g)] :
    Function.Injective (fun f : A.rightTruncatedRepresentable l i ⟶ M => f ≫ g) := by
  intro f f' h
  apply (A.rightTruncatedRepresentableYonedaEquiv l i M hM).injective
  apply (ModuleCat.mono_iff_injective ((A.rightModuleEvaluation i).map g)).mp (by infer_instance)
  simpa only [A.rightTruncatedRepresentableYonedaEquiv_comp l i hM hN] using
    congrArg (A.rightTruncatedRepresentableYonedaEquiv l i N hN) h
end ASGinzburg.ZAlgebra
