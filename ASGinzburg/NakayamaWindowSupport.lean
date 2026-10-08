import ASGinzburg.FiniteDimensionalSimpleTranslation
import ASGinzburg.FiniteDimensionalWindowSequences

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def rightFiniteDimensionalNakayamaUnderlying (hAS : A.ASRegular Q)
    (M : A.RightModule) (hM : A.rightFiniteDimensionalProperty M) : A.RightModule :=
  ((A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.obj ⟨M,hM⟩).obj

theorem rightVertexFiltration_nakayama_window (hAS : A.ASRegular Q)
    {M : A.RightModule} (F : A.RightVertexFiltration M) :
    ∀ (hM : A.rightFiniteDimensionalProperty M) (l r : ℤ),
      A.rightModuleWindowProperty l r M →
        A.rightModuleWindowProperty (l-Q.vertices) (r-Q.vertices)
          (A.rightFiniteDimensionalNakayamaUnderlying Q hAS M hM) := by
  induction F with
  | zero hZero =>
    intro hM l r hW i hi
    have H := A.rightModuleExtLeft_isZero_of_isZero hZero 3
    exact A.leftModuleVectorDual_component_isZero _ i ((A.leftModuleEvaluation i).map_isZero H)
  | @step M i f hf tail ih =>
    intro hM l r hW
    letI := hf
    let S : ShortComplex A.RightModule := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
    have hC : A.rightFiniteDimensionalProperty (cokernel f) :=
      A.rightFiniteDimensional_of_epi (cokernel.π f) hM
    have hCW := A.rightModuleWindow_of_epi (cokernel.π f) hW
    obtain ⟨hli,hir⟩ := A.rightModuleWindow_vertex_of_mono hW f
    let T := A.rightFiniteDimensionalShortComplex S (A.rightFiniteDimensional_simple i) hM hC
    have hT : T.ShortExact := A.rightFiniteDimensionalShortComplex_shortExact hS _ _ _
    let E := (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor
    have H := (A.rightFiniteDimensionalNakayama_shortExact Q hAS hT).map_of_exact
      A.rightFiniteDimensionalProperty.ι
    have h₁ : A.rightModuleWindowProperty (l-Q.vertices) (r-Q.vertices)
        (A.rightFiniteDimensionalNakayamaUnderlying Q hAS (A.simpleRightModule i)
          (A.rightFiniteDimensional_simple i)) := by
      let e := A.rightFiniteDimensionalProperty.ι.mapIso
        (A.rightFiniteDimensionalNakayamaSimpleHeightIso Q hAS i)
      exact A.rightModuleWindow_of_mono e.hom
        (A.rightModuleWindow_simple _ _ _ (by omega) (by omega))
    exact A.rightModuleWindow_of_shortExact H h₁ (ih hC l r hCW)
theorem rightFiniteDimensional_nakayama_window (hAS : A.ASRegular Q)
    (M : A.RightModule) (hM : A.rightFiniteDimensionalProperty M) (l r : ℤ)
    (hW : A.rightModuleWindowProperty l r M) :
    A.rightModuleWindowProperty (l-Q.vertices) (r-Q.vertices)
      (A.rightFiniteDimensionalNakayamaUnderlying Q hAS M hM) :=
  A.rightVertexFiltration_nakayama_window Q hAS (A.rightFiniteDimensionalVertexFiltration M hM) hM l r hW
end ASGinzburg.ZAlgebra
