import ASGinzburg.NakayamaWindowSupport

/-!
# Inverse Nakayama translation of simples and interval support
-/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem rightFiniteDimensional_isZero_iff (M : A.RightFiniteDimensional) :
    IsZero M ↔ IsZero M.obj := by
  rw [IsZero.iff_id_eq_zero,IsZero.iff_id_eq_zero]
  rfl

instance rightFiniteDimensionalNakayamaInverseAdditive (hAS : A.ASRegular Q) :
    (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).inverse.Additive := by
  change (A.rightFiniteDimensionalVectorDualFunctor.rightOp ⋙
    A.leftFiniteDimensionalExtThreeFunctor Q hAS).Additive
  infer_instance

noncomputable def rightFiniteDimensionalSimpleVectorDualIso (i : ℤ) :
    A.rightFiniteDimensionalVectorDualFunctor.obj (op (A.rightFiniteDimensionalSimple i)) ≅
      A.leftFiniteDimensionalSimple i :=
  A.leftFiniteDimensionalProperty.isoMk (A.rightSimpleVectorDualIso i)

noncomputable def leftFiniteDimensionalExtThreeSimpleIso (hAS : A.ASRegular Q) (w : Q.LiftVertex) :
    (A.leftFiniteDimensionalExtThreeFunctor Q hAS).obj (op (A.leftFiniteDimensionalSimple (Q.height w))) ≅
      A.rightFiniteDimensionalSimple (Q.height (Q.tau w)) :=
  A.rightFiniteDimensionalProperty.isoMk (hAS.leftExtThreeIsoSimple A Q w)

noncomputable def rightFiniteDimensionalNakayamaInverseSimpleIso (hAS : A.ASRegular Q)
    (w : Q.LiftVertex) :
    (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).inverse.obj
        (A.rightFiniteDimensionalSimple (Q.height w)) ≅
      A.rightFiniteDimensionalSimple (Q.height (Q.tau w)) :=
  ((A.leftFiniteDimensionalExtThreeFunctor Q hAS).mapIso
    (A.rightFiniteDimensionalSimpleVectorDualIso (Q.height w)).op).symm ≪≫
      A.leftFiniteDimensionalExtThreeSimpleIso Q hAS w

noncomputable def rightFiniteDimensionalNakayamaInverseSimpleHeightIso (hAS : A.ASRegular Q)
    (i : ℤ) :
    (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).inverse.obj (A.rightFiniteDimensionalSimple i) ≅
      A.rightFiniteDimensionalSimple (i + Q.vertices) := by
  let w := Q.heightEquiv.symm i
  have hw : Q.height w = i := by
    rw [← Q.heightEquiv_apply]
    exact Q.heightEquiv.apply_symm_apply i
  simpa only [Q.height_tau,hw] using A.rightFiniteDimensionalNakayamaInverseSimpleIso Q hAS w

noncomputable def rightFiniteDimensionalNakayamaInverseUnderlying (hAS : A.ASRegular Q)
    (M : A.RightModule) (hM : A.rightFiniteDimensionalProperty M) : A.RightModule :=
  ((A.rightFiniteDimensionalNakayamaEquivalence Q hAS).inverse.obj ⟨M,hM⟩).obj

theorem rightVertexFiltration_nakayama_inverse_window (hAS : A.ASRegular Q)
    {M : A.RightModule} (F : A.RightVertexFiltration M) :
    ∀ (hM : A.rightFiniteDimensionalProperty M) (l r : ℤ),
      A.rightModuleWindowProperty l r M →
        A.rightModuleWindowProperty (l+Q.vertices) (r+Q.vertices)
          (A.rightFiniteDimensionalNakayamaInverseUnderlying Q hAS M hM) := by
  induction F with
  | @zero M hZero =>
    intro hM l r hW i hi
    have H := (A.rightFiniteDimensional_isZero_iff (⟨M,hM⟩ : A.RightFiniteDimensional)).mpr hZero
    have H' := (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).inverse.map_isZero H
    have H'' := A.rightFiniteDimensionalProperty.ι.map_isZero H'
    exact (A.rightModuleEvaluation i).map_isZero H''
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
    let E := (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).inverse
    have H := (hT.map_of_exact E).map_of_exact A.rightFiniteDimensionalProperty.ι
    have h₁ : A.rightModuleWindowProperty (l+Q.vertices) (r+Q.vertices)
        (A.rightFiniteDimensionalNakayamaInverseUnderlying Q hAS (A.simpleRightModule i)
          (A.rightFiniteDimensional_simple i)) := by
      let e := A.rightFiniteDimensionalProperty.ι.mapIso
        (A.rightFiniteDimensionalNakayamaInverseSimpleHeightIso Q hAS i)
      exact A.rightModuleWindow_of_mono e.hom
        (A.rightModuleWindow_simple _ _ _ (by omega) (by omega))
    exact A.rightModuleWindow_of_shortExact H h₁ (ih hC l r hCW)

theorem rightFiniteDimensional_nakayama_inverse_window (hAS : A.ASRegular Q)
    (M : A.RightModule) (hM : A.rightFiniteDimensionalProperty M) (l r : ℤ)
    (hW : A.rightModuleWindowProperty l r M) :
    A.rightModuleWindowProperty (l+Q.vertices) (r+Q.vertices)
      (A.rightFiniteDimensionalNakayamaInverseUnderlying Q hAS M hM) :=
  A.rightVertexFiltration_nakayama_inverse_window Q hAS
    (A.rightFiniteDimensionalVertexFiltration M hM) hM l r hW
end ASGinzburg.ZAlgebra
