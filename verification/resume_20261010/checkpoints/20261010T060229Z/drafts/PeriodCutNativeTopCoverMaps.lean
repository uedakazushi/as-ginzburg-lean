import ASGinzburg.PeriodCutGradedBoundedMinimalResolution
import ASGinzburg.PeriodCutForgetExactness

/-! The native top-basis cover maps to its actual native module before
any ordinary graded-data presentation is chosen. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

noncomputable def cutNativeTopCoverSource (N : E.CutGradedRightModule Q) :
    E.CutGradedRightModule Q :=
  E.cornerGradedRightModule Q ((E.cornerCoverZAlgebra Q).rightTopBasisFreeModule N.recoveredRightModule)

noncomputable def cutNativeTopCoverπ (N : E.CutGradedRightModule Q) :
    E.cutNativeTopCoverSource Q N ⟶ N :=
  E.cornerGradedModuleMap Q ((E.cornerCoverZAlgebra Q).rightTopBasisFreeModuleπ
    N.recoveredRightModule) ≫ N.recoveredGradedModuleIso.hom

noncomputable def cutNativeTopCoverOrdinaryπ (N : E.CutGradedRightModule Q) :
    (E.cutNativeTopCoverSource Q N).ringModule ⟶ N.ringModule :=
  (E.cornerModuleRingFunctor Q).map
    ((E.cornerCoverZAlgebra Q).rightTopBasisFreeModuleπ N.recoveredRightModule) ≫
      (E.cutGradedForgetFunctor Q).map N.recoveredGradedModuleIso.hom

theorem cutNativeTopCoverOrdinaryπ_epi (N : E.CutGradedRightModule Q)
    (b : ℤ) (hb : ∀ q : ℤ, q < b → N.grade q = ⊥) :
    Epi (E.cutNativeTopCoverOrdinaryπ Q N) := by
  let f := (E.cornerCoverZAlgebra Q).rightTopBasisFreeModuleπ N.recoveredRightModule
  have hf : Epi f :=
    (E.cornerCoverZAlgebra Q).rightTopBasisFreeModuleπ_epi N.recoveredRightModule
      ((Q.vertices : ℤ) * (-b) + (Q.vertices : ℤ))
      (N.recoveredRightModule_isZero_above_of_grade_lower_bound b hb)
  letI : Epi f := hf
  letI : Epi ((E.cornerModuleRingFunctor Q).map f) := inferInstance
  change Epi ((E.cornerModuleRingFunctor Q).map f ≫
    (E.cutGradedForgetFunctor Q).map N.recoveredGradedModuleIso.hom)
  infer_instance

end ASGinzburg.ZAlgebra.PeriodIso
