import work.ASGinzburgDraft.PeriodCutOrdinaryCoverData
import work.ASGinzburgDraft.PeriodCutTotalMapSurjectivity

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
  (E.cutGradedForgetFunctor Q).map (E.cutNativeTopCoverπ Q N)

theorem cutNativeTopCoverOrdinaryπ_apply (N : E.CutGradedRightModule Q)
    (x : (E.cutNativeTopCoverSource Q N).ringModule) :
    E.cutNativeTopCoverOrdinaryπ Q N x = N.recoveredTotalEquiv
      (E.cornerTotalModuleLinearMap Q
        ((E.cornerCoverZAlgebra Q).rightTopBasisFreeModuleπ N.recoveredRightModule) x) := rfl

theorem cutNativeTopCoverOrdinaryπ_epi (N : E.CutGradedRightModule Q)
    (b : ℤ) (hb : ∀ q : ℤ, q < b → N.grade q = ⊥) :
    Epi (E.cutNativeTopCoverOrdinaryπ Q N) := by
  let f := (E.cornerCoverZAlgebra Q).rightTopBasisFreeModuleπ N.recoveredRightModule
  have hf : Epi f :=
    (E.cornerCoverZAlgebra Q).rightTopBasisFreeModuleπ_epi N.recoveredRightModule
      ((Q.vertices : ℤ) * (-b) + (Q.vertices : ℤ) - 1)
      (E.cutRecoveredRightModule_isZero_above_sharp_lower_bound Q N b hb)
  have hsurj := E.cornerTotalModuleLinearMap_surjective_of_epi Q f hf
  apply (ModuleCat.epi_iff_surjective (E.cutNativeTopCoverOrdinaryπ Q N)).mpr
  change Function.Surjective (fun x => N.recoveredTotalEquiv (E.cornerTotalModuleLinearMap Q f x))
  exact N.recoveredTotalEquiv.surjective.comp hsurj

end ASGinzburg.ZAlgebra.PeriodIso
