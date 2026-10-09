import ASGinzburg.PeriodCutGradedModuleEnrichment
import ASGinzburg.PeriodCutModuleMorphismActions

/-! The actual cut graded-module construction is a functor on cover modules. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cornerGradedModuleMap
    {M N : (E.cornerCoverZAlgebra Q).RightModule} (f : M⟶N) :
    E.cornerGradedRightModule Q M⟶E.cornerGradedRightModule Q N :=
  ⟨E.cornerTotalModuleLinearMap Q f,⟨
    fun r x => LinearMap.congr_fun (E.cutRightRepresentation_naturality Q f r) x,
    E.cornerTotalModuleLinearMap_mem_grade Q f⟩⟩

noncomputable def cornerGradedModuleFunctor :
    (E.cornerCoverZAlgebra Q).RightModule ⥤ E.CutGradedRightModule Q where
  obj := E.cornerGradedRightModule Q
  map := E.cornerGradedModuleMap Q
  map_id M := by
    apply Subtype.ext
    apply DFinsupp.lhom_ext
    intro x v
    change E.cornerTotalModuleLinearMap Q (𝟙 M)
      (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x v)=
        DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x v
    rw [E.cornerTotalModuleLinearMap_lof]
    rfl
  map_comp f g := by
    apply Subtype.ext
    apply DFinsupp.lhom_ext
    intro x v
    change E.cornerTotalModuleLinearMap Q (f≫g)
      (DirectSum.lof k Q.LiftVertex _ x v)=
      E.cornerTotalModuleLinearMap Q g
        (E.cornerTotalModuleLinearMap Q f (DirectSum.lof k Q.LiftVertex _ x v))
    rw [E.cornerTotalModuleLinearMap_lof,E.cornerTotalModuleLinearMap_lof,
      E.cornerTotalModuleLinearMap_lof]
    rfl

end ASGinzburg.ZAlgebra.PeriodIso
