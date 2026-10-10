import ASGinzburg.PeriodCornerTotalModuleMorphisms
import ASGinzburg.RightModuleHomology

/-! Genuine epimorphisms of directed cover modules are surjective on
the native cut total spaces, by their actual component maps. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cornerTotalModuleLinearMap_surjective_of_epi
    {P M : (E.cornerCoverZAlgebra Q).RightModule} (f : P ⟶ M) (hf : Epi f) :
    Function.Surjective (E.cornerTotalModuleLinearMap Q f) := by
  classical
  change Function.Surjective (DirectSum.lmap
    (fun z : Q.LiftVertex => (f.app (Opposite.op (E.cornerCoordinateObject Q z))).hom))
  apply (DirectSum.lmap_surjective _).mpr
  intro z
  exact (E.cornerCoverZAlgebra Q).rightModule_epi_iff_surjective f |>.mp hf (Q.heightEquiv z)

end ASGinzburg.ZAlgebra.PeriodIso
