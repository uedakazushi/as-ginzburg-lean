import ASGinzburg.PeriodCutGradedRightModules
import ASGinzburg.SimpleRightModules

/-! A cover vertex simple gives an actual one-dimensional total space.
This follows from the proved support of the genuine quotient simple. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cornerSimpleSpace_off (z x : Q.LiftVertex) (hx : x≠z) :
    Subsingleton (E.CornerModuleSpace Q
      ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)) x) := by
  apply ModuleCat.isZero_iff_subsingleton.mp
  change IsZero (((E.cornerCoverZAlgebra Q).rightModuleEvaluation (Q.heightEquiv x)).obj
    ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)))
  rw [Q.heightEquiv_apply]
  exact (E.cornerCoverZAlgebra Q).simpleRightModule_off_diagonal
    (Q.height z) (Q.height x) (fun h => hx (Q.height_bijective.injective h))

noncomputable def cornerSimpleTotalSpaceEquiv (z : Q.LiftVertex) :
    E.CornerModuleTotalSpace Q
        ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)) ≃ₗ[k]
      E.CornerModuleSpace Q
        ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)) z where
  toFun := DirectSum.component k Q.LiftVertex _ z
  invFun := DirectSum.lof k Q.LiftVertex _ z
  left_inv v := by
    apply DFinsupp.ext
    intro x
    by_cases hx : x=z
    · subst x
      simp only [DirectSum.lof_eq_of,DirectSum.of_eq_same,DirectSum.component]
      rfl
    · letI := E.cornerSimpleSpace_off Q z x hx
      exact Subsingleton.elim _ _
  right_inv v := by
    simp only [DirectSum.lof_eq_of,DirectSum.component]
    exact DFinsupp.single_eq_same
  map_add' := map_add (DirectSum.component k Q.LiftVertex _ z)
  map_smul' := map_smul (DirectSum.component k Q.LiftVertex _ z)

theorem cornerSimpleTotalSpace_finrank (z : Q.LiftVertex) :
    Module.finrank k (E.CornerModuleTotalSpace Q
      ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)))=1 := by
  rw [(E.cornerSimpleTotalSpaceEquiv Q z).finrank_eq]
  change Module.finrank k
    (((E.cornerCoverZAlgebra Q).rightModuleEvaluation (Q.heightEquiv z)).obj
      ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)))=1
  rw [Q.heightEquiv_apply]
  exact (E.cornerCoverZAlgebra Q).simpleRightModule_diagonal_finrank (Q.height z)

end ASGinzburg.ZAlgebra.PeriodIso
