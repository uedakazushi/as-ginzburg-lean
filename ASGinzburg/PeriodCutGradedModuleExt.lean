import ASGinzburg.PeriodCutGradedModuleAbelian
import ASGinzburg.ExactEquivalenceExt
import ASGinzburg.RightModuleExtLinear

/-! Actual derived-category Ext is preserved in every degree by the
concrete cover-to-graded-R equivalence, including its k-linear structure. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable instance cutGradedModuleExtModule
    (M N : E.CutGradedRightModule Q) (n : ℕ) : Module k (Abelian.Ext.{v} M N n) := by
  letI := HasDerivedCategory.standard (E.CutGradedRightModule Q)
  exact ASGinzburg.exactExtModule k M N n

noncomputable def cornerGradedModuleExtAddEquiv
    (M N : (E.cornerCoverZAlgebra Q).RightModule) (n : ℕ) :
    Abelian.Ext.{v} M N n ≃+
      Abelian.Ext.{v} (E.cornerGradedRightModule Q M) (E.cornerGradedRightModule Q N) n := by
  letI := HasDerivedCategory.standard (E.cornerCoverZAlgebra Q).RightModule
  letI := HasDerivedCategory.standard (E.CutGradedRightModule Q)
  exact ASGinzburg.exactEquivalenceExtAddEquiv (E.cornerGradedModuleEquivalence Q) M N n

noncomputable def cornerGradedModuleExtLinearEquiv
    (M N : (E.cornerCoverZAlgebra Q).RightModule) (n : ℕ) :
    Abelian.Ext.{v} M N n ≃ₗ[k]
      Abelian.Ext.{v} (E.cornerGradedRightModule Q M) (E.cornerGradedRightModule Q N) n := by
  letI := HasDerivedCategory.standard (E.cornerCoverZAlgebra Q).RightModule
  letI := HasDerivedCategory.standard (E.CutGradedRightModule Q)
  exact ASGinzburg.exactEquivalenceExtLinearEquiv (E.cornerGradedModuleEquivalence Q) k M N n

end ASGinzburg.ZAlgebra.PeriodIso
