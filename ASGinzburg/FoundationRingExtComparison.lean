import ASGinzburg.FoundationRingEquivalenceLinear
import ASGinzburg.FoundationEnoughProjectives
import ASGinzburg.ExactEquivalenceExt

/-! The proved concrete finite-ring equivalence preserves actual
derived-category Ext in every degree, linearly over the original field. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

instance foundationRingEnoughProjectives :
    EnoughProjectives (ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) :=
  (A.foundationRingRightEquivalence Q).enoughProjectives_iff.mp inferInstance

instance foundationRingHasExt : HasExt.{u} (ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) :=
  hasExt_of_enoughProjectives (ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ)

noncomputable instance foundationExtModule (M N : A.FoundationRightModule Q) (n : ℕ) :
    Module k (Abelian.Ext.{u} M N n) := by
  letI := HasDerivedCategory.standard (A.FoundationRightModule Q)
  exact ASGinzburg.exactExtModule k M N n

noncomputable instance foundationRingExtModule
    (M N : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) (n : ℕ) :
    Module k (Abelian.Ext.{u} M N n) := by
  letI := HasDerivedCategory.standard (ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ)
  exact ASGinzburg.exactExtModule k M N n

noncomputable def foundationRingExtLinearEquiv
    (M N : A.FoundationRightModule Q) (n : ℕ) :
    Abelian.Ext.{u} M N n ≃ₗ[k]
      Abelian.Ext.{u} (A.foundationRightTotalModule Q M) (A.foundationRightTotalModule Q N) n := by
  letI := HasDerivedCategory.standard (A.FoundationRightModule Q)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ)
  letI : (A.foundationRingRightEquivalence Q).functor.Additive :=
    A.foundationRightTotalFunctorAdditive Q
  letI : (A.foundationRingRightEquivalence Q).inverse.Additive :=
    A.foundationRingRightComponentRecoveryAdditive Q
  letI : (A.foundationRingRightEquivalence Q).functor.Linear k :=
    A.foundationRightTotalFunctorLinear Q
  exact ASGinzburg.exactEquivalenceExtLinearEquiv (A.foundationRingRightEquivalence Q) k M N n

end ASGinzburg.ZAlgebra
