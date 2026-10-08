import ASGinzburg.ExactEquivalenceExt
import ASGinzburg.LocallyUnitalAbelian

/-! The proved concrete locally unital equivalences preserve actual Ext in
all nonnegative degrees, with its actual field action. Naturality is developed
separately before transferring the paper's complete equation (1.12). -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable instance leftModuleExtModule (M N : A.LeftModule) (n : ℕ) :
    Module k (Abelian.Ext.{v} M N n) := by
  letI := HasDerivedCategory.standard A.LeftModule
  exact ASGinzburg.exactExtModule k M N n

noncomputable instance leftLocallyUnitalExtModule (M N : A.LeftLocallyUnitalModule) (n : ℕ) :
    Module k (Abelian.Ext.{v} M N n) := by
  letI := HasDerivedCategory.standard A.LeftLocallyUnitalModule
  exact ASGinzburg.exactExtModule k M N n

noncomputable instance rightLocallyUnitalExtModule (M N : A.RightLocallyUnitalModule) (n : ℕ) :
    Module k (Abelian.Ext.{v} M N n) := by
  letI := HasDerivedCategory.standard A.RightLocallyUnitalModule
  exact ASGinzburg.exactExtModule k M N n

noncomputable def leftLocallyUnitalExtAddEquiv (M N : A.LeftModule) (n : ℕ) :
    Abelian.Ext.{v} M N n ≃+
      Abelian.Ext.{v} (A.leftTotalLocallyUnitalModule M) (A.leftTotalLocallyUnitalModule N) n := by
  letI := HasDerivedCategory.standard A.LeftModule
  letI := HasDerivedCategory.standard A.LeftLocallyUnitalModule
  letI : A.leftLocallyUnitalEquivalence.functor.Additive := A.leftTotalLocallyUnitalFunctorAdditive
  letI : A.leftLocallyUnitalEquivalence.inverse.Additive := A.leftLocallyUnitalComponentFunctorAdditive
  exact ASGinzburg.exactEquivalenceExtAddEquiv A.leftLocallyUnitalEquivalence M N n

noncomputable def rightLocallyUnitalExtAddEquiv (M N : A.RightModule) (n : ℕ) :
    Abelian.Ext.{v} M N n ≃+
      Abelian.Ext.{v} (A.rightTotalLocallyUnitalModule M) (A.rightTotalLocallyUnitalModule N) n := by
  letI := HasDerivedCategory.standard A.RightModule
  letI := HasDerivedCategory.standard A.RightLocallyUnitalModule
  letI : A.rightLocallyUnitalEquivalence.functor.Additive := A.rightTotalLocallyUnitalFunctorAdditive
  letI : A.rightLocallyUnitalEquivalence.inverse.Additive := A.rightLocallyUnitalComponentFunctorAdditive
  exact ASGinzburg.exactEquivalenceExtAddEquiv A.rightLocallyUnitalEquivalence M N n

noncomputable def leftLocallyUnitalExtLinearEquiv (M N : A.LeftModule) (n : ℕ) :
    Abelian.Ext.{v} M N n ≃ₗ[k]
      Abelian.Ext.{v} (A.leftTotalLocallyUnitalModule M) (A.leftTotalLocallyUnitalModule N) n := by
  letI := HasDerivedCategory.standard A.LeftModule
  letI := HasDerivedCategory.standard A.LeftLocallyUnitalModule
  letI : A.leftLocallyUnitalEquivalence.functor.Additive := A.leftTotalLocallyUnitalFunctorAdditive
  letI : A.leftLocallyUnitalEquivalence.inverse.Additive := A.leftLocallyUnitalComponentFunctorAdditive
  letI : A.leftLocallyUnitalEquivalence.functor.Linear k := A.leftTotalLocallyUnitalFunctorLinear
  exact ASGinzburg.exactEquivalenceExtLinearEquiv A.leftLocallyUnitalEquivalence k M N n

noncomputable def rightLocallyUnitalExtLinearEquiv (M N : A.RightModule) (n : ℕ) :
    Abelian.Ext.{v} M N n ≃ₗ[k]
      Abelian.Ext.{v} (A.rightTotalLocallyUnitalModule M) (A.rightTotalLocallyUnitalModule N) n := by
  letI := HasDerivedCategory.standard A.RightModule
  letI := HasDerivedCategory.standard A.RightLocallyUnitalModule
  letI : A.rightLocallyUnitalEquivalence.functor.Additive := A.rightTotalLocallyUnitalFunctorAdditive
  letI : A.rightLocallyUnitalEquivalence.inverse.Additive := A.rightLocallyUnitalComponentFunctorAdditive
  letI : A.rightLocallyUnitalEquivalence.functor.Linear k := A.rightTotalLocallyUnitalFunctorLinear
  exact ASGinzburg.exactEquivalenceExtLinearEquiv A.rightLocallyUnitalEquivalence k M N n

end ASGinzburg.ZAlgebra
