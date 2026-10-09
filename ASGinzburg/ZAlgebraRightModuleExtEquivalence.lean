import ASGinzburg.ZAlgebraRightModuleEquivalence

/-! The actual right-module equivalence transports genuine projective
resolutions and preserves actual Ext, linearly for the existing actions. -/
namespace ASGinzburg.ZAlgebra.Isomorphism
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A B : ZAlgebra.{u,v} k}
variable (E : Isomorphism A B)

noncomputable def rightModuleExtLinearEquiv (M N : A.RightModule) (n : ℕ) :
    Abelian.Ext.{v} M N n ≃ₗ[k]
      Abelian.Ext.{v} (E.rightModuleEquivalence.functor.obj M)
        (E.rightModuleEquivalence.functor.obj N) n := by
  letI := HasDerivedCategory.standard A.RightModule
  letI := HasDerivedCategory.standard B.RightModule
  exact ASGinzburg.exactEquivalenceExtLinearEquiv E.rightModuleEquivalence k M N n

noncomputable def rightModuleProjectiveResolution {M : A.RightModule}
    (P : ProjectiveResolution M) :
    ProjectiveResolution (E.rightModuleEquivalence.functor.obj M) :=
  equivalenceProjectiveResolution E.rightModuleEquivalence P

theorem rightModuleProjectiveResolution_isZero {M : A.RightModule}
    (P : ProjectiveResolution M) (n : ℕ) (h : IsZero (P.complex.X n)) :
    IsZero ((E.rightModuleProjectiveResolution P).complex.X n) :=
  equivalenceProjectiveResolution_isZero E.rightModuleEquivalence P n h

end ASGinzburg.ZAlgebra.Isomorphism
