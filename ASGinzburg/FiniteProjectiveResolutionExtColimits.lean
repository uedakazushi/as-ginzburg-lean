import ASGinzburg.FiniteProjectiveHomColimits
import ASGinzburg.ASResolutionExtColimits
import ASGinzburg.ASFiniteDimensionalResolutionLength
import ASGinzburg.FiniteProjectiveDuality

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v w w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightFiniteProjectiveHigherExtFunctorIsZero {P : A.RightModule}
    (hP : A.rightFiniteProjectiveProperty P) (n : ℕ) :
    IsZero (A.rightModuleExtCovariant P (n+1)) := by
  letI : Projective P := A.rightFiniteProjectiveProperty_projective hP
  rw [Functor.isZero_iff]
  intro N
  letI : Subsingleton (Abelian.Ext.{v} P N (n+1)) :=
    ⟨fun a b => by rw [Abelian.Ext.eq_zero_of_projective a,Abelian.Ext.eq_zero_of_projective b]⟩
  change IsZero (ModuleCat.of k (Abelian.Ext.{v} P N (n+1)))
  exact ModuleCat.isZero_of_subsingleton _

noncomputable def rightFiniteProjectiveExtPreservesColimits {P : A.RightModule}
    (hP : A.rightFiniteProjectiveProperty P) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J A.RightModule] [HasColimitsOfShape J (ModuleCat.{v} k)]
    (n : ℕ) : PreservesColimitsOfShape J (A.rightModuleExtCovariant P n) := by
  cases n with
  | zero =>
    letI := A.rightFiniteProjectiveHomPreservesColimits hP J
    exact A.rightModuleExtZeroPreservesColimits P J
  | succ n =>
    exact Functor.preservesColimitsOfShape_of_isZero _
      (A.rightFiniteProjectiveHigherExtFunctorIsZero hP n) J

/-- Derived from actual finite projective covers and exact colimits, for every degree. -/
noncomputable def rightFiniteProjectiveResolutionExtPreservesExactColimits (length : ℕ)
    {M : A.RightModule} (hM : A.HasRightFiniteProjectiveResolutionLength length M)
    (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J A.RightModule] [HasColimitsOfShape J (ModuleCat.{v} k)]
    [HasExactColimitsOfShape J (ModuleCat.{v} k)] (n : ℕ) :
    PreservesColimitsOfShape J (A.rightModuleExtCovariant M n) := by
  induction length generalizing M n with
  | zero => exact A.rightFiniteProjectiveExtPreservesColimits hM J n
  | succ length ih =>
    obtain ⟨P,π,hP,hπ,htail⟩ := hM
    letI := hπ
    letI : Projective P := A.rightFiniteProjectiveProperty_projective hP
    let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel π }
    cases n with
    | zero =>
      letI := ih htail 0
      letI : PreservesColimitsOfShape J ((linearCoyoneda k A.RightModule).obj (op (kernel π))) :=
        preservesColimitsOfShape_of_natIso (A.rightModuleExtZeroFunctorIso (kernel π))
      letI := A.rightFiniteProjectiveHomPreservesColimits hP J
      letI := A.rightModuleHomPreservesExactColimits hS J
      exact A.rightModuleExtZeroPreservesColimits M J
    | succ n =>
      letI := ih htail n
      letI := A.rightFiniteProjectiveExtPreservesColimits hP J n
      exact A.rightModuleExtSuccPreservesColimits hS n J

noncomputable def rightFiniteDimensionalExtPreservesExactColimits
    (Q : CutQuiver) (hAS : A.ASRegular Q) (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J A.RightModule] [HasColimitsOfShape J (ModuleCat.{v} k)]
    [HasExactColimitsOfShape J (ModuleCat.{v} k)] (n : ℕ) :
    PreservesColimitsOfShape J (A.rightModuleExtCovariant M n) :=
  A.rightFiniteProjectiveResolutionExtPreservesExactColimits 3
    (A.rightFiniteDimensional_hasFiniteProjectiveResolutionLength Q hAS M hM) J n

noncomputable def rightFiniteDimensionalExtPreservesCoproducts
    (Q : CutQuiver) (hAS : A.ASRegular Q) (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) (I : Type) (n : ℕ) :
    PreservesColimitsOfShape (Discrete I) (A.rightModuleExtCovariant M n) := by
  letI : HasExactColimitsOfShape (Discrete I) (ModuleCat.{v} k) := moduleCatExactCoproducts I
  exact A.rightFiniteDimensionalExtPreservesExactColimits Q hAS M hM (Discrete I) n

noncomputable def rightFiniteDimensionalExtCoproductIso
    (Q : CutQuiver) (hAS : A.ASRegular Q) (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) {I : Type} (n : ℕ) (F : I → A.RightModule) :
    ModuleCat.of k (Abelian.Ext.{v} M (∐ F) n) ≅
      ∐ fun i => ModuleCat.of k (Abelian.Ext.{v} M (F i) n) := by
  letI := A.rightFiniteDimensionalExtPreservesCoproducts Q hAS M hM I n
  exact PreservesCoproduct.iso (A.rightModuleExtCovariant M n) F

noncomputable def rightFiniteDimensionalExtDirectSumLinearEquiv
    (Q : CutQuiver) (hAS : A.ASRegular Q) (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) {I : Type} [DecidableEq I]
    (n : ℕ) (F : I → A.RightModule) :
    Abelian.Ext.{v} M (∐ F) n ≃ₗ[k] ⨁ i, Abelian.Ext.{v} M (F i) n :=
  ((A.rightFiniteDimensionalExtCoproductIso Q hAS M hM n F) ≪≫
    ModuleCat.coprodIsoDirectSum _).toLinearEquiv
end ASGinzburg.ZAlgebra
