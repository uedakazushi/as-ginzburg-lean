import ASGinzburg.LeftHomColimits
import ASGinzburg.FiniteProjectiveResolutionExtColimits
import ASGinzburg.ASFiniteDimensionalResolutionLength
import ASGinzburg.FiniteProjectiveDuality

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v w w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def leftModuleExtZeroPreservesColimits (M : A.LeftModule)
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)]
    [PreservesColimitsOfShape J ((linearCoyoneda k A.LeftModule).obj (op M))] :
    PreservesColimitsOfShape J (A.leftModuleExtCovariant M 0) :=
  preservesColimitsOfShape_of_natIso (A.leftModuleExtZeroFunctorIso M).symm

noncomputable def leftModuleExtSuccPreservesColimits {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (ModuleCat.{v} k)]
    [PreservesColimitsOfShape J (A.leftModuleExtCovariant S.X₁ n)]
    [PreservesColimitsOfShape J (A.leftModuleExtCovariant S.X₂ n)] :
    PreservesColimitsOfShape J (A.leftModuleExtCovariant S.X₃ (n + 1)) := by
  letI := cokernelFunctorPreservesColimits (J := J) (A.leftModuleExtPrecompNat S.f n)
  exact preservesColimitsOfShape_of_natIso (A.leftModuleExtCokernelNatIso hS n)

end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v w w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem leftFiniteProjectiveHigherExtFunctorIsZero {P : A.LeftModule}
    (hP : A.leftFiniteProjectiveProperty P) (n : ℕ) :
    IsZero (A.leftModuleExtCovariant P (n+1)) := by
  letI : Projective P := A.leftFiniteProjectiveProperty_projective hP
  rw [Functor.isZero_iff]
  intro N
  letI : Subsingleton (Abelian.Ext.{v} P N (n+1)) :=
    ⟨fun a b => by rw [Abelian.Ext.eq_zero_of_projective a,Abelian.Ext.eq_zero_of_projective b]⟩
  change IsZero (ModuleCat.of k (Abelian.Ext.{v} P N (n+1)))
  exact ModuleCat.isZero_of_subsingleton _

noncomputable def leftFiniteProjectiveExtPreservesColimits {P : A.LeftModule}
    (hP : A.leftFiniteProjectiveProperty P) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J A.LeftModule] [HasColimitsOfShape J (ModuleCat.{v} k)]
    (n : ℕ) : PreservesColimitsOfShape J (A.leftModuleExtCovariant P n) := by
  cases n with
  | zero =>
    letI := A.leftFiniteProjectiveHomPreservesColimits hP J
    exact A.leftModuleExtZeroPreservesColimits P J
  | succ n =>
    exact Functor.preservesColimitsOfShape_of_isZero _
      (A.leftFiniteProjectiveHigherExtFunctorIsZero hP n) J

/-- Derived from actual finite projective covers and exact colimits, for every degree. -/
noncomputable def leftFiniteProjectiveResolutionExtPreservesExactColimits (length : ℕ)
    {M : A.LeftModule} (hM : A.HasLeftFiniteProjectiveResolutionLength length M)
    (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J A.LeftModule] [HasColimitsOfShape J (ModuleCat.{v} k)]
    [HasExactColimitsOfShape J (ModuleCat.{v} k)] (n : ℕ) :
    PreservesColimitsOfShape J (A.leftModuleExtCovariant M n) := by
  induction length generalizing M n with
  | zero => exact A.leftFiniteProjectiveExtPreservesColimits hM J n
  | succ length ih =>
    obtain ⟨P,π,hP,hπ,htail⟩ := hM
    letI := hπ
    letI : Projective P := A.leftFiniteProjectiveProperty_projective hP
    let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel π }
    cases n with
    | zero =>
      letI := ih htail 0
      letI : PreservesColimitsOfShape J ((linearCoyoneda k A.LeftModule).obj (op (kernel π))) :=
        preservesColimitsOfShape_of_natIso (A.leftModuleExtZeroFunctorIso (kernel π))
      letI := A.leftFiniteProjectiveHomPreservesColimits hP J
      letI := A.leftModuleHomPreservesExactColimits hS J
      exact A.leftModuleExtZeroPreservesColimits M J
    | succ n =>
      letI := ih htail n
      letI := A.leftFiniteProjectiveExtPreservesColimits hP J n
      exact A.leftModuleExtSuccPreservesColimits hS n J

noncomputable def leftFiniteDimensionalExtPreservesExactColimits
    (Q : CutQuiver) (hAS : A.ASRegular Q) (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J A.LeftModule] [HasColimitsOfShape J (ModuleCat.{v} k)]
    [HasExactColimitsOfShape J (ModuleCat.{v} k)] (n : ℕ) :
    PreservesColimitsOfShape J (A.leftModuleExtCovariant M n) :=
  A.leftFiniteProjectiveResolutionExtPreservesExactColimits 3
    (A.leftFiniteDimensional_hasFiniteProjectiveResolutionLength Q hAS M hM) J n

noncomputable def leftFiniteDimensionalExtPreservesCoproducts
    (Q : CutQuiver) (hAS : A.ASRegular Q) (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) (I : Type) (n : ℕ) :
    PreservesColimitsOfShape (Discrete I) (A.leftModuleExtCovariant M n) := by
  letI : HasExactColimitsOfShape (Discrete I) (ModuleCat.{v} k) := moduleCatExactCoproducts I
  exact A.leftFiniteDimensionalExtPreservesExactColimits Q hAS M hM (Discrete I) n

noncomputable def leftFiniteDimensionalExtCoproductIso
    (Q : CutQuiver) (hAS : A.ASRegular Q) (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) {I : Type} (n : ℕ) (F : I → A.LeftModule) :
    ModuleCat.of k (Abelian.Ext.{v} M (∐ F) n) ≅
      ∐ fun i => ModuleCat.of k (Abelian.Ext.{v} M (F i) n) := by
  letI := A.leftFiniteDimensionalExtPreservesCoproducts Q hAS M hM I n
  exact PreservesCoproduct.iso (A.leftModuleExtCovariant M n) F

noncomputable def leftFiniteDimensionalExtDirectSumLinearEquiv
    (Q : CutQuiver) (hAS : A.ASRegular Q) (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) {I : Type} [DecidableEq I]
    (n : ℕ) (F : I → A.LeftModule) :
    Abelian.Ext.{v} M (∐ F) n ≃ₗ[k] ⨁ i, Abelian.Ext.{v} M (F i) n :=
  ((A.leftFiniteDimensionalExtCoproductIso Q hAS M hM n F) ≪≫
    ModuleCat.coprodIsoDirectSum _).toLinearEquiv
end ASGinzburg.ZAlgebra
