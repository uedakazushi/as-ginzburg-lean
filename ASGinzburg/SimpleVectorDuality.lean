import ASGinzburg.RightSingleSupportIsomorphism
import ASGinzburg.ModuleVectorDuality


namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k]
theorem moduleCatDualInto_isZero (U M : ModuleCat.{v} k) (hM : IsZero M) :
    IsZero ((moduleCatDualIntoFunctor U).obj (op M)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro f g
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx : x=0 := (ModuleCat.isZero_iff_subsingleton.mp hM).elim x 0
  change f.hom x = g.hom x
  rw [hx,map_zero,map_zero]
end ASGinzburg

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightModuleVectorDual_component_isZero (M : A.RightModule) (i : ℤ)
    (hM : IsZero ((A.rightModuleEvaluation i).obj M)) :
    IsZero ((A.leftModuleEvaluation i).obj (A.rightModuleVectorDual M)) :=
  ASGinzburg.moduleCatDualInto_isZero (ModuleCat.of k (A.Hom 0 0)) _ hM

theorem rightSimpleVectorDual_diagonal_finrank (i : ℤ) :
    Module.finrank k ((A.leftModuleEvaluation i).obj (A.rightModuleVectorDual (A.simpleRightModule i))) = 1 := by
  let M : ModuleCat.{v} k := (A.rightModuleEvaluation i).obj (A.simpleRightModule i)
  let U : ModuleCat.{v} k := ModuleCat.of k (A.Hom 0 0)
  change Module.finrank k (M ⟶ U) = 1
  rw [(ModuleCat.homLinearEquiv (M := M) (N := U) (S := k)).finrank_eq,
    (ASGinzburg.dualIntoToDual (M := M) (A.scalarEndEquiv 0)).finrank_eq,
    Subspace.dual_finrank_eq]
  exact A.simpleRightModule_diagonal_finrank i

noncomputable def rightSimpleVectorDualDiagonalIso (i : ℤ) :
    (A.leftModuleEvaluation i).obj (A.rightModuleVectorDual (A.simpleRightModule i)) ≅
      (A.leftModuleEvaluation i).obj (A.simpleLeftModule i) := by
  let V : ModuleCat.{v} k := (A.leftModuleEvaluation i).obj
    (A.rightModuleVectorDual (A.simpleRightModule i))
  let W : ModuleCat.{v} k := (A.leftModuleEvaluation i).obj (A.simpleLeftModule i)
  letI : Module.Finite k V := A.leftFiniteDimensional_component_finite
    (A.rightModuleVectorDual_finite (A.rightFiniteDimensional_simple i)) i
  letI : Module.Finite k W := A.leftFiniteDimensional_component_finite (A.leftFiniteDimensional_simple i) i
  let e : V ≃ₗ[k] W := LinearEquiv.ofFinrankEq (R := k) V W
    ((A.rightSimpleVectorDual_diagonal_finrank i).trans (A.simpleLeftModule_diagonal_finrank i).symm)
  exact e.toModuleIso

noncomputable def rightSimpleVectorDualIso (i : ℤ) :
    A.rightModuleVectorDual (A.simpleRightModule i) ≅ A.simpleLeftModule i :=
  A.leftModuleIsoOfSingleSupport _ _ i
    (fun j hj => A.rightModuleVectorDual_component_isZero _ j (A.simpleRightModule_off_diagonal i j hj))
    (fun j hj => A.simpleLeftModule_off_diagonal i j hj)
    (A.rightSimpleVectorDualDiagonalIso i)

theorem leftModuleVectorDual_component_isZero (M : A.LeftModule) (i : ℤ)
    (hM : IsZero ((A.leftModuleEvaluation i).obj M)) :
    IsZero ((A.rightModuleEvaluation i).obj (A.leftModuleVectorDual M)) :=
  ASGinzburg.moduleCatDualInto_isZero (ModuleCat.of k (A.Hom 0 0)) _ hM

theorem leftSimpleVectorDual_diagonal_finrank (i : ℤ) :
    Module.finrank k ((A.rightModuleEvaluation i).obj (A.leftModuleVectorDual (A.simpleLeftModule i))) = 1 := by
  let M : ModuleCat.{v} k := (A.leftModuleEvaluation i).obj (A.simpleLeftModule i)
  let U : ModuleCat.{v} k := ModuleCat.of k (A.Hom 0 0)
  change Module.finrank k (M ⟶ U) = 1
  rw [(ModuleCat.homLinearEquiv (M := M) (N := U) (S := k)).finrank_eq,
    (ASGinzburg.dualIntoToDual (M := M) (A.scalarEndEquiv 0)).finrank_eq,
    Subspace.dual_finrank_eq]
  exact A.simpleLeftModule_diagonal_finrank i

noncomputable def leftSimpleVectorDualDiagonalIso (i : ℤ) :
    (A.rightModuleEvaluation i).obj (A.leftModuleVectorDual (A.simpleLeftModule i)) ≅
      (A.rightModuleEvaluation i).obj (A.simpleRightModule i) := by
  let V : ModuleCat.{v} k := (A.rightModuleEvaluation i).obj
    (A.leftModuleVectorDual (A.simpleLeftModule i))
  let W : ModuleCat.{v} k := (A.rightModuleEvaluation i).obj (A.simpleRightModule i)
  letI : Module.Finite k V := A.rightFiniteDimensional_component_finite
    (A.leftModuleVectorDual_finite (A.leftFiniteDimensional_simple i)) i
  letI : Module.Finite k W := A.rightFiniteDimensional_component_finite (A.rightFiniteDimensional_simple i) i
  let e : V ≃ₗ[k] W := LinearEquiv.ofFinrankEq (R := k) V W
    ((A.leftSimpleVectorDual_diagonal_finrank i).trans (A.simpleRightModule_diagonal_finrank i).symm)
  exact e.toModuleIso

noncomputable def leftSimpleVectorDualIso (i : ℤ) :
    A.leftModuleVectorDual (A.simpleLeftModule i) ≅ A.simpleRightModule i :=
  A.rightSingleSupportIso i _ _
    (fun j hj => A.leftModuleVectorDual_component_isZero _ j (A.simpleLeftModule_off_diagonal i j hj))
    (fun j hj => A.simpleRightModule_off_diagonal i j hj)
    (A.leftSimpleVectorDualDiagonalIso i)
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

end ASGinzburg.ZAlgebra
