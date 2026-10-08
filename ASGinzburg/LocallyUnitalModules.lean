import ASGinzburg.TotalModuleRepresentations
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.Module.RingHom

/-!
The actual total representations extend over the unitization. Concrete total
spaces become ModuleCat objects, and lie in the full subcategory where finite
sums of the original component identities fix every element. The equivalence
with the original component module categories is constructed separately.
-/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

abbrev totalUnitization := Unitization k A.totalAlgebra

noncomputable instance totalUnitizationRing : Ring A.totalUnitization :=
  Unitization.instRing

noncomputable instance totalUnitizationSemiring : Semiring A.totalUnitization :=
  A.totalUnitizationRing.toSemiring

noncomputable def leftTotalUnitalRepresentation (M : A.LeftModule) :
    A.totalUnitization →ₐ[k] Module.End k (A.leftModuleTotalSpace M) :=
  Unitization.lift (A.leftTotalRepresentation M)

noncomputable def rightTotalUnitalOppositeRepresentation (M : A.RightModule) :
    A.totalUnitization →ₐ[k] (Module.End k (A.rightModuleTotalSpace M))ᵐᵒᵖ :=
  Unitization.lift (A.rightTotalRepresentation M)

noncomputable def rightTotalUnitalRepresentation (M : A.RightModule) :
    A.totalUnitizationᵐᵒᵖ →ₐ[k] Module.End k (A.rightModuleTotalSpace M) :=
  AlgHom.opComm (A.rightTotalUnitalOppositeRepresentation M)

noncomputable def leftTotalUnitizationModule (M : A.LeftModule) :
    Module A.totalUnitization (A.leftModuleTotalSpace M) :=
  Module.compHom (A.leftModuleTotalSpace M) (A.leftTotalUnitalRepresentation M).toRingHom

noncomputable def rightTotalUnitizationModule (M : A.RightModule) :
    Module A.totalUnitizationᵐᵒᵖ (A.rightModuleTotalSpace M) :=
  Module.compHom (A.rightModuleTotalSpace M) (A.rightTotalUnitalRepresentation M).toRingHom


@[simp] theorem leftTotalUnitalRepresentation_coe (M : A.LeftModule) (a : A.totalAlgebra) :
    A.leftTotalUnitalRepresentation M (a : A.totalUnitization) = A.leftTotalRepresentation M a := by
  simp [leftTotalUnitalRepresentation]

@[simp] theorem rightTotalUnitalRepresentation_op_coe (M : A.RightModule) (a : A.totalAlgebra) :
    A.rightTotalUnitalRepresentation M (MulOpposite.op (a : A.totalUnitization)) =
      (A.rightTotalRepresentation M a).unop := by
  change (A.rightTotalUnitalOppositeRepresentation M (a : A.totalUnitization)).unop = _
  simp [rightTotalUnitalOppositeRepresentation]

noncomputable def leftTotalModule (M : A.LeftModule) : ModuleCat.{v} A.totalUnitization := by
  letI := A.leftTotalUnitizationModule M
  exact ModuleCat.of A.totalUnitization (A.leftModuleTotalSpace M)

noncomputable def rightTotalModule (M : A.RightModule) : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ := by
  letI := A.rightTotalUnitizationModule M
  exact ModuleCat.of A.totalUnitizationᵐᵒᵖ (A.rightModuleTotalSpace M)

@[simp] theorem leftTotalModule_component_smul (M : A.LeftModule) {i j : ℤ}
    (a : A.Hom i j) (x : A.leftTotalModule M) :
    ((A.totalAlgebraComponent a : A.totalAlgebra) : A.totalUnitization) • x =
      A.leftModuleTotalAction M a x := by
  change A.leftTotalUnitalRepresentation M (A.totalAlgebraComponent a : A.totalUnitization) x = _
  rw [A.leftTotalUnitalRepresentation_coe, A.leftTotalRepresentation_component]

@[simp] theorem rightTotalModule_component_smul (M : A.RightModule) {i j : ℤ}
    (a : A.Hom i j) (x : A.rightTotalModule M) :
    MulOpposite.op ((A.totalAlgebraComponent a : A.totalAlgebra) : A.totalUnitization) • x =
      A.rightModuleTotalAction M a x := by
  change A.rightTotalUnitalRepresentation M
    (MulOpposite.op (A.totalAlgebraComponent a : A.totalUnitization)) x = _
  rw [A.rightTotalUnitalRepresentation_op_coe, A.rightTotalRepresentation_component]

/-- The concrete local-unit condition on modules over the unitization. -/
def leftLocallyUnitalProperty : ObjectProperty (ModuleCat.{v} A.totalUnitization) :=
  fun M => ∀ x : M, ∃ s : Finset ℤ, (A.totalAlgebraLocalUnit s : A.totalUnitization) • x = x

def rightLocallyUnitalProperty : ObjectProperty (ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) :=
  fun M => ∀ x : M, ∃ s : Finset ℤ,
    MulOpposite.op (A.totalAlgebraLocalUnit s : A.totalUnitization) • x = x

abbrev LeftLocallyUnitalModule := A.leftLocallyUnitalProperty.FullSubcategory
abbrev RightLocallyUnitalModule := A.rightLocallyUnitalProperty.FullSubcategory

theorem leftTotalModule_locally_unital (M : A.LeftModule) :
    A.leftLocallyUnitalProperty (A.leftTotalModule M) := by
  intro x
  obtain ⟨s,hs⟩ := A.leftModuleTotalSpace_local_units M x
  refine ⟨s,?_⟩
  change A.leftTotalUnitalRepresentation M (A.totalAlgebraLocalUnit s : A.totalUnitization) x = x
  rw [A.leftTotalUnitalRepresentation_coe]
  simpa only [totalAlgebraLocalUnit, map_sum, leftTotalRepresentation_component] using hs

theorem rightTotalModule_locally_unital (M : A.RightModule) :
    A.rightLocallyUnitalProperty (A.rightTotalModule M) := by
  intro x
  obtain ⟨s,hs⟩ := A.rightModuleTotalSpace_local_units M x
  refine ⟨s,?_⟩
  change A.rightTotalUnitalRepresentation M
    (MulOpposite.op (A.totalAlgebraLocalUnit s : A.totalUnitization)) x = x
  rw [A.rightTotalUnitalRepresentation_op_coe]
  have h : (A.rightTotalRepresentation M (A.totalAlgebraLocalUnit s)).unop =
      ∑ i ∈ s, A.rightModuleTotalAction M (A.id i) := by
    change (MulOpposite.opLinearEquiv k).symm
      (A.rightTotalRepresentation M (A.totalAlgebraLocalUnit s)) = _
    simp only [totalAlgebraLocalUnit, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact A.rightTotalRepresentation_component M (A.id i)
  rw [h]
  exact hs

noncomputable def leftTotalLocallyUnitalModule (M : A.LeftModule) : A.LeftLocallyUnitalModule :=
  ⟨A.leftTotalModule M, A.leftTotalModule_locally_unital M⟩

noncomputable def rightTotalLocallyUnitalModule (M : A.RightModule) : A.RightLocallyUnitalModule :=
  ⟨A.rightTotalModule M, A.rightTotalModule_locally_unital M⟩

end ASGinzburg.ZAlgebra
