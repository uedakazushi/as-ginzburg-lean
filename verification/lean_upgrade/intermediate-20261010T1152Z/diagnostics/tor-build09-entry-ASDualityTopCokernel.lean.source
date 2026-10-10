import ASGinzburg.ASResolutionComplex
import ASGinzburg.RightModuleExtLeftSequence
import ASGinzburg.ASResolutionSyzygies

namespace ASGinzburg.ZAlgebra.ASResolution
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}
  {w : Q.LiftVertex} (R : A.ASResolution Q w)

noncomputable def dualTopProjection :
    A.rightModuleADual (R.complexTerm 3) ⟶
      A.rightModuleExtLeft (A.simpleRightModule (Q.height w)) 3 :=
  (A.rightModuleExtLeftZeroIso (R.complexTerm 3)).inv ≫
    A.rightModuleExtBoundaryLeft R.shortExact₂ 0 ≫
      (A.rightModuleExtDimensionShiftLeftIso R.shortExact₁ 0).hom ≫
        (A.rightModuleExtDimensionShiftLeftIso (shortExact₀ (A := A) (Q := Q) (v := w)) 1).hom

noncomputable instance dualTopProjectionEpi : Epi R.dualTopProjection := by
  dsimp [dualTopProjection]
  infer_instance

theorem dualTopProjection_dual_d₃ : A.rightModuleADualMap R.d₃ ≫ R.dualTopProjection = 0 := by
  dsimp [dualTopProjection, complexTerm]
  rw [← Category.assoc, A.rightModuleADualMap_extLeftZeroIso_inv R.d₃]
  simp only [Category.assoc]
  rw [← Category.assoc (A.rightModuleExtPrecompLeft R.d₃ 0)
    (A.rightModuleExtBoundaryLeft R.shortExact₂ 0)]
  rw [A.rightModuleExtPrecompLeft_boundary_zero R.shortExact₂ 0, zero_comp, comp_zero]
end ASGinzburg.ZAlgebra.ASResolution

namespace ASGinzburg.ZAlgebra.ASResolution
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}
  {w : Q.LiftVertex} (R : A.ASResolution Q w)

theorem dualTopProjection_exact :
    (ShortComplex.mk (A.rightModuleADualMap R.d₃) R.dualTopProjection R.dualTopProjection_dual_d₃).Exact := by
  let e : A.rightModuleExtLeft (kernel R.firstCover) 1 ≅
      A.rightModuleExtLeft (A.simpleRightModule (Q.height w)) 3 :=
    A.rightModuleExtDimensionShiftLeftIso R.shortExact₁ 0 ≪≫
      A.rightModuleExtDimensionShiftLeftIso (shortExact₀ (A := A) (Q := Q) (v := w)) 1
  let T := ShortComplex.mk (A.rightModuleExtPrecompLeft R.d₃ 0)
    (A.rightModuleExtBoundaryLeft R.shortExact₂ 0)
    (A.rightModuleExtPrecompLeft_boundary_zero R.shortExact₂ 0)
  let eS : ShortComplex.mk (A.rightModuleADualMap R.d₃) R.dualTopProjection R.dualTopProjection_dual_d₃ ≅ T :=
    ShortComplex.isoMk (A.rightModuleExtLeftZeroIso (A.asResolutionTerm₂ Q w)).symm
      (A.rightModuleExtLeftZeroIso (R.complexTerm 3)).symm e.symm
      (by exact (A.rightModuleADualMap_extLeftZeroIso_inv R.d₃).symm)
      (by
        dsimp [dualTopProjection,e,T]
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id])
  exact (ShortComplex.exact_iff_of_iso eS).mpr (A.rightModuleExtBoundaryLeft_exact R.shortExact₂ 0)
end ASGinzburg.ZAlgebra.ASResolution
