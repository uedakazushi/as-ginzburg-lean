import ASGinzburg.TriangleTensorAction
import Mathlib.LinearAlgebra.Dual.Basis

/-! The actual transpose arrow change identifies a change of basis of
the three quadratic slices with the usual GL action on the cut arrows. -/
namespace ASGinzburg
open scoped TensorProduct
universe u
variable (k : Type u) [Field k]

noncomputable def triangleArrowTranspose
    (g : ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k) :
    ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k :=
  (Pi.basisFun k (Fin 3)).toDualEquiv.trans
    (g.dualMap.trans (Pi.basisFun k (Fin 3)).toDualEquiv.symm)

theorem triangleArrowTranspose_single_apply
    (g : ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k) (j i : Fin 3) :
    triangleArrowTranspose k g (Pi.single j 1) i = g (Pi.single i 1) j := by
  classical
  let b := Pi.basisFun k (Fin 3)
  have h := b.coord_toDualEquiv_symm_apply i (g.dualMap (b.toDualEquiv (b j)))
  simp only [Module.Basis.coord_apply, Module.Basis.dualBasis_repr,
    LinearEquiv.dualMap_apply, Module.Basis.toDualEquiv_apply,
    Module.Basis.toDual_apply_right] at h
  simpa only [triangleArrowTranspose, LinearEquiv.trans_apply, b,
    Pi.basisFun_repr, Pi.basisFun_apply] using h

theorem cubicCoordinates333_tmul (x y z : ArrowSpace333 k) (xyz : Triple333) :
    cubicCoordinates333 k (x ⊗ₜ[k] (y ⊗ₜ[k] z)) xyz =
      x xyz.1 * (y xyz.2.1 * z xyz.2.2) := by
  rcases xyz with ⟨i,j,l⟩
  change ((Pi.basisFun k (Fin 3)).tensorProduct
    ((Pi.basisFun k (Fin 3)).tensorProduct (Pi.basisFun k (Fin 3)))).repr
      (x ⊗ₜ[k] (y ⊗ₜ[k] z)) (i,(j,l)) = _
  rw [Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.tensorProduct_repr_tmul_apply]
  simp [Pi.basisFun_repr, mul_comm]

theorem tensorToCutRelations333_basisChangeZ
    (g : ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k)
    (w : CubicTensor333 k) (z : Fin 3) (xy : Fin 3 × Fin 3) :
    tensorToCutRelations333 k
        (arrowBasisChange333 k (LinearEquiv.refl k _) (LinearEquiv.refl k _)
          (triangleArrowTranspose k g) w) z xy =
      ∑ j : Fin 3, g (Pi.single z 1) j * tensorToCutRelations333 k w j xy := by
  classical
  let C := (tensorToCutRelations333 k).toLinearMap
  let L : CubicTensor333 k →ₗ[k] k :=
    ((LinearMap.proj xy).comp ((LinearMap.proj z).comp C)).comp
      (arrowBasisChange333 k (LinearEquiv.refl k _) (LinearEquiv.refl k _)
        (triangleArrowTranspose k g)).toLinearMap
  let R : CubicTensor333 k →ₗ[k] k :=
    ∑ j : Fin 3, g (Pi.single z 1) j •
      ((LinearMap.proj xy).comp ((LinearMap.proj j).comp C))
  have h : L = R := by
    apply (cubicBasis333 k).ext
    intro xyz
    simp only [L, R, C, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearEquiv.coe_coe, tensorToCutRelations333, LinearEquiv.trans_apply,
      cutRelationCoordinates333]
    simp [cubicBasis333, Module.Basis.tensorProduct_apply',
      Pi.basisFun_apply, arrowBasisChange333_tmul, cubicCoordinates333_tmul,
      triangleArrowTranspose_single_apply, Pi.single_apply]
  exact LinearMap.congr_fun h w

end ASGinzburg
