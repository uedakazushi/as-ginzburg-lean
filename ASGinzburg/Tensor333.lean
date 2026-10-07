import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# The concrete (3,3,3) tensor and its three quadratic cut relations

Unlike an abstract correspondence schema, the tensor product and all
linear maps here are concrete mathlib vector spaces. The AS and Ginzburg
regularity predicates on this space have not yet been constructed.
-/

namespace ASGinzburg

open scoped TensorProduct

universe u
variable (k : Type u) [Field k]

abbrev ArrowSpace333 := Fin 3 → k
abbrev CubicTensor333 := ArrowSpace333 k ⊗[k] (ArrowSpace333 k ⊗[k] ArrowSpace333 k)
abbrev Triple333 := Fin 3 × (Fin 3 × Fin 3)
abbrev CubicCoefficients333 := Triple333 → k
abbrev CutRelations333 := Fin 3 → (Fin 3 × Fin 3 → k)

noncomputable def cubicBasis333 : Module.Basis Triple333 k (CubicTensor333 k) :=
  (Pi.basisFun k (Fin 3)).tensorProduct
    ((Pi.basisFun k (Fin 3)).tensorProduct (Pi.basisFun k (Fin 3)))

noncomputable def cubicCoordinates333 : CubicTensor333 k ≃ₗ[k] CubicCoefficients333 k :=
  (cubicBasis333 k).repr.trans (Finsupp.linearEquivFunOnFinite k k Triple333)

def cutRelationCoordinates333 : CubicCoefficients333 k ≃ₗ[k] CutRelations333 k where
  toFun w z xy := w (xy.1, (xy.2, z))
  invFun r xyz := r xyz.2.2 (xyz.1, xyz.2.1)
  left_inv := by intro w; funext ⟨x,y,z⟩; rfl
  right_inv := by intro r; funext z ⟨x,y⟩; rfl
  map_add' := by intro w w'; rfl
  map_smul' := by intro c w; rfl

/-- Writing w = z₁r₁ + z₂r₂ + z₃r₃ in the fixed ordered bases. -/
noncomputable def tensorToCutRelations333 : CubicTensor333 k ≃ₗ[k] CutRelations333 k :=
  (cubicCoordinates333 k).trans (cutRelationCoordinates333 k)

theorem tensor_recovered_from_cut_relations333 (w : CubicTensor333 k) :
    (tensorToCutRelations333 k).symm (tensorToCutRelations333 k w) = w :=
  (tensorToCutRelations333 k).symm_apply_apply w

theorem cubicTensor333_finrank : Module.finrank k (CubicTensor333 k) = 27 := by
  rw [(cubicCoordinates333 k).finrank_eq]
  simp [CubicCoefficients333, Triple333]

noncomputable def arrowBasisChange333
    (x y z : ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k) :
    CubicTensor333 k ≃ₗ[k] CubicTensor333 k :=
  TensorProduct.congr x (TensorProduct.congr y z)

theorem arrowBasisChange333_tmul
    (x y z : ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k)
    (a b c : ArrowSpace333 k) :
    arrowBasisChange333 k x y z (a ⊗ₜ[k] (b ⊗ₜ[k] c)) =
      x a ⊗ₜ[k] (y b ⊗ₜ[k] z c) := by
  simp [arrowBasisChange333]

end ASGinzburg
