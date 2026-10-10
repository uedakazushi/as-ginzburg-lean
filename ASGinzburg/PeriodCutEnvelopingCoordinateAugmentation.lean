import ASGinzburg.PeriodCutEnvelopingVertexIdempotents
import ASGinzburg.PeriodCutEnvelopingAugmentationComparison
import ASGinzburg.ScalarProductEnvelopingCoordinates

/-! An actual surjective scalar augmentation of the unsigned enveloping
algebra. Its kernel is the genuine full enveloping augmentation kernel,
and its pair idempotents lift the corresponding scalar delta functions. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped TensorProduct
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))
attribute [local instance 2000] cutEnvelopingOppositeFactorScalarTower
  cutEnvelopingOppositeFactorScalarComm cutGradedRingSelfScalarTower cutGradedRingSelfScalarComm

noncomputable def cutEnvelopingCoordinateAugmentation :
    AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))) →ₐ[k]
      (Q.Vertex × Q.Vertex → k) :=
  (scalarProductPairEnvelopingEquiv k Q.Vertex).toAlgHom.comp
    (algebraEnvelopingMap k (E.cutAugmentation Q))

theorem cutEnvelopingCoordinateAugmentation_surjective :
    Function.Surjective (E.cutEnvelopingCoordinateAugmentation Q) :=
  (scalarProductPairEnvelopingEquiv k Q.Vertex).surjective.comp
    (algebraEnvelopingMap_surjective k (E.cutAugmentation Q)
      (E.cutAugmentation_surjective Q))

theorem cutEnvelopingCoordinateAugmentation_ker :
    RingHom.ker (E.cutEnvelopingCoordinateAugmentation Q) =
      E.cutEnvelopingAugmentationKernel Q := by
  rw [E.cutEnvelopingAugmentationKernel_eq_scalarKernel Q]
  ext x
  change scalarProductPairEnvelopingEquiv k Q.Vertex
      (algebraEnvelopingMap k (E.cutAugmentation Q) x) = 0 ↔
    algebraEnvelopingMap k (E.cutAugmentation Q) x = 0
  constructor
  · intro hx
    exact (scalarProductPairEnvelopingEquiv k Q.Vertex).injective
      (hx.trans (scalarProductPairEnvelopingEquiv k Q.Vertex).map_zero.symm)
  · intro hx
    rw [hx]
    exact (scalarProductPairEnvelopingEquiv k Q.Vertex).map_zero

theorem cutEnvelopingCoordinateAugmentation_vertexIdempotent (a : Q.Vertex × Q.Vertex) :
    E.cutEnvelopingCoordinateAugmentation Q (E.cutEnvelopingVertexIdempotent Q a) =
      Pi.single a (1:k) := by
  change scalarProductPairEnvelopingEquiv k Q.Vertex
    (E.cutAugmentation Q (E.cutVertexIdempotent (fun i : Q.Vertex => (i.val : ℤ)) a.1)
      ⊗ₜ[k] MulOpposite.op
        (E.cutAugmentation Q (E.cutVertexIdempotent (fun i : Q.Vertex => (i.val : ℤ)) a.2))) = _
  rw [E.cutAugmentation_vertexIdempotent Q, E.cutAugmentation_vertexIdempotent Q]
  exact scalarProductPairEnvelopingEquiv_delta k Q.Vertex a.1 a.2

end ASGinzburg.ZAlgebra.PeriodIso
