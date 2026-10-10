import work.ASGinzburgDraft.TrianglePotentialCoordinates
import work.ASGinzburgDraft.TriangleQuadraticASRegular
import ASGinzburg.ASFoundationPotentialDerivatives
import ASGinzburg.ASFoundationJacobianRingEquiv

/-! The actual tensor candidate w_B of source Corollary 5.2, obtained
from the proved AS foundation potential construction. Its cut derivatives
are the chosen actual quadratic relations. Ginzburg regularity and full
algebra recovery are not asserted. -/
namespace ASGinzburg

theorem triangle_zero_cut_return_path_is_quadratic
    (a : {a : triangle333.Arrow // triangle333.cut a = true})
    (p : triangle333.Path (triangle333.target a.val) (triangle333.source a.val))
    (hp : p.cutDegree = 0) : p.length = 2 := by
  have ha : 6 ≤ a.val.val := by simpa only [triangle333, decide_eq_true_eq] using a.property
  have ha9 : a.val.val < 9 := a.val.isLt
  have hw := p.winding_eq
  rw [triangle_path_winding, hp] at hw
  change (p.length : ℤ) =
    (a.val.val / 3 : ℕ) - ((a.val.val / 3 + 1) % 3 : ℕ) + 3 * (0 : ℤ) at hw
  omega

end ASGinzburg

namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def QuadraticASRegular.triangleFoundationTensor (hAS : A.QuadraticASRegular) :
    CubicTensor333 k :=
  (triangleTensorPotentialEquiv k).symm
    ((A.quadraticASRegular_iff_triangleASRegular.mp hAS).foundationPotential A triangle333)

theorem QuadraticASRegular.triangleFoundationTensor_potential (hAS : A.QuadraticASRegular) :
    triangleTensorPotentialEquiv k (hAS.triangleFoundationTensor A) =
      (A.quadraticASRegular_iff_triangleASRegular.mp hAS).foundationPotential A triangle333 :=
  (triangleTensorPotentialEquiv k).apply_symm_apply _

theorem QuadraticASRegular.triangleFoundationTensor_cubic_formula (hAS : A.QuadraticASRegular) :
    cyclicTrace (trianglePotential (cubicCoordinates333 k (hAS.triangleFoundationTensor A))) =
      ((A.quadraticASRegular_iff_triangleASRegular.mp hAS).foundationPotential A triangle333).val := by
  rw [← triangleTensorPotentialEquiv_val, hAS.triangleFoundationTensor_potential A]

theorem QuadraticASRegular.triangleFoundationTensor_cut_derivative
    (hAS : A.QuadraticASRegular)
    (a : {a : triangle333.Arrow // triangle333.cut a = true}) :
    triangle333.pathCyclicDerivative k a.val
      (triangleTensorPotentialEquiv k (hAS.triangleFoundationTensor A)) =
        (A.quadraticASRegular_iff_triangleASRegular.mp hAS).cutPathRelation A triangle333 a := by
  rw [hAS.triangleFoundationTensor_potential A]
  exact (A.quadraticASRegular_iff_triangleASRegular.mp hAS).foundationPotential_pathCyclicDerivative
    A triangle333 a

theorem QuadraticASRegular.triangleFoundationTensor_Z_derivative
    (hAS : A.QuadraticASRegular) (z : Fin 3) :
    triangle333.pathCyclicDerivative k (triangleZ z)
      (triangleTensorPotentialEquiv k (hAS.triangleFoundationTensor A)) =
        (A.quadraticASRegular_iff_triangleASRegular.mp hAS).cutPathRelation A triangle333
          ⟨triangleZ z, triangleZ_cut z⟩ :=
  hAS.triangleFoundationTensor_cut_derivative A ⟨triangleZ z, triangleZ_cut z⟩

theorem QuadraticASRegular.triangleFoundationTensor_relations_quadratic
    (hAS : A.QuadraticASRegular)
    (a : {a : triangle333.Arrow // triangle333.cut a = true}) :
    (A.quadraticASRegular_iff_triangleASRegular.mp hAS).cutPathRelation A triangle333 a ∈
      Finsupp.supported k k {p : triangle333.Path (triangle333.target a.val)
        (triangle333.source a.val) | p.length = 2 ∧ p.cutDegree = 0} := by
  have hs := (A.quadraticASRegular_iff_triangleASRegular.mp hAS).cutPathRelation_support
    A triangle333 a
  rw [Finsupp.mem_supported] at hs ⊢
  intro p hp
  exact ⟨triangle_zero_cut_return_path_is_quadratic a p (hs hp).2, (hs hp).2⟩

noncomputable def QuadraticASRegular.triangleFoundationTensorFoundationAlgEquiv
    {A : ZAlgebra.{u,u} k} (hAS : A.QuadraticASRegular) :
    triangle333.ZeroCutJacobianRing k
      (triangleTensorPotentialEquiv k (hAS.triangleFoundationTensor A)) ≃ₐ[k]
        A.FoundationAlgebra triangle333 := by
  rw [hAS.triangleFoundationTensor_potential A]
  exact (A.quadraticASRegular_iff_triangleASRegular.mp hAS).foundationJacobianRingAlgEquiv
    A triangle333

end ASGinzburg.ZAlgebra
