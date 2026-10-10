import work.ASGinzburgDraft.TriangleGinzburgGLCochainInvariance
import work.ASGinzburgDraft.TriangleGinzburgFoundationPotentialOrbit
import ASGinzburg.PathAutomorphismJacobianDescent

/-! On the genuine image of a Ginzburg-regular triangle potential, the
actual AS foundation candidate is itself regular and recovers the actual
source algebra. This does not assert recovery for arbitrary AS algebras. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem triangleGinzburgRegular_foundationPotential_ginzburgRegular
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) :
    triangle333.GinzburgRegular k
      ((hG.asRegular triangle333 k φ).foundationPotential _ triangle333) := by
  obtain ⟨E,hE⟩ := triangleGinzburgRegular_foundationPotential_pathAutomorphism k φ hG
  apply (triangleGinzburgRegular_pathAutomorphism_iff k E _).mpr
  rw [hE]
  exact hG

theorem triangleGinzburgRegular_foundationTensor_ginzburgRegular
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) :
    triangle333.GinzburgRegular k (triangleTensorPotentialEquiv k
      ((hG.asRegular triangle333 k φ).triangleFoundationTensor _)) := by
  simpa only [ZAlgebra.ASRegular.triangleFoundationTensor,LinearEquiv.apply_symm_apply] using
    triangleGinzburgRegular_foundationPotential_ginzburgRegular k φ hG

noncomputable def triangleGinzburgFoundationRegularPotential
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) :
    GinzburgRegularPotential k triangle333 :=
  ⟨(hG.asRegular triangle333 k φ).foundationPotential _ triangle333,
    triangleGinzburgRegular_foundationPotential_ginzburgRegular k φ hG⟩

@[simp] theorem triangleGinzburgFoundationRegularPotential_val
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) :
    (triangleGinzburgFoundationRegularPotential k φ hG).val =
      (hG.asRegular triangle333 k φ).foundationPotential _ triangle333 := rfl

theorem triangleGinzburgFoundationRegularPotential_recovery
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) :
    Nonempty (ZAlgebra.Isomorphism (triangle333.unrolledJacobianZAlgebra k φ)
      (triangle333.unrolledJacobianZAlgebra k
        (triangleGinzburgFoundationRegularPotential k φ hG).val)) := by
  have h := triangleGinzburgRegular_foundationPotential_pathClass k φ hG
  obtain ⟨F⟩ := triangle333.unrolledJacobian_isomorphism_of_potentialPathClass k
    ((hG.asRegular triangle333 k φ).foundationPotential _ triangle333) φ h
  exact ⟨F.symm⟩

theorem triangleGinzburgFoundationRegularPotential_pathClass
    (φ : GinzburgRegularPotential k triangle333) :
    (triangleGinzburgFoundationRegularPotential k φ.val φ.property).pathAutomorphismClass
        k triangle333 = φ.pathAutomorphismClass k triangle333 := by
  apply (GinzburgRegularPotential.pathAutomorphismClass_eq_iff_smul k triangle333 _ φ).mpr
  exact triangleGinzburgRegular_foundationPotential_pathAutomorphism k φ.val φ.property

theorem triangleGinzburgRegular_foundationCandidate_recovery
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) :
    ∃ ψ : GinzburgRegularPotential k triangle333,
      ψ.val = (hG.asRegular triangle333 k φ).foundationPotential _ triangle333 ∧
      Nonempty (ZAlgebra.Isomorphism (triangle333.unrolledJacobianZAlgebra k φ)
        (triangle333.unrolledJacobianZAlgebra k ψ.val)) :=
  ⟨triangleGinzburgFoundationRegularPotential k φ hG,rfl,
    triangleGinzburgFoundationRegularPotential_recovery k φ hG⟩

end ASGinzburg
