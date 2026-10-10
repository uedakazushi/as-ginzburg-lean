import work.ASGinzburgDraft.TriangleASFoundationPotentialIsomorphismOrbits
import work.ASGinzburgDraft.TriangleGinzburgFoundationPotentialRegularity

/-! The genuine source-image regularity and recovery results extend to
every triangle AS algebra actually isomorphic to a regular Jacobian.
Neither candidate regularity nor candidate recovery is an assumption. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem triangleASRegular_Isomorphism_foundationPotential_ginzburgRegular_iff
    (A B : ZAlgebra.{u,u} k) (F : ZAlgebra.Isomorphism A B)
    (hAS : A.ASRegular triangle333) (hBS : B.ASRegular triangle333) :
    triangle333.GinzburgRegular k (hAS.foundationPotential A triangle333) ↔
      triangle333.GinzburgRegular k (hBS.foundationPotential B triangle333) := by
  obtain ⟨E,hE⟩ :=
    triangleASRegular_Isomorphism_foundationPotential_pathAutomorphism k A B F hAS hBS
  have h := triangleGinzburgRegular_pathAutomorphism_iff k E
    (hAS.foundationPotential A triangle333)
  rw [hE] at h
  exact h

theorem triangleASRegular_isomorphicJacobian_foundationPotential_pathClass
    (A : ZAlgebra.{u,u} k) (hAS : A.ASRegular triangle333)
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ)
    (F : ZAlgebra.Isomorphism A (triangle333.unrolledJacobianZAlgebra k φ)) :
    triangle333.potentialPathAutomorphismClass k (hAS.foundationPotential A triangle333) =
      triangle333.potentialPathAutomorphismClass k φ := by
  exact (triangleASRegular_Isomorphism_foundationPotential_pathClass k A
    (triangle333.unrolledJacobianZAlgebra k φ) F hAS (hG.asRegular triangle333 k φ)).trans
      (triangleGinzburgRegular_foundationPotential_pathClass k φ hG)

theorem triangleASRegular_isomorphicJacobian_foundationPotential_ginzburgRegular
    (A : ZAlgebra.{u,u} k) (hAS : A.ASRegular triangle333)
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ)
    (F : ZAlgebra.Isomorphism A (triangle333.unrolledJacobianZAlgebra k φ)) :
    triangle333.GinzburgRegular k (hAS.foundationPotential A triangle333) := by
  apply (triangleASRegular_Isomorphism_foundationPotential_ginzburgRegular_iff k A
    (triangle333.unrolledJacobianZAlgebra k φ) F hAS (hG.asRegular triangle333 k φ)).mpr
  exact triangleGinzburgRegular_foundationPotential_ginzburgRegular k φ hG

theorem triangleASRegular_isomorphicJacobian_foundationPotential_recovery
    (A : ZAlgebra.{u,u} k) (hAS : A.ASRegular triangle333)
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ)
    (F : ZAlgebra.Isomorphism A (triangle333.unrolledJacobianZAlgebra k φ)) :
    Nonempty (ZAlgebra.Isomorphism A (triangle333.unrolledJacobianZAlgebra k
      (hAS.foundationPotential A triangle333))) := by
  obtain ⟨G⟩ := triangle333.unrolledJacobian_isomorphism_of_potentialPathClass k
    (hAS.foundationPotential A triangle333) φ
    (triangleASRegular_isomorphicJacobian_foundationPotential_pathClass k A hAS φ hG F)
  exact ⟨F.trans G.symm⟩

theorem triangleASRegular_isomorphicJacobian_foundationCandidate_recovery
    (A : ZAlgebra.{u,u} k) (hAS : A.ASRegular triangle333)
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ)
    (F : ZAlgebra.Isomorphism A (triangle333.unrolledJacobianZAlgebra k φ)) :
    ∃ ψ : GinzburgRegularPotential k triangle333,
      ψ.val = hAS.foundationPotential A triangle333 ∧
      Nonempty (ZAlgebra.Isomorphism A (triangle333.unrolledJacobianZAlgebra k ψ.val)) := by
  refine ⟨⟨hAS.foundationPotential A triangle333,
    triangleASRegular_isomorphicJacobian_foundationPotential_ginzburgRegular k A hAS φ hG F⟩,
    rfl, ?_⟩
  exact triangleASRegular_isomorphicJacobian_foundationPotential_recovery k A hAS φ hG F

end ASGinzburg
