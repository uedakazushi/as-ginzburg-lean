import ASGinzburg.UnrolledErasureIdeals
import ASGinzburg.UnrolledJacobianErasure
import ASGinzburg.UnrolledJacobianAlgebra
import ASGinzburg.PathJacobianIdeal

/-! Every actual unrolled Jacobian relation and the genuine ideal it
generates maps into the original Jacobian ideal under forgetting sheets. -/
namespace ASGinzburg.CutQuiver
open ZAlgebra
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledEndpointEquiv_mem_erasureIdeal (I : Q.PathLinearIdeal k)
    {u v u' v' : Q.LiftVertex} (hu : u=u') (hv : v=v')
    (f : Q.UnrolledPathComponent k u v) :
    Q.unrolledPathEraseLinearMap k u' v'
      (Finsupp.mapDomain (UnrolledPath.endpointEquiv Q hu hv) f) ∈ I.hom u'.1 v'.1 ↔
        Q.unrolledPathEraseLinearMap k u v f ∈ I.hom u.1 v.1 := by
  subst u' v'
  change Q.unrolledPathEraseLinearMap k u v (Finsupp.mapDomain id f) ∈ I.hom u.1 v.1 ↔ _
  rw [Finsupp.mapDomain_id]

theorem unrolledComponentHeightEquiv_mem_erasureIdeal (I : Q.PathLinearIdeal k)
    (u v : Q.LiftVertex) (f : Q.UnrolledPathComponent k u v) :
    Q.unrolledComponentHeightEquiv k u v f ∈ (Q.unrolledErasureIdeal k I).hom
      (Q.height u) (Q.height v) ↔ Q.unrolledPathEraseLinearMap k u v f ∈ I.hom u.1 v.1 := by
  exact Q.unrolledEndpointEquiv_mem_erasureIdeal k I
    (Q.heightEquiv_symm_height u).symm (Q.heightEquiv_symm_height v).symm f

theorem jacobianGenerators_mem_erasureIdeal (φ : Q.Potential k) (i j : ℤ) :
    Q.jacobianGenerators k φ i j ⊆
      (Q.unrolledErasureIdeal k (Q.pathJacobianIdeal k φ)).hom i j := by
  rintro f ⟨a,m,hi,hj,rfl⟩
  subst i j
  apply (Q.unrolledComponentHeightEquiv_mem_erasureIdeal k _ _ _ _).mpr
  rw [Q.unrolledJacobianRelation_erase]
  exact Q.pathCyclicDerivative_mem_pathJacobianIdeal k φ a

theorem unrolledJacobianIdeal_le_erasureIdeal (φ : Q.Potential k) (i j : ℤ) :
    (Q.unrolledJacobianIdeal k φ).hom i j ≤
      (Q.unrolledErasureIdeal k (Q.pathJacobianIdeal k φ)).hom i j :=
  LinearIdeal.generated_le _ _ (Q.jacobianGenerators_mem_erasureIdeal k φ) i j

end ASGinzburg.CutQuiver
