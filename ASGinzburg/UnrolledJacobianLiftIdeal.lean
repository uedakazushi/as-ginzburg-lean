import ASGinzburg.UnrolledJacobianIdealErasure

/-! The genuine integer-indexed unrolled Jacobian ideal pulled back
to actual lifted vertices, with product closure and all relations. -/
namespace ASGinzburg.CutQuiver
open ZAlgebra
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledEndpointEquiv_comp {u v w u' v' w' : Q.LiftVertex}
    (hu : u=u') (hv : v=v') (hw : w=w')
    (f : Q.UnrolledPathComponent k u v) (g : Q.UnrolledPathComponent k v w) :
    Finsupp.mapDomain (UnrolledPath.endpointEquiv Q hu hw) (Q.unrolledPathComp k g f)=
      Q.unrolledPathComp k (Finsupp.mapDomain (UnrolledPath.endpointEquiv Q hv hw) g)
        (Finsupp.mapDomain (UnrolledPath.endpointEquiv Q hu hv) f) := by
  subst u' v' w'
  change Finsupp.mapDomain id (Q.unrolledPathComp k g f)=
    Q.unrolledPathComp k (Finsupp.mapDomain id g) (Finsupp.mapDomain id f)
  simp only [Finsupp.mapDomain_id]

theorem unrolledComponentHeightEquiv_comp {u v w : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k u v) (g : Q.UnrolledPathComponent k v w) :
    Q.unrolledComponentHeightEquiv k u w (Q.unrolledPathComp k g f)=
      (Q.unrolledPathZAlgebra k).comp (Q.unrolledComponentHeightEquiv k v w g)
        (Q.unrolledComponentHeightEquiv k u v f) :=
  Q.unrolledEndpointEquiv_comp k (Q.heightEquiv_symm_height u).symm
    (Q.heightEquiv_symm_height v).symm (Q.heightEquiv_symm_height w).symm f g

noncomputable def unrolledJacobianLiftIdeal (φ : Q.Potential k) (u v : Q.LiftVertex) :
    Submodule k (Q.UnrolledPathComponent k u v) :=
  ((Q.unrolledJacobianIdeal k φ).hom (Q.height u) (Q.height v)).comap
    (Q.unrolledComponentHeightEquiv k u v).toLinearMap

theorem unrolledJacobianLiftIdeal_comp_left (φ : Q.Potential k) {u v w : Q.LiftVertex}
    {f : Q.UnrolledPathComponent k u v} (hf : f ∈ Q.unrolledJacobianLiftIdeal k φ u v)
    (g : Q.UnrolledPathComponent k v w) :
    Q.unrolledPathComp k g f ∈ Q.unrolledJacobianLiftIdeal k φ u w := by
  change Q.unrolledComponentHeightEquiv k u w (Q.unrolledPathComp k g f) ∈
    (Q.unrolledJacobianIdeal k φ).hom (Q.height u) (Q.height w)
  rw [Q.unrolledComponentHeightEquiv_comp]
  exact (Q.unrolledJacobianIdeal k φ).comp_left hf _

theorem unrolledJacobianLiftIdeal_comp_right (φ : Q.Potential k) {u v w : Q.LiftVertex}
    {g : Q.UnrolledPathComponent k v w} (hg : g ∈ Q.unrolledJacobianLiftIdeal k φ v w)
    (f : Q.UnrolledPathComponent k u v) :
    Q.unrolledPathComp k g f ∈ Q.unrolledJacobianLiftIdeal k φ u w := by
  change Q.unrolledComponentHeightEquiv k u w (Q.unrolledPathComp k g f) ∈
    (Q.unrolledJacobianIdeal k φ).hom (Q.height u) (Q.height w)
  rw [Q.unrolledComponentHeightEquiv_comp]
  exact (Q.unrolledJacobianIdeal k φ).comp_right hg _

theorem unrolledJacobianRelation_mem_liftIdeal (φ : Q.Potential k) (a : Q.Arrow) (m : ℤ) :
    Q.unrolledJacobianRelation k a φ m ∈ Q.unrolledJacobianLiftIdeal k φ
      (Q.target a,m) (Q.source a,m+((1-Q.cutDegree a:ℕ):ℤ)) := by
  apply LinearIdeal.subset_generated
  exact ⟨a,m,rfl,rfl,rfl⟩

theorem unrolledJacobianLiftIdeal_erase (φ : Q.Potential k) {u v : Q.LiftVertex}
    {f : Q.UnrolledPathComponent k u v} (hf : f ∈ Q.unrolledJacobianLiftIdeal k φ u v) :
    Q.unrolledPathEraseLinearMap k u v f ∈ (Q.pathJacobianIdeal k φ).hom u.1 v.1 := by
  apply (Q.unrolledComponentHeightEquiv_mem_erasureIdeal k _ u v f).mp
  exact Q.unrolledJacobianIdeal_le_erasureIdeal k φ _ _ hf

end ASGinzburg.CutQuiver
