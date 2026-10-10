import work.ASGinzburgDraft.ZeroCutJacobianIsomorphismLeadingMaps
import work.ASGinzburgDraft.PathSubstitutionAutomorphismCriteria
import work.ASGinzburgDraft.PathAutomorphismUnrolling
import work.ASGinzburgDraft.ZAlgebraFoundationIsomorphism

/-! Genuine foundation isomorphisms lift to vertex- and cut-preserving
free-path automorphisms. The lift intertwines the given isomorphism on
the entire zero-cut foundation and fixes every cut arrow. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def VertexCutPathAutomorphism.zeroCutPathAlgEquiv
    (E : Q.VertexCutPathAutomorphism k) : Q.ZeroCutPathRing k ≃ₐ[k] Q.ZeroCutPathRing k :=
  (Q.zeroCutPathComponentAlgebra k).totalAlgEquivOfComponents (Q.zeroCutPathComponentAlgebra k)
    (fun i j => VertexCutPathAutomorphism.cutComponentLinearEquiv Q k E i j 0)
    (by
      intro i
      apply Subtype.ext
      exact (Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_id E.val
        (VertexCutPathAutomorphism.fixes_vertex Q k E) i)
    (by
      intro i j l f g
      apply Subtype.ext
      exact (Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_comp E.val
        (VertexCutPathAutomorphism.fixes_vertex Q k E) f.val g.val)

theorem VertexCutPathAutomorphism.zeroCutPathAlgEquiv_apply
    (E : Q.VertexCutPathAutomorphism k) (x : Q.ZeroCutPathRing k) (i j : Q.Vertex) :
    VertexCutPathAutomorphism.zeroCutPathAlgEquiv Q k E x i j =
      VertexCutPathAutomorphism.cutComponentLinearEquiv Q k E i j 0 (x i j) := rfl

theorem VertexCutPathAutomorphism.zeroCutPathAlgEquiv_vertex
    (E : Q.VertexCutPathAutomorphism k) (i : Q.Vertex) :
    VertexCutPathAutomorphism.zeroCutPathAlgEquiv Q k E
      ((Q.zeroCutPathComponentAlgebra k).totalIdempotent i) =
        (Q.zeroCutPathComponentAlgebra k).totalIdempotent i := by
  classical
  funext p q
  rw [VertexCutPathAutomorphism.zeroCutPathAlgEquiv_apply]
  by_cases hp : p = i
  · subst p
    by_cases hq : q = i
    · subst q
      simp only [LinearComponentAlgebra.totalIdempotent,
        LinearComponentAlgebra.totalComponent_apply_same]
      apply Subtype.ext
      exact (Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_id E.val
        (VertexCutPathAutomorphism.fixes_vertex Q k E) i
    · simp [LinearComponentAlgebra.totalIdempotent,
        LinearComponentAlgebra.totalComponent,hq]
  · simp [LinearComponentAlgebra.totalIdempotent,
      LinearComponentAlgebra.totalComponent,hp]

noncomputable def zeroCutJacobianFoundationAlgHom (φ : Q.Potential k) :
    Q.ZeroCutPathRing k →ₐ[k] (Q.unrolledJacobianZAlgebra k φ).FoundationAlgebra Q :=
  (Q.zeroCutPathComponentAlgebra k).totalAlgHomOfComponents
    ((Q.unrolledJacobianZAlgebra k φ).foundationComponents Q)
    (Q.zeroCutJacobianComponentProjection k φ)
    (Q.zeroCutJacobianComponentProjection_id k φ)
    (Q.zeroCutJacobianComponentProjection_comp k φ)

variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))

noncomputable def zeroCutIsomorphismPathAutomorphism : Q.VertexCutPathAutomorphism k :=
  Q.invertibleLeadingPathSubstitutionAutomorphism k (Q.zeroCutIsomorphismArrowReplacement k F)
    (Q.zeroCutIsomorphismArrowReplacement_mem_cut k F)
    (Q.zeroCutIsomorphismSubstitution_leading_bijective k F)

theorem zeroCutIsomorphismPathAutomorphism_arrow (a : Q.Arrow) :
    VertexCutPathAutomorphism.arrowReplacement Q k (Q.zeroCutIsomorphismPathAutomorphism k F) a =
      Q.zeroCutIsomorphismArrowReplacement k F a :=
  Q.invertibleLeadingPathSubstitutionAutomorphism_arrow k _ _ _ a

theorem zeroCutIsomorphismPathAutomorphism_cut_arrow (a : Q.Arrow) (ha : Q.cut a = true) :
    VertexCutPathAutomorphism.arrowReplacement Q k (Q.zeroCutIsomorphismPathAutomorphism k F) a =
      Q.pathIdentityArrowReplacement k a := by
  rw [Q.zeroCutIsomorphismPathAutomorphism_arrow,Q.zeroCutIsomorphismArrowReplacement_cut k F a ha]

theorem zeroCutIsomorphismPathAutomorphism_projection (i j : Q.Vertex)
    (f : Q.pathCutComponent k i j 0) :
    Q.zeroCutJacobianComponentProjection k ψ i j
      (VertexCutPathAutomorphism.cutComponentLinearEquiv Q k
        (Q.zeroCutIsomorphismPathAutomorphism k F) i j 0 f) =
      F.map _ _ (Q.zeroCutJacobianComponentProjection k φ i j f) := by
  have H : VertexCutPathAutomorphism.cutComponentLinearEquiv Q k
      (Q.zeroCutIsomorphismPathAutomorphism k F) i j 0 f =
        Q.pathCutSubstitution k (Q.zeroCutIsomorphismArrowReplacement k F)
          (Q.zeroCutIsomorphismArrowReplacement_mem_cut k F) i j 0 f := by
    apply Subtype.ext
    exact VertexCutPathAutomorphism.component_of_substitution Q k _ _
      (Q.invertibleLeadingPathSubstitutionAutomorphism_toAlgHom k _ _ _) i j f.val
  rw [H]
  exact Q.zeroCutIsomorphismSubstitution_projection k F i j f

theorem zeroCutIsomorphismPathAutomorphism_jacobian_mem_iff (i j : Q.Vertex)
    (f : Q.pathCutComponent k i j 0) :
    (VertexCutPathAutomorphism.cutComponentLinearEquiv Q k
      (Q.zeroCutIsomorphismPathAutomorphism k F) i j 0 f).val ∈
        (Q.pathJacobianIdeal k ψ).hom i j ↔
      f.val ∈ (Q.pathJacobianIdeal k φ).hom i j := by
  rw [← Q.zeroCutJacobianComponentProjection_eq_zero_iff,
    Q.zeroCutIsomorphismPathAutomorphism_projection,
    ← Q.zeroCutJacobianComponentProjection_eq_zero_iff]
  exact (F.map (i.val : ℤ) (j.val : ℤ)).map_eq_zero_iff

noncomputable def zeroCutIsomorphismFreePathAlgEquiv : Q.ZeroCutPathRing k ≃ₐ[k] Q.ZeroCutPathRing k :=
  VertexCutPathAutomorphism.zeroCutPathAlgEquiv Q k (Q.zeroCutIsomorphismPathAutomorphism k F)

theorem zeroCutIsomorphismFreePathAlgEquiv_intertwines (x : Q.ZeroCutPathRing k) :
    Q.zeroCutJacobianFoundationAlgHom k ψ (Q.zeroCutIsomorphismFreePathAlgEquiv k F x) =
      F.foundationAlgEquiv Q (Q.zeroCutJacobianFoundationAlgHom k φ x) := by
  funext i j
  exact Q.zeroCutIsomorphismPathAutomorphism_projection k F i j (x i j)

end ASGinzburg.CutQuiver
