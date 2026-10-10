import work.ASGinzburgDraft.ZeroCutFoundationComponentAutomorphism
import work.ASGinzburgDraft.ZeroCutJacobianIsomorphismPathLift
import Mathlib.Algebra.Module.Submodule.Equiv

/-! The genuine zero-cut lift transports the actual native Jacobian
ideal in each foundation component, without any all-sheet condition. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))

theorem zeroCutIsomorphismJacobianComponent_mem_iff (i j : Q.Vertex)
    (f : (Q.unrolledPathZAlgebra k).Hom (i.val : ℤ) (j.val : ℤ)) :
    VertexCutPathAutomorphism.foundationPathComponentLinearEquiv Q k
      (Q.zeroCutIsomorphismPathAutomorphism k F) i j f ∈
        (Q.unrolledJacobianIdeal k ψ).hom (i.val : ℤ) (j.val : ℤ) ↔
    f ∈ (Q.unrolledJacobianIdeal k φ).hom (i.val : ℤ) (j.val : ℤ) := by
  obtain ⟨f, rfl⟩ := (Q.zeroCutFoundationComponentEquiv k i j).surjective f
  rw [VertexCutPathAutomorphism.foundationPathComponentLinearEquiv_on_cut,
    ← Q.unrolledJacobianQuotientMap_kernel k ψ, ← Q.unrolledJacobianQuotientMap_kernel k φ]
  change Q.zeroCutJacobianComponentProjection k ψ i j
    (VertexCutPathAutomorphism.cutComponentLinearEquiv Q k
      (Q.zeroCutIsomorphismPathAutomorphism k F) i j 0 f) = 0 ↔
      Q.zeroCutJacobianComponentProjection k φ i j f = 0
  rw [Q.zeroCutIsomorphismPathAutomorphism_projection]
  exact (F.map (i.val : ℤ) (j.val : ℤ)).map_eq_zero_iff

theorem zeroCutIsomorphismJacobianComponent_map (i j : Q.Vertex) :
    ((Q.unrolledJacobianIdeal k φ).hom (i.val : ℤ) (j.val : ℤ)).map
      (VertexCutPathAutomorphism.foundationPathComponentLinearEquiv Q k
        (Q.zeroCutIsomorphismPathAutomorphism k F) i j).toLinearMap =
    (Q.unrolledJacobianIdeal k ψ).hom (i.val : ℤ) (j.val : ℤ) := by
  apply Submodule.ext
  intro f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (Q.zeroCutIsomorphismJacobianComponent_mem_iff k F i j g).mpr hg
  · intro hf
    let E := VertexCutPathAutomorphism.foundationPathComponentLinearEquiv Q k
      (Q.zeroCutIsomorphismPathAutomorphism k F) i j
    refine ⟨E.symm f, ?_, E.apply_symm_apply f⟩
    apply (Q.zeroCutIsomorphismJacobianComponent_mem_iff k F i j (E.symm f)).mp
    change E (E.symm f) ∈ _
    simpa only [LinearEquiv.apply_symm_apply] using hf

noncomputable def zeroCutIsomorphismJacobianComponentLinearEquiv (i j : Q.Vertex) :
    (Q.unrolledJacobianIdeal k φ).hom (i.val : ℤ) (j.val : ℤ) ≃ₗ[k]
      (Q.unrolledJacobianIdeal k ψ).hom (i.val : ℤ) (j.val : ℤ) :=
  (VertexCutPathAutomorphism.foundationPathComponentLinearEquiv Q k
    (Q.zeroCutIsomorphismPathAutomorphism k F) i j).ofSubmodules _ _
      (Q.zeroCutIsomorphismJacobianComponent_map k F i j)

theorem zeroCutIsomorphismJacobianComponentLinearEquiv_val (i j : Q.Vertex)
    (f : (Q.unrolledJacobianIdeal k φ).hom (i.val : ℤ) (j.val : ℤ)) :
    (Q.zeroCutIsomorphismJacobianComponentLinearEquiv k F i j f).val =
      VertexCutPathAutomorphism.foundationPathComponentLinearEquiv Q k
        (Q.zeroCutIsomorphismPathAutomorphism k F) i j f.val :=
  LinearEquiv.ofSubmodules_apply _ _ f

end ASGinzburg.CutQuiver
