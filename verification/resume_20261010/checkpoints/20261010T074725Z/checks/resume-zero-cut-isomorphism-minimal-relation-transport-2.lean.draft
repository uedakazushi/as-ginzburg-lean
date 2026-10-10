import work.ASGinzburgDraft.ZeroCutIsomorphismJacobianComponentTransport
import work.ASGinzburgDraft.FoundationIdealComponentTransport
import Mathlib.LinearAlgebra.Quotient.Basic

/-! A genuine native Jacobian Z-algebra isomorphism transports the
actual minimal relation quotient in each sheet-zero component. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))

theorem zeroCutIsomorphismRelationDecomposables_map (i j : Q.Vertex) :
    (Q.relationDecomposables (Q.unrolledJacobianIdeal k φ) (i.val : ℤ) (j.val : ℤ)).map
      (VertexCutPathAutomorphism.foundationPathComponentLinearEquiv Q k
        (Q.zeroCutIsomorphismPathAutomorphism k F) i j).toLinearMap =
    Q.relationDecomposables (Q.unrolledJacobianIdeal k ψ) (i.val : ℤ) (j.val : ℤ) := by
  apply Q.foundationRelationDecomposables_component_map k
    (fun i j => VertexCutPathAutomorphism.foundationPathComponentLinearEquiv Q k
      (Q.zeroCutIsomorphismPathAutomorphism k F) i j)
  · intro i j l f g
    exact VertexCutPathAutomorphism.foundationPathComponentLinearEquiv_comp Q k _ f g
  · exact Q.zeroCutIsomorphismJacobianComponent_mem_iff k F
  · intro i j f
    exact Q.unrolledArrowIdeal_linearEquiv_mem_iff k _ _ _ f

theorem zeroCutIsomorphismMinimalRelationDenominator_map (i j : Q.Vertex) :
    (Submodule.comap ((Q.unrolledJacobianIdeal k φ).hom (i.val : ℤ) (j.val : ℤ)).subtype
      (Q.relationDecomposables (Q.unrolledJacobianIdeal k φ) (i.val : ℤ) (j.val : ℤ))).map
        (Q.zeroCutIsomorphismJacobianComponentLinearEquiv k F i j).toLinearMap =
    Submodule.comap ((Q.unrolledJacobianIdeal k ψ).hom (i.val : ℤ) (j.val : ℤ)).subtype
      (Q.relationDecomposables (Q.unrolledJacobianIdeal k ψ) (i.val : ℤ) (j.val : ℤ)) := by
  let C := VertexCutPathAutomorphism.foundationPathComponentLinearEquiv Q k
    (Q.zeroCutIsomorphismPathAutomorphism k F) i j
  let E := Q.zeroCutIsomorphismJacobianComponentLinearEquiv k F i j
  have hD := Q.zeroCutIsomorphismRelationDecomposables_map k F i j
  apply Submodule.ext
  intro f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    change (E g).val ∈
      Q.relationDecomposables (Q.unrolledJacobianIdeal k ψ) (i.val : ℤ) (j.val : ℤ)
    rw [Q.zeroCutIsomorphismJacobianComponentLinearEquiv_val, ← hD]
    exact Submodule.mem_map.mpr ⟨g.val, hg, rfl⟩
  · intro hf
    refine ⟨E.symm f, ?_, E.apply_symm_apply f⟩
    change (E.symm f).val ∈
      Q.relationDecomposables (Q.unrolledJacobianIdeal k φ) (i.val : ℤ) (j.val : ℤ)
    have hCf : C ((E.symm f).val) ∈
        Q.relationDecomposables (Q.unrolledJacobianIdeal k ψ) (i.val : ℤ) (j.val : ℤ) := by
      rw [← Q.zeroCutIsomorphismJacobianComponentLinearEquiv_val]
      change (E (E.symm f)).val ∈
        Q.relationDecomposables (Q.unrolledJacobianIdeal k ψ) (i.val : ℤ) (j.val : ℤ)
      rw [E.apply_symm_apply]
      exact hf
    rw [← hD, Submodule.mem_map] at hCf
    rcases hCf with ⟨g, hg, heq⟩
    have hgf : g = (E.symm f).val := C.injective heq
    exact hgf ▸ hg

noncomputable def zeroCutIsomorphismMinimalRelationEquiv (i j : Q.Vertex) :
    Q.MinimalRelationComponent (Q.unrolledJacobianIdeal k φ) (i.val : ℤ) (j.val : ℤ) ≃ₗ[k]
      Q.MinimalRelationComponent (Q.unrolledJacobianIdeal k ψ) (i.val : ℤ) (j.val : ℤ) :=
  Submodule.Quotient.equiv _ _ (Q.zeroCutIsomorphismJacobianComponentLinearEquiv k F i j)
    (Q.zeroCutIsomorphismMinimalRelationDenominator_map k F i j)

theorem zeroCutIsomorphismMinimalRelationEquiv_mk (i j : Q.Vertex)
    (r : (Q.unrolledJacobianIdeal k φ).hom (i.val : ℤ) (j.val : ℤ)) :
    Q.zeroCutIsomorphismMinimalRelationEquiv k F i j (Submodule.Quotient.mk r) =
      Submodule.Quotient.mk (Q.zeroCutIsomorphismJacobianComponentLinearEquiv k F i j r) :=
  rfl

end ASGinzburg.CutQuiver
