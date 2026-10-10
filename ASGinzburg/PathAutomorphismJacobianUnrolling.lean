import ASGinzburg.PathAutomorphismUnrolling
import ASGinzburg.ZAlgebraIsomorphismQuotients
import ASGinzburg.UnrolledJacobianErasureEquality

/-! Actual homogeneous Jacobian compatibility transfers to the actual
unrolled Jacobian quotient. The input ideal compatibility is explicit;
the nonlinear cyclic derivative chain rule remains a separate obligation. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledJacobianIdeal_mem_iff_integer_erase
    (φ : Q.Potential k) (i j : ℤ) (f : (Q.unrolledPathZAlgebra k).Hom i j) :
    f ∈ (Q.unrolledJacobianIdeal k φ).hom i j ↔
      Q.unrolledPathEraseLinearMap k (Q.heightEquiv.symm i) (Q.heightEquiv.symm j) f ∈
        (Q.pathJacobianIdeal k φ).hom (Q.heightEquiv.symm i).1 (Q.heightEquiv.symm j).1 := by
  rw [Q.unrolledJacobianIdeal_eq_erasureIdeal k φ i j]
  rfl

variable (E : Q.VertexCutPathAutomorphism k) (φ ψ : Q.Potential k)
  (hE : ∀ i j (f : Q.PathComponent k i j),
    f ∈ (Q.pathJacobianIdeal k φ).hom i j ↔
      VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f ∈
        (Q.pathJacobianIdeal k ψ).hom i j)

include hE

theorem VertexCutPathAutomorphism.unrolledJacobianIdeal_mem
    (i j : ℤ) (f : (Q.unrolledPathZAlgebra k).Hom i j) :
    f ∈ (Q.unrolledJacobianIdeal k φ).hom i j ↔
      (VertexCutPathAutomorphism.unrolledPathZAlgebraIsomorphism Q k E).map i j f ∈
        (Q.unrolledJacobianIdeal k ψ).hom i j := by
  rw [Q.unrolledJacobianIdeal_mem_iff_integer_erase k φ,
    Q.unrolledJacobianIdeal_mem_iff_integer_erase k ψ]
  change _ ↔ Q.unrolledPathEraseLinearMap k _ _
    (VertexCutPathAutomorphism.unrolledComponentLinearEquiv Q k E _ _ f) ∈ _
  rw [VertexCutPathAutomorphism.unrolledComponentLinearEquiv_erase]
  exact hE _ _ _

theorem VertexCutPathAutomorphism.unrolledJacobianIdeal_map (i j : ℤ) :
    ((Q.unrolledJacobianIdeal k φ).hom i j).map
      ((VertexCutPathAutomorphism.unrolledPathZAlgebraIsomorphism Q k E).map i j).toLinearMap =
        (Q.unrolledJacobianIdeal k ψ).hom i j := by
  apply Submodule.ext
  intro f
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact (VertexCutPathAutomorphism.unrolledJacobianIdeal_mem Q k E φ ψ hE i j g).mp hg
  · intro hf
    obtain ⟨g,rfl⟩ :=
      ((VertexCutPathAutomorphism.unrolledPathZAlgebraIsomorphism Q k E).map i j).surjective f
    exact ⟨g,(VertexCutPathAutomorphism.unrolledJacobianIdeal_mem Q k E φ ψ hE i j g).mpr hf,rfl⟩

noncomputable def VertexCutPathAutomorphism.unrolledJacobianZAlgebraIsomorphism :
    ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ) (Q.unrolledJacobianZAlgebra k ψ) :=
  (VertexCutPathAutomorphism.unrolledPathZAlgebraIsomorphism Q k E).idealQuotientIsomorphism
    (Q.unrolledJacobianIdeal k φ) (Q.unrolledJacobianIdeal k ψ)
    (Q.unrolledJacobianIdeal_diagonal_eq_bot k φ) (Q.unrolledJacobianIdeal_diagonal_eq_bot k ψ)
    (VertexCutPathAutomorphism.unrolledJacobianIdeal_map Q k E φ ψ hE)

end ASGinzburg.CutQuiver
