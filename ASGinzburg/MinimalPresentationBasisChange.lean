import ASGinzburg.MinimalPresentationArrowLifts
import ASGinzburg.MinimalPresentationIndecomposables
import ASGinzburg.IndecomposableGeneration
import ASGinzburg.ASArbitraryBasisPresentation

/-! Actual arbitrary incoming bases give free-path automorphisms commuting
with the original minimal presentation and transporting its actual kernel.
Period-coherent descent to the finite cut quiver remains a separate task. -/
namespace ASGinzburg.ZAlgebra.MinimalPathPresentation
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}

theorem basisChange_indecomposable_commutes (F : A.MinimalPathPresentation Q)
    (B : A.IncomingBasisSystem Q) (i j : ℤ)
    (x : (Q.unrolledPathZAlgebra k).Hom i j ⧸
      Submodule.span k ((Q.unrolledPathZAlgebra k).products i j)) :
    F.indecomposableEquiv i j
      ((F.arrowSubstitution B.incomingElement).indecomposableMap i j x)=
        (B.minimalPathPresentation A Q).indecomposableEquiv i j x := by
  obtain ⟨f,rfl⟩ := (Submodule.span k
    ((Q.unrolledPathZAlgebra k).products i j)).mkQ_surjective x
  change F.indecomposableEquiv i j
    ((F.arrowSubstitution B.incomingElement).indecomposableMap i j
      (Submodule.Quotient.mk f))=
    (B.minimalPathPresentation A Q).indecomposableEquiv i j (Submodule.Quotient.mk f)
  rw [Homomorphism.indecomposableMap_apply_mk,
    indecomposableEquiv_apply_mk,indecomposableEquiv_apply_mk,
    F.arrowSubstitution_commutes]
  rfl

theorem basisChange_indecomposable_surjective (F : A.MinimalPathPresentation Q)
    (B : A.IncomingBasisSystem Q) (i j : ℤ) :
    Function.Surjective ((F.arrowSubstitution B.incomingElement).indecomposableMap i j) := by
  intro x
  refine ⟨((B.minimalPathPresentation A Q).indecomposableEquiv i j).symm
    (F.indecomposableEquiv i j x),?_⟩
  apply (F.indecomposableEquiv i j).injective
  rw [F.basisChange_indecomposable_commutes]
  exact LinearEquiv.apply_symm_apply _ _

noncomputable def basisChangeIsomorphism (F : A.MinimalPathPresentation Q)
    (B : A.IncomingBasisSystem Q) :
    Isomorphism (Q.unrolledPathZAlgebra k) (Q.unrolledPathZAlgebra k) :=
  (F.arrowSubstitution B.incomingElement).isomorphismOfIndecomposableSurjective
    (fun i j _ => F.basisChange_indecomposable_surjective B i j)

theorem basisChangeIsomorphism_commutes (F : A.MinimalPathPresentation Q)
    (B : A.IncomingBasisSystem Q) (i j : ℤ)
    (f : (Q.unrolledPathZAlgebra k).Hom i j) :
    F.presentation.map i j ((F.basisChangeIsomorphism B).map i j f)=
      (B.minimalPathPresentation A Q).presentation.map i j f :=
  F.arrowSubstitution_commutes B.incomingElement i j f

theorem basisChangeIsomorphism_kernel (F : A.MinimalPathPresentation Q)
    (B : A.IncomingBasisSystem Q) (i j : ℤ) :
    (B.minimalPathPresentation A Q).presentation.kernel.hom i j=
      Submodule.comap ((F.basisChangeIsomorphism B).map i j).toLinearMap
        (F.presentation.kernel.hom i j) := by
  ext f
  change ((B.minimalPathPresentation A Q).presentation.map i j f=0) ↔
    (F.presentation.map i j ((F.basisChangeIsomorphism B).map i j f)=0)
  rw [F.basisChangeIsomorphism_commutes]

end ASGinzburg.ZAlgebra.MinimalPathPresentation
