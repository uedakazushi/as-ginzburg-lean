import ASGinzburg.PathJacobianRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The finite component Jacobian algebra is an actual quotient of
the full path ring by precisely the genuine component Jacobian ideal. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathQuotientRingMap_eq_zero_iff (I : Q.PathLinearIdeal k) (x : Q.PathRing k) :
    Q.pathQuotientRingMap k I x=0 ↔ ∀ i j, x i j ∈ I.hom i j := by
  constructor
  · intro h i j
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact congrFun (congrFun h i) j
  · intro h
    funext i j
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h i j)

noncomputable def pathQuotientRingKernelAlgEquiv (I : Q.PathLinearIdeal k) :
    (Q.PathRing k ⧸ RingHom.ker (Q.pathQuotientRingMap k I).toRingHom) ≃ₐ[k]
      Q.PathQuotientRing k I :=
  Ideal.quotientKerAlgEquivOfSurjective (Q.pathQuotientRingMap_surjective k I)

theorem pathJacobianRingMap_eq_zero_iff (φ : Q.Potential k) (x : Q.PathRing k) :
    Q.pathJacobianRingMap k φ x=0 ↔ ∀ i j, x i j ∈ (Q.pathJacobianIdeal k φ).hom i j :=
  Q.pathQuotientRingMap_eq_zero_iff k _ x

noncomputable def pathJacobianRingKernelAlgEquiv (φ : Q.Potential k) :
    (Q.PathRing k ⧸ RingHom.ker (Q.pathJacobianRingMap k φ).toRingHom) ≃ₐ[k]
      Q.PathJacobianRing k φ :=
  Q.pathQuotientRingKernelAlgEquiv k _

end ASGinzburg.CutQuiver
