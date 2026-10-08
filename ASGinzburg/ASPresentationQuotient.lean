import ASGinzburg.ASPresentationKernel
import ASGinzburg.ZAlgebraIsomorphisms

/-! The original AS algebra is the actual quotient of its free path
presentation by its genuine kernel ideal. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.presentationQuotientIso (hAS : A.ASRegular Q) :
    Isomorphism
      ((hAS.unrolledPathPresentation A Q).kernel.quotient
        (hAS.unrolledPathPresentation A Q).kernel_diagonal_eq_bot) A :=
  (hAS.unrolledPathPresentation A Q).quotientKernelIso
    (hAS.unrolledPathPresentation_surjective A Q)

theorem ASRegular.presentationQuotientIso_apply_mk (hAS : A.ASRegular Q)
    {i j : ℤ} (f : (Q.unrolledPathZAlgebra k).Hom i j) :
    (hAS.presentationQuotientIso A Q).map i j (Submodule.Quotient.mk f) =
      (hAS.unrolledPathPresentation A Q).map i j f := rfl

end ASGinzburg.ZAlgebra

namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledPathIdeal_diagonal_eq_bot (n : ℕ) (hn : 0<n) (i : ℤ) :
    (Q.unrolledPathIdeal k n).hom i i=⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  apply Finsupp.ext
  intro p
  apply (Finsupp.mem_supported' k f).mp hf
  change ¬n ≤ p.length
  rw [p.diagonal_eq_nil]
  simpa only [UnrolledPath.length] using Nat.not_le.mpr hn

theorem ideal_diagonal_eq_bot_of_le_arrow_square
    (I : (Q.unrolledPathZAlgebra k).LinearIdeal)
    (hI : ∀ i j, I.hom i j ≤
      ((Q.unrolledArrowIdeal k).mul (Q.unrolledArrowIdeal k)).hom i j) (i : ℤ) :
    I.hom i i=⊥ := by
  apply eq_bot_iff.mpr
  have H := hI i i
  rw [Q.unrolledArrowIdeal_square k,Q.unrolledPathIdeal_diagonal_eq_bot k 2 (by omega)] at H
  exact H

end ASGinzburg.CutQuiver
