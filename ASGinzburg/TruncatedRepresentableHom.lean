import ASGinzburg.TruncatedRepresentables

/-!
# Recover algebra components, identity and product from actual truncated representables
-/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def rightTruncatedRepresentableHomComponentEquiv (l i j : ℤ) (hli : l ≤ i) :
    A.Hom i j ≃ₗ[k] (A.rightTruncatedRepresentable l i ⟶ A.rightTruncatedRepresentable l j) :=
  (A.rightTruncatedRepresentableComponentIso l j i hli).toLinearEquiv.symm.trans
    (A.rightTruncatedRepresentableYonedaEquiv l i (A.rightTruncatedRepresentable l j)
      (A.rightTruncatedRepresentable_below l j)).symm

theorem rightTruncatedRepresentableHomComponentEquiv_yoneda (l i j : ℤ) (hli : l ≤ i)
    (x : A.Hom i j) :
    A.rightTruncatedRepresentableYonedaEquiv l i (A.rightTruncatedRepresentable l j)
        (A.rightTruncatedRepresentable_below l j)
        (A.rightTruncatedRepresentableHomComponentEquiv l i j hli x) =
      (A.rightModuleEvaluation i).map (A.rightTruncatedRepresentableπ l j) x := by
  unfold rightTruncatedRepresentableHomComponentEquiv
  rw [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  rfl

@[reassoc] theorem rightTruncatedRepresentableHomComponentEquiv_π (l i j : ℤ) (hli : l ≤ i)
    (x : A.Hom i j) :
    A.rightTruncatedRepresentableπ l i ≫ A.rightTruncatedRepresentableHomComponentEquiv l i j hli x =
      A.representableToElement i (A.representable j) x ≫ A.rightTruncatedRepresentableπ l j := by
  apply (A.representableYonedaEquiv i (A.rightTruncatedRepresentable l j)).injective
  change A.rightTruncatedRepresentableYonedaEquiv l i (A.rightTruncatedRepresentable l j)
    (A.rightTruncatedRepresentable_below l j) (A.rightTruncatedRepresentableHomComponentEquiv l i j hli x) = _
  rw [A.rightTruncatedRepresentableHomComponentEquiv_yoneda,A.representableYonedaEquiv_comp]
  exact congrArg ((A.rightModuleEvaluation i).map (A.rightTruncatedRepresentableπ l j))
    ((A.representableYonedaEquiv i (A.representable j)).apply_symm_apply x).symm

theorem representableToElement_identity (i : ℤ) :
    A.representableToElement i (A.representable i) (A.id i) = 𝟙 (A.representable i) := by
  apply (A.representableYonedaEquiv i (A.representable i)).injective
  exact (A.representableYonedaEquiv i (A.representable i)).apply_symm_apply _

theorem representableToElement_composition (i j m : ℤ) (f : A.Hom i j) (g : A.Hom j m) :
    A.representableToElement i (A.representable m) (A.comp g f) =
      A.representableToElement i (A.representable j) f ≫ A.representableToElement j (A.representable m) g := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (A.comp_assoc x f g).symm

theorem rightTruncatedRepresentableHomComponentEquiv_id (l i : ℤ) (hli : l ≤ i) :
    A.rightTruncatedRepresentableHomComponentEquiv l i i hli (A.id i) = 𝟙 _ := by
  apply (cancel_epi (A.rightTruncatedRepresentableπ l i)).mp
  rw [A.rightTruncatedRepresentableHomComponentEquiv_π,A.representableToElement_identity]
  simp

theorem rightTruncatedRepresentableHomComponentEquiv_comp (l i j m : ℤ)
    (hli : l ≤ i) (hlj : l ≤ j) (f : A.Hom i j) (g : A.Hom j m) :
    A.rightTruncatedRepresentableHomComponentEquiv l i m hli (A.comp g f) =
      A.rightTruncatedRepresentableHomComponentEquiv l i j hli f ≫
        A.rightTruncatedRepresentableHomComponentEquiv l j m hlj g := by
  apply (cancel_epi (A.rightTruncatedRepresentableπ l i)).mp
  rw [A.rightTruncatedRepresentableHomComponentEquiv_π,← Category.assoc,
    A.rightTruncatedRepresentableHomComponentEquiv_π,Category.assoc,
    A.rightTruncatedRepresentableHomComponentEquiv_π,A.representableToElement_composition]
  exact Category.assoc _ _ _
end ASGinzburg.ZAlgebra
