import ASGinzburg.PeriodSheetComponents

/-! The transported basis vectors are the quotient classes of the
actual transported AS generator representatives, with explicit index
transport on the true product quotients. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def homTransportIndecomposableEquiv (i j i' j' : ℤ) (hi : i=i') (hj : j=j') :
    (A.Hom i j ⧸ Submodule.span k (A.products i j)) ≃ₗ[k]
      (A.Hom i' j' ⧸ Submodule.span k (A.products i' j')) := by
  subst i'
  subst j'
  exact LinearEquiv.refl k _

theorem homTransportIndecomposableEquiv_apply_mk (i j i' j' : ℤ)
    (hi : i=i') (hj : j=j') (f : A.Hom i j) :
    A.homTransportIndecomposableEquiv i j i' j' hi hj (Submodule.Quotient.mk f)=
      Submodule.Quotient.mk (A.homTransport i j i' j' hi hj f) := by
  subst i'
  subst j'
  rfl

namespace ASResolution
variable {A} {Q : CutQuiver} {w : Q.LiftVertex} (R : A.ASResolution Q w)
  {p : ℤ} (E : A.PeriodIso p)

noncomputable def transportedGeneratorBasis (n i : ℤ) (hi : i<Q.height w)
    (i' j' : ℤ) (h₁ : i+n*p=i') (h₂ : Q.height w+n*p=j') :
    Module.Basis (GeneratorIndex (Q:=Q) (w:=w) i) k
      (A.Hom i' j' ⧸ Submodule.span k (A.products i' j')) :=
  (R.indecomposableGeneratorBasis i hi).map
    (((E.powInt n).indecomposableEquiv i (Q.height w)).trans
      (A.homTransportIndecomposableEquiv _ _ _ _ h₁ h₂))

theorem transportedGeneratorBasis_apply (n i : ℤ) (hi : i<Q.height w)
    (i' j' : ℤ) (h₁ : i+n*p=i') (h₂ : Q.height w+n*p=j')
    (a : GeneratorIndex (Q:=Q) (w:=w) i) :
    R.transportedGeneratorBasis E n i hi i' j' h₁ h₂ a=
      Submodule.Quotient.mk (A.homTransport _ _ _ _ h₁ h₂
        ((E.powInt n).map i (Q.height w) (R.incomingGenerator i a))) := by
  rw [transportedGeneratorBasis,Module.Basis.map_apply,R.indecomposableGeneratorBasis_apply]
  change A.homTransportIndecomposableEquiv _ _ _ _ h₁ h₂
    ((E.powInt n).indecomposableEquiv i (Q.height w)
      (Submodule.Quotient.mk (R.incomingGenerator i a)))=_
  rw [PeriodIso.indecomposableEquiv_apply_mk,A.homTransportIndecomposableEquiv_apply_mk]

end ASResolution
end ASGinzburg.ZAlgebra
