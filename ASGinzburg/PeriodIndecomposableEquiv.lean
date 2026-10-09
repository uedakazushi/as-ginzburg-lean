import ASGinzburg.ASPeriodicity
import ASGinzburg.ASIncomingBasisSystems

/-! A genuine multiplicative period isomorphism preserves the actual
positive-product subspaces and hence the indecomposable quotients.
The AS application uses the period already derived from ASRegular. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}

namespace PeriodIso
variable (E : A.PeriodIso p)

theorem image_products (i j : ℤ) :
    E.map i j '' A.products i j=A.products (i+p) (j+p) := by
  ext x
  constructor
  · rintro ⟨f,⟨m,him,hmj,a,b,rfl⟩,rfl⟩
    exact ⟨m+p,by omega,by omega,E.map i m a,E.map m j b,(E.map_comp a b).symm⟩
  · rintro ⟨l,hil,hlj,a,b,rfl⟩
    obtain ⟨m,hm⟩ : ∃ m : ℤ,m+p=l := ⟨l-p,sub_add_cancel l p⟩
    subst l
    obtain ⟨a',rfl⟩ := (E.map i m).surjective a
    obtain ⟨b',rfl⟩ := (E.map m j).surjective b
    exact ⟨A.comp b' a',⟨m,by omega,by omega,a',b',rfl⟩,E.map_comp a' b'⟩

theorem map_products_span (i j : ℤ) :
    Submodule.map (E.map i j).toLinearMap (Submodule.span k (A.products i j))=
      Submodule.span k (A.products (i+p) (j+p)) := by
  rw [Submodule.map_span]
  change Submodule.span k (E.map i j '' A.products i j)=_
  rw [E.image_products i j]

noncomputable def indecomposableEquiv (i j : ℤ) :
    (A.Hom i j ⧸ Submodule.span k (A.products i j)) ≃ₗ[k]
      (A.Hom (i+p) (j+p) ⧸ Submodule.span k (A.products (i+p) (j+p))) :=
  Submodule.Quotient.equiv _ _ (E.map i j) (E.map_products_span i j)

theorem indecomposableEquiv_apply_mk (i j : ℤ) (f : A.Hom i j) :
    E.indecomposableEquiv i j (Submodule.Quotient.mk f)=
      Submodule.Quotient.mk (E.map i j f) := rfl

end PeriodIso

noncomputable def ASRegular.periodIndecomposableEquiv (A : ZAlgebra.{u,v} k)
    (Q : CutQuiver) (hAS : A.ASRegular Q) (i j : ℤ) :
    (A.Hom i j ⧸ Submodule.span k (A.products i j)) ≃ₗ[k]
      (A.Hom (i+Q.vertices) (j+Q.vertices) ⧸
        Submodule.span k (A.products (i+Q.vertices) (j+Q.vertices))) :=
  (hAS.periodIso A Q).indecomposableEquiv i j

end ASGinzburg.ZAlgebra
