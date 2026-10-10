import ASGinzburg.ASIndecomposables
import ASGinzburg.ZAlgebraHomomorphisms

/-! Surjective actual component-algebra maps preserve the span of all
positive products and induce the genuine indecomposable quotient isomorphism
when their kernel is decomposable. The kernel condition is proved separately. -/
namespace ASGinzburg.ZAlgebra.Homomorphism
universe u v w
variable {k : Type u} [Field k] {B : ZAlgebra.{u,v} k} {A : ZAlgebra.{u,w} k}
  (F : Homomorphism B A) (hF : ∀ i j, Function.Surjective (F.map i j))

include hF in
theorem map_products_span (i j : ℤ) :
    Submodule.map (F.map i j) (Submodule.span k (B.products i j))=
      Submodule.span k (A.products i j) := by
  apply le_antisymm
  · rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨f,⟨l,hil,hlj,a,b,rfl⟩,rfl⟩
    rw [F.map_comp]
    exact Submodule.subset_span ⟨l,hil,hlj,F.map i l a,F.map l j b,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨l,hil,hlj,a,b,rfl⟩
    obtain ⟨a',rfl⟩ := hF i l a
    obtain ⟨b',rfl⟩ := hF l j b
    rw [←F.map_comp]
    exact Submodule.mem_map.mpr
      ⟨B.comp b' a',Submodule.subset_span ⟨l,hil,hlj,a',b',rfl⟩,rfl⟩

noncomputable def indecomposableEquiv (i j : ℤ)
    (hker : F.kernel.hom i j≤Submodule.span k (B.products i j)) :
    (B.Hom i j ⧸ Submodule.span k (B.products i j)) ≃ₗ[k]
      (A.Hom i j ⧸ Submodule.span k (A.products i j)) :=
  (ASGinzburg.surjectiveQuotientImageEquiv (F.map i j) (hF i j)
    (Submodule.span k (B.products i j)) hker).trans
    (Submodule.quotEquivOfEq _ _ (F.map_products_span hF i j))

end ASGinzburg.ZAlgebra.Homomorphism
