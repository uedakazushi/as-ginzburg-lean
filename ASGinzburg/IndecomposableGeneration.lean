import ASGinzburg.ZAlgebraIsomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Actual indecomposable quotient generation implies generation of
the whole directed algebra. A component endomorphism with this property
is an automorphism, using the existing local finite dimensionality. -/
namespace ASGinzburg.ZAlgebra.Homomorphism
universe u v w
variable {k : Type u} [Field k] {B : ZAlgebra.{u,v} k} {A : ZAlgebra.{u,w} k}
  (F : Homomorphism B A)

theorem products_span_le_comap (i j : ℤ) :
    Submodule.span k (B.products i j)≤
      Submodule.comap (F.map i j) (Submodule.span k (A.products i j)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hil,hlj,a,b,rfl⟩
  change F.map i j (B.comp b a)∈Submodule.span k (A.products i j)
  rw [F.map_comp]
  exact Submodule.subset_span ⟨l,hil,hlj,F.map i l a,F.map l j b,rfl⟩

noncomputable def indecomposableMap (i j : ℤ) :
    (B.Hom i j ⧸ Submodule.span k (B.products i j)) →ₗ[k]
      (A.Hom i j ⧸ Submodule.span k (A.products i j)) :=
  (Submodule.span k (B.products i j)).mapQ
    (Submodule.span k (A.products i j)) (F.map i j) (F.products_span_le_comap i j)

theorem indecomposableMap_apply_mk (i j : ℤ) (f : B.Hom i j) :
    F.indecomposableMap i j (Submodule.Quotient.mk f)=
      Submodule.Quotient.mk (F.map i j f) := rfl

noncomputable def rangeSubcategory : A.LinearSubcategory where
  hom i j := LinearMap.range (F.map i j)
  id_mem i := ⟨B.id i,F.map_id i⟩
  comp_mem := by
    rintro i j l _ _ ⟨f,rfl⟩ ⟨g,rfl⟩
    exact ⟨B.comp g f,F.map_comp f g⟩

theorem surjective_of_indecomposable_surjective
    (hq : ∀ i j, i<j → Function.Surjective (F.indecomposableMap i j)) :
    ∀ i j, Function.Surjective (F.map i j) := by
  have hd : ∀ i j, i<j → LinearMap.range (F.map i j) ⊔
      Submodule.span k (A.products i j)=⊤ := by
    intro i j hij
    let p := Submodule.span k (A.products i j)
    have hm : Submodule.map p.mkQ (LinearMap.range (F.map i j))=⊤ := by
      apply eq_top_iff.mpr
      intro y _
      obtain ⟨x,rfl⟩ := hq i j hij y
      obtain ⟨f,rfl⟩ := (Submodule.span k (B.products i j)).mkQ_surjective x
      exact ⟨F.map i j f,⟨f,rfl⟩,rfl⟩
    have hs := (p.map_mkQ_eq_top _).mp hm
    simpa only [sup_comm] using hs
  have ht := A.generated_of_decomposition (fun i j => LinearMap.range (F.map i j))
    hd F.rangeSubcategory (fun _ _ => le_rfl)
  intro i j
  exact LinearMap.range_eq_top.mp (ht i j)

end ASGinzburg.ZAlgebra.Homomorphism

namespace ASGinzburg.ZAlgebra.Homomorphism
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}

noncomputable def isomorphismOfIndecomposableSurjective (F : Homomorphism A A)
    (hq : ∀ i j, i<j → Function.Surjective (F.indecomposableMap i j)) : Isomorphism A A where
  map i j := LinearEquiv.ofBijective (F.map i j)
    ⟨LinearMap.injective_iff_surjective.mpr (F.surjective_of_indecomposable_surjective hq i j),
      F.surjective_of_indecomposable_surjective hq i j⟩
  map_id := F.map_id
  map_comp := F.map_comp

end ASGinzburg.ZAlgebra.Homomorphism
