import ASGinzburg.QuotientZAlgebra

/-! Vertex-fixing isomorphisms and the actual first isomorphism theorem
for the concrete locally finite directed Z-algebras. -/
namespace ASGinzburg.ZAlgebra
universe u v w x
variable {k : Type u} [Field k]

structure Isomorphism (B : ZAlgebra.{u,v} k) (A : ZAlgebra.{u,w} k) where
  map : ∀ i j, B.Hom i j ≃ₗ[k] A.Hom i j
  map_id : ∀ i, map i i (B.id i)=A.id i
  map_comp : ∀ {i j l} (f : B.Hom i j) (g : B.Hom j l),
    map i l (B.comp g f)=A.comp (map j l g) (map i j f)

namespace Isomorphism
variable {B : ZAlgebra.{u,v} k} {A : ZAlgebra.{u,w} k} {C : ZAlgebra.{u,x} k}

noncomputable def homomorphism (F : Isomorphism B A) : Homomorphism B A where
  map i j := (F.map i j).toLinearMap
  map_id := F.map_id
  map_comp := F.map_comp

noncomputable def refl (B : ZAlgebra.{u,v} k) : Isomorphism B B where
  map i j := LinearEquiv.refl k (B.Hom i j)
  map_id := by intro i; rfl
  map_comp := by intro i j l f g; rfl

noncomputable def symm (F : Isomorphism B A) : Isomorphism A B where
  map i j := (F.map i j).symm
  map_id := by
    intro i
    apply (F.map i i).injective
    simp [F.map_id]
  map_comp := by
    intro i j l f g
    apply (F.map i l).injective
    simp [F.map_comp]

noncomputable def trans (F : Isomorphism B A) (G : Isomorphism A C) :
    Isomorphism B C where
  map i j := (F.map i j).trans (G.map i j)
  map_id := by intro i; simp [F.map_id,G.map_id]
  map_comp := by intro i j l f g; simp [F.map_comp,G.map_comp]

end Isomorphism

namespace Homomorphism
variable {B : ZAlgebra.{u,v} k} {A : ZAlgebra.{u,w} k}
variable (F : Homomorphism B A) (hF : ∀ i j, Function.Surjective (F.map i j))

noncomputable def quotientKernelIso :
    Isomorphism (F.kernel.quotient F.kernel_diagonal_eq_bot) A where
  map := F.componentQuotientEquiv hF
  map_id := by intro i; exact F.map_id i
  map_comp := by
    intro i j l x y
    obtain ⟨f,rfl⟩ := (F.kernel.hom i j).mkQ_surjective x
    obtain ⟨g,rfl⟩ := (F.kernel.hom j l).mkQ_surjective y
    change F.componentQuotientEquiv hF i l
      (F.kernel.quotientComp (Submodule.Quotient.mk g) (Submodule.Quotient.mk f)) = _
    rw [LinearIdeal.quotientComp_mk]
    exact F.map_comp f g

theorem quotientKernelIso_apply_mk {i j : ℤ} (f : B.Hom i j) :
    (F.quotientKernelIso hF).map i j (Submodule.Quotient.mk f)=F.map i j f := rfl

end Homomorphism
end ASGinzburg.ZAlgebra
