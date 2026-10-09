import ASGinzburg.LeftModules

/-! Opposite-category covariant representables are the existing right
representables, by the actual unop map on their hom spaces. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

def oppositeHomUnopEquiv (X Y : A.Objᵒᵖ) :
    (X ⟶ Y) ≃ₗ[k] (Y.unop ⟶ X.unop) where
  toFun := Quiver.Hom.unop
  invFun := Quiver.Hom.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def oppositeCoyonedaYonedaIso (i : ℤ) :
    (linearCoyoneda k A.Objᵒᵖ).obj (op (op (⟨i⟩ : A.Obj))) ≅
      (linearYoneda k A.Obj).obj ⟨i⟩ :=
  NatIso.ofComponents (fun Y => (A.oppositeHomUnopEquiv (op ⟨i⟩) Y).toModuleIso)
    (by intro X Y f; apply ModuleCat.hom_ext; ext g; rfl)

end ASGinzburg.ZAlgebra
