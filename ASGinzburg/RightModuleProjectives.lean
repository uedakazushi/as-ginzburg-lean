import ASGinzburg.RightModuleHomology
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Representable right modules are projective

Linear Yoneda identifies maps `P_i → M` with the actual vertex component `M_i`.
Epimorphisms are componentwise surjective, so the generator at `i` can be lifted.
This proves projectivity in the existing linear-presheaf category, without
assuming an AS resolution or altering the paper's conditions.
-/

namespace ASGinzburg.ZAlgebra

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- An element of `M_i` induces the right-module map `P_i → M`. -/
def representableToElement (i : ℤ) (M : A.RightModule)
    (x : (A.rightModuleEvaluation i).obj M) : A.representable i ⟶ M := by
  letI := M.property.1
  letI := M.property.2
  exact
    { app := fun Y => ModuleCat.ofHom
        { toFun := fun f => M.obj.map f.op x
          map_add' := by
            intro f g
            change M.obj.map (f.op + g.op) x = M.obj.map f.op x + M.obj.map g.op x
            rw [Functor.map_add]
            rfl
          map_smul' := by
            intro r f
            change M.obj.map (r • f.op) x = r • M.obj.map f.op x
            rw [Functor.map_smul]
            rfl }
      naturality := by
        intro Y Z f
        ext g
        change M.obj.map (f.unop ≫ g).op x = M.obj.map f (M.obj.map g.op x)
        rw [op_comp, Functor.map_comp]
        rfl }

/-- Linear Yoneda for every right module, with no additional representability assumption. -/
def representableYonedaEquiv (i : ℤ) (M : A.RightModule) :
    (A.representable i ⟶ M) ≃ₗ[k] (A.rightModuleEvaluation i).obj M where
  toFun f := f.app (op ⟨i⟩) (A.id i)
  invFun x := A.representableToElement i M x
  left_inv f := by
    apply NatTrans.ext
    funext Y
    apply ModuleCat.hom_ext
    ext g
    change M.obj.map g.op (f.app (op ⟨i⟩) (A.id i)) = f.app Y g
    have h := congrArg (fun h => h (A.id i)) (f.naturality g.op)
    change f.app Y (A.comp (A.id i) g) =
      M.obj.map g.op (f.app (op ⟨i⟩) (A.id i)) at h
    rw [A.comp_id] at h
    exact h.symm
  right_inv x := by
    change M.obj.map (𝟙 (op (⟨i⟩ : A.Obj))) x = x
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_add' f g := rfl
  map_smul' r f := rfl

@[simp]
theorem representableYonedaEquiv_apply (i : ℤ) (M : A.RightModule)
    (f : A.representable i ⟶ M) :
    A.representableYonedaEquiv i M f = f.app (op ⟨i⟩) (A.id i) := rfl

@[simp]
theorem representableYonedaEquiv_comp (i : ℤ) {M N : A.RightModule}
    (f : A.representable i ⟶ M) (g : M ⟶ N) :
    A.representableYonedaEquiv i N (f ≫ g) =
      (A.rightModuleEvaluation i).map g (A.representableYonedaEquiv i M f) := rfl

/-- The inverse Yoneda map is right multiplication of an element by a component of `A`. -/
@[simp]
theorem representableYonedaEquiv_symm_app (i : ℤ) (M : A.RightModule)
    (x : (A.rightModuleEvaluation i).obj M) (Y : A.Objᵒᵖ) (f : Y.unop ⟶ (⟨i⟩ : A.Obj)) :
    ((A.representableYonedaEquiv i M).symm x).app Y f = M.obj.map f.op x := rfl

/-- Lift the distinguished generator through the epi, then extend by the right action. -/
instance representableProjective (i : ℤ) : Projective (A.representable i) where
  factors := by
    intro M N f e he
    have hs := (A.rightModule_epi_iff_surjective e).mp he i
    obtain ⟨x, hx⟩ := hs (A.representableYonedaEquiv i N f)
    refine ⟨(A.representableYonedaEquiv i M).symm x, ?_⟩
    apply (A.representableYonedaEquiv i N).injective
    rw [A.representableYonedaEquiv_comp, LinearEquiv.apply_symm_apply]
    exact hx

end ASGinzburg.ZAlgebra
