import ASGinzburg.LeftModuleHomology
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Left submodules and actual cokernel quotients

A submodule is a family of vector subspaces closed under the existing left
action. Its inclusion is monic and its categorical quotient forms a short
exact sequence. No abstract replacement for the underlying module is used.
-/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}

/-- Component subspaces closed under the existing covariant left action. -/
structure LeftSubmodule (M : A.LeftModule) where
  component : ∀ X : A.Obj, Submodule k (M.obj.obj X)
  map_mem : ∀ {X Y : A.Obj} (f : X ⟶ Y) {x : M.obj.obj X},
    x ∈ component X → M.obj.map f x ∈ component Y

namespace LeftSubmodule
variable {M : A.LeftModule} (S : LeftSubmodule M)

def presheaf : A.Obj ⥤ ModuleCat.{v} k where
  obj X := ModuleCat.of k (S.component X)
  map f := ModuleCat.ofHom {
    toFun x := ⟨M.obj.map f x, S.map_mem f x.property⟩
    map_add' x y := Subtype.ext (map_add (M.obj.map f).hom x.val y.val)
    map_smul' r x := Subtype.ext (map_smul (M.obj.map f).hom r x.val) }
  map_id X := by
    ext x
    change M.obj.map (𝟙 X) x.val = x.val
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    ext x
    change M.obj.map (f ≫ g) x.val = M.obj.map g (M.obj.map f x.val)
    rw [CategoryTheory.Functor.map_comp]
    rfl

instance presheafAdditive : S.presheaf.Additive where
  map_add := by
    letI := M.property.1
    intro X Y f g
    ext x
    apply Subtype.ext
    change M.obj.map (f + g) x.val = M.obj.map f x.val + M.obj.map g x.val
    rw [Functor.map_add]
    rfl

instance presheafLinear : S.presheaf.Linear k where
  map_smul := by
    letI := M.property.2
    intro X Y f r
    ext x
    apply Subtype.ext
    change M.obj.map (r • f) x.val = r • M.obj.map f x.val
    rw [Functor.map_smul]
    rfl

def object : A.LeftModule := ⟨S.presheaf, ⟨inferInstance, inferInstance⟩⟩

def inclusion : S.object ⟶ M where
  app X := ModuleCat.ofHom (S.component X).subtype
  naturality := by
    intro X Y f
    rfl

instance inclusionMono : Mono S.inclusion := by
  apply (A.leftModule_mono_iff_injective _).mpr
  intro i
  exact Subtype.val_injective

noncomputable def quotient : A.LeftModule := cokernel S.inclusion
noncomputable def quotientπ : M ⟶ S.quotient := cokernel.π S.inclusion

noncomputable instance quotientπEpi : Epi S.quotientπ := by
  dsimp [quotientπ]
  infer_instance

noncomputable def quotientShortComplex : ShortComplex A.LeftModule :=
  ShortComplex.mk S.inclusion S.quotientπ (cokernel.condition _)

theorem quotientShortExact : S.quotientShortComplex.ShortExact where
  exact := ShortComplex.exact_cokernel S.inclusion
  mono_f := S.inclusionMono
  epi_g := S.quotientπEpi

end LeftSubmodule
end ASGinzburg.ZAlgebra
