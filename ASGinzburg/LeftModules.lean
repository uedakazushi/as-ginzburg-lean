import ASGinzburg.RightModuleProjectives

/-!
# Concrete left modules and the A-dual of a right module

Left modules are covariant additive linear functors on the same algebra.
The A-dual has component Hom_A(M,P_i), with left action by postcomposition.
This does not yet prove the positive-degree AS duality or direct-sum exchange.
-/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

def leftModuleProperty : ObjectProperty (A.Obj ⥤ ModuleCat.{v} k) :=
  fun F => F.Additive ∧ F.Linear k

abbrev LeftModule := A.leftModuleProperty.FullSubcategory

instance leftRepresentableLinear (X : A.Objᵒᵖ) :
    ((linearCoyoneda k A.Obj).obj X).Linear k where
  map_smul := by
    intro Y Z f r
    ext h
    change h ≫ (r • f) = r • (h ≫ f)
    simp

/-- A e_i has component e_j A e_i at j. -/
def leftRepresentable (i : ℤ) : A.LeftModule :=
  ⟨(linearCoyoneda k A.Obj).obj (op ⟨i⟩), ⟨inferInstance, inferInstance⟩⟩

/-- The actual covariant family of right representables. -/
def representableFunctor : A.Obj ⥤ A.RightModule where
  obj X := A.representable X.index
  map f := (linearYoneda k A.Obj).map f
  map_id X := (linearYoneda k A.Obj).map_id X
  map_comp f g := (linearYoneda k A.Obj).map_comp f g

instance representableFunctorAdditive : A.representableFunctor.Additive where
  map_add := (linearYoneda k A.Obj).map_add

instance representableFunctorLinear : A.representableFunctor.Linear k where
  map_smul := by intro X Y f r; exact (linearYoneda k A.Obj).map_smul r f

instance rightModuleCoyonedaLinear (M : A.RightModule) :
    ((linearCoyoneda k A.RightModule).obj (op M)).Linear k where
  map_smul := by
    intro X Y f r
    ext h
    change h ≫ (r • f) = r • (h ≫ f)
    simp

/-- The A-dual, with a proved concrete left action, without replacing Hom by a Prop. -/
def rightModuleADual (M : A.RightModule) : A.LeftModule :=
  ⟨A.representableFunctor ⋙ (linearCoyoneda k A.RightModule).obj (op M),
    ⟨inferInstance, inferInstance⟩⟩

@[simp] theorem rightModuleADual_obj (M : A.RightModule) (i : ℤ) :
    (A.rightModuleADual M).obj.obj ⟨i⟩ = ModuleCat.of k (M ⟶ A.representable i) := rfl

/-- Contravariant action on right-module morphisms is actual precomposition. -/
def rightModuleADualMap {M N : A.RightModule} (f : M ⟶ N) :
    A.rightModuleADual N ⟶ A.rightModuleADual M where
  app X := ModuleCat.ofHom
    { toFun := fun g => f ≫ g
      map_add' := fun g h => Preadditive.comp_add _ _ _ f g h
      map_smul' := fun r g => Linear.comp_smul _ _ _ f r g }
  naturality := by intro X Y g; ext h; exact (Category.assoc f h _).symm

/-- The A-dual is a functor into the concrete left-module category. -/
def rightModuleADualFunctor : A.RightModuleᵒᵖ ⥤ A.LeftModule where
  obj M := A.rightModuleADual M.unop
  map f := A.rightModuleADualMap f.unop
  map_id M := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    ext h
    exact Category.id_comp h
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    ext h
    exact Category.assoc g.unop f.unop h

/-- Each component of the A-dual of P_i is the correct component of A e_i. -/
noncomputable def representableADualComponentEquiv (i j : ℤ) :
    ((A.rightModuleADual (A.representable i)).obj.obj ⟨j⟩) ≃ₗ[k] A.Hom i j :=
  (A.representableHomEquiv i j).symm

/-- The component identifications respect the left action, hence give an
actual left-module isomorphism Hom_A(P_i,A) = A e_i in the component model. -/
noncomputable def representableADualIso (i : ℤ) :
    A.rightModuleADual (A.representable i) ≅ A.leftRepresentable i := by
  let e : (A.rightModuleADual (A.representable i)).obj ≅ (A.leftRepresentable i).obj :=
    NatIso.ofComponents (fun X => (A.representableHomEquiv i X.index).symm.toModuleIso)
      (by
        intro X Y g
        rcases X with ⟨j⟩
        rcases Y with ⟨l⟩
        apply ModuleCat.hom_ext
        ext h
        apply (A.representableHomEquiv i l).injective
        change A.representableHomEquiv i l
            ((A.representableHomEquiv i l).symm
              (h ≫ (linearYoneda k A.Obj).map g)) =
          (linearYoneda k A.Obj).map ((A.representableHomEquiv i j).symm h ≫ g)
        rw [LinearEquiv.apply_symm_apply, Functor.map_comp]
        have hh : (linearYoneda k A.Obj).map
            ((A.representableHomEquiv i j).symm h) = h :=
          (A.representableHomEquiv i j).apply_symm_apply h
        rw [hh]
        rfl)
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

end ASGinzburg.ZAlgebra
