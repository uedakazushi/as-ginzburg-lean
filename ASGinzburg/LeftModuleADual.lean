import ASGinzburg.LeftModuleProjectives
import ASGinzburg.RightModuleExtLeftAction

/-!
# The left A-dual and biduality of representables

Both duals use actual Hom spaces and actions. Representables return to
themselves under the two duals. Biduality for general finite projectives
and perfect complexes still requires further proofs.
-/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- The contravariant family of concrete left representables. -/
def leftRepresentableFunctor : A.Objᵒᵖ ⥤ A.LeftModule where
  obj X := A.leftRepresentable X.unop.index
  map f := (linearCoyoneda k A.Obj).map f
  map_id X := (linearCoyoneda k A.Obj).map_id X
  map_comp f g := (linearCoyoneda k A.Obj).map_comp f g

instance leftRepresentableFunctorAdditive : A.leftRepresentableFunctor.Additive where
  map_add := by
    intro X Y f g
    apply NatTrans.ext
    funext Z
    apply ModuleCat.hom_ext
    ext h
    change (f + g).unop ≫ h = f.unop ≫ h + g.unop ≫ h
    simp

instance leftRepresentableFunctorLinear : A.leftRepresentableFunctor.Linear k where
  map_smul := by
    intro X Y f r
    apply NatTrans.ext
    funext Z
    apply ModuleCat.hom_ext
    ext h
    change (r • f.unop) ≫ h = r • (f.unop ≫ h)
    exact Linear.smul_comp _ _ _ r f.unop h

instance leftModuleCoyonedaLinear (M : A.LeftModule) :
    ((linearCoyoneda k A.LeftModule).obj (op M)).Linear k where
  map_smul := by
    intro X Y f r
    ext h
    change h ≫ (r • f) = r • (h ≫ f)
    simp

/-- The left A-dual, as a concrete right module with component Hom(N,A e_i). -/
def leftModuleADual (N : A.LeftModule) : A.RightModule :=
  ⟨A.leftRepresentableFunctor ⋙ (linearCoyoneda k A.LeftModule).obj (op N),
    ⟨inferInstance, inferInstance⟩⟩

@[simp] theorem leftModuleADual_obj (N : A.LeftModule) (i : ℤ) :
    (A.leftModuleADual N).obj.obj (op ⟨i⟩) =
      ModuleCat.of k (N ⟶ A.leftRepresentable i) := rfl

def leftModuleADualMap {M N : A.LeftModule} (f : M ⟶ N) :
    A.leftModuleADual N ⟶ A.leftModuleADual M where
  app X := ModuleCat.ofHom
    { toFun := fun g => f ≫ g
      map_add' := fun g h => Preadditive.comp_add _ _ _ f g h
      map_smul' := fun r g => Linear.comp_smul _ _ _ f r g }
  naturality := by intro X Y g; ext h; exact (Category.assoc f h _).symm

def leftModuleADualFunctor : A.LeftModuleᵒᵖ ⥤ A.RightModule where
  obj M := A.leftModuleADual M.unop
  map f := A.leftModuleADualMap f.unop
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

/-- Covariant Yoneda identifies the A-dual of A e_i with P_i, respecting
all of the actual right action. -/
noncomputable def leftRepresentableADualIso (i : ℤ) :
    A.leftModuleADual (A.leftRepresentable i) ≅ A.representable i := by
  let e : (A.leftModuleADual (A.leftRepresentable i)).obj ≅ (A.representable i).obj :=
    NatIso.ofComponents (fun X =>
      (A.leftRepresentableYonedaEquiv i (A.leftRepresentable X.unop.index)).toModuleIso) (by
        intro X Y f
        apply ModuleCat.hom_ext
        ext g
        exact A.leftRepresentableYonedaEquiv_comp i g (A.leftRepresentableFunctor.map f))
  exact ⟨e.hom,e.inv,e.hom_inv_id,e.inv_hom_id⟩

/-- A checked representable returns to itself under the actual two A-duals.
Naturality of the bidual evaluation on arbitrary modules is not asserted here. -/
noncomputable def representableBidualIso (i : ℤ) :
    A.leftModuleADual (A.rightModuleADual (A.representable i)) ≅ A.representable i :=
  (A.leftModuleADualFunctor.mapIso (A.representableADualIso i).op).symm ≪≫
    A.leftRepresentableADualIso i

/-- The same concrete biduality on a left representable. -/
noncomputable def leftRepresentableBidualIso (i : ℤ) :
    A.rightModuleADual (A.leftModuleADual (A.leftRepresentable i)) ≅ A.leftRepresentable i :=
  (A.rightModuleADualFunctor.mapIso (A.leftRepresentableADualIso i).op).symm ≪≫
    A.representableADualIso i

end ASGinzburg.ZAlgebra
