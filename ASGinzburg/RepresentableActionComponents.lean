import ASGinzburg.RightModuleHomology

/-! The actual representable action written with explicit A.Hom
component types, avoiding repeated expansion of the Yoneda construction. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

def representablePrecomposition (i j l : ℤ) (a : A.Hom i j) :
    ModuleCat.of k (A.Hom j l) ⟶ ModuleCat.of k (A.Hom i l) :=
  ModuleCat.ofHom ((A.comp (u:=i) (v:=j) (w:=l)).flip a)

theorem representable_map_eq_precomposition (i j l : ℤ) (a : A.Hom i j) :
    (A.representable l).obj.map
        (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op=
      A.representablePrecomposition i j l a := rfl

end ASGinzburg.ZAlgebra
