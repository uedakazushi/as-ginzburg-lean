import ASGinzburg.CoproductRadicals

/-! The existing finite-coproduct component isomorphism preserves the
actual right action, by naturality of each actual coproduct projection. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
variable {I : Type} [Fintype I] [DecidableEq I] (g : I → A.RightModule)

theorem rightFiniteCoproductPiEquiv_action (i j : ℤ) (f : A.Hom i j)
    (x : (A.rightModuleEvaluation j).obj (∐ g)) (a : I) :
    A.rightFiniteCoproductPiEquiv g i
        ((∐ g).obj.map (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from f).op x) a=
      (g a).obj.map (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from f).op
        (A.rightFiniteCoproductPiEquiv g j x a) := by
  rw [A.rightFiniteCoproductPiEquiv_projection,A.rightFiniteCoproductPiEquiv_projection]
  exact congrArg (fun h => h x)
    ((A.rightFiniteCoproductProjection g a).naturality
      (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from f).op)

end ASGinzburg.ZAlgebra
