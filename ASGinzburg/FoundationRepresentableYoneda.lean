import ASGinzburg.FoundationResolutionTerms

/-! Actual linear Yoneda for the sheet-zero restricted representables,
with elements extended by the original contravariant component action. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

def foundationActionArrow (i j : Q.Vertex) (f : A.Hom (i.val : ℤ) (j.val : ℤ)) :
    (op (⟨(j.val : ℤ)⟩ : A.Obj)) ⟶ op (⟨(i.val : ℤ)⟩ : A.Obj) :=
  (show (⟨(i.val : ℤ)⟩ : A.Obj) ⟶ ⟨(j.val : ℤ)⟩ from f).op

def foundationRepresentableToElement (i : Q.Vertex) (M : A.FoundationRightModule Q)
    (x : (A.foundationRightEvaluation Q i).obj M) :
    A.foundationRepresentable Q i ⟶ M := by
  letI := M.property.1
  letI := M.property.2
  exact {
    app := fun Y => ModuleCat.ofHom {
      toFun f := M.obj.map (A.foundationActionArrow Q Y i f) x
      map_add' := by
        intro f g
        change M.obj.map (A.foundationActionArrow Q Y i f+
          A.foundationActionArrow Q Y i g) x=_
        rw [Functor.map_add]
        rfl
      map_smul' := by
        intro r f
        change M.obj.map (r • A.foundationActionArrow Q Y i f) x=_
        rw [Functor.map_smul]
        rfl }
    naturality := by
      intro Y Z f
      ext g
      change M.obj.map (A.foundationActionArrow Q Z i (A.comp g f.unop)) x=
        M.obj.map f (M.obj.map (A.foundationActionArrow Q Y i g) x)
      have h : A.foundationActionArrow Q Z i (A.comp g f.unop)=
          A.foundationActionArrow Q Y i g ≫ f := rfl
      rw [h]
      exact congrArg (fun t => t.hom x)
        (M.obj.map_comp (A.foundationActionArrow Q Y i g) f) }

def foundationRepresentableYonedaEquiv (i : Q.Vertex) (M : A.FoundationRightModule Q) :
    (A.foundationRepresentable Q i ⟶ M) ≃ₗ[k] (A.foundationRightEvaluation Q i).obj M where
  toFun f := f.app i (A.id (i.val : ℤ))
  invFun x := A.foundationRepresentableToElement Q i M x
  left_inv f := by
    apply NatTrans.ext
    funext Y
    apply ModuleCat.hom_ext
    ext g
    change M.obj.map (A.foundationActionArrow Q Y i g)
      (f.app i (A.id (i.val : ℤ)))=f.app Y g
    have h := congrArg (fun h => h (A.id (i.val : ℤ)))
      (f.naturality (A.foundationActionArrow Q Y i g))
    change f.app Y (A.comp (A.id (i.val : ℤ)) g)=
      M.obj.map (A.foundationActionArrow Q Y i g) (f.app i (A.id (i.val : ℤ))) at h
    rw [A.comp_id] at h
    exact h.symm
  right_inv x := by
    change M.obj.map (A.foundationActionArrow Q i i (A.id (i.val : ℤ))) x=x
    exact congrArg (fun t => t.hom x) (M.obj.map_id (i : A.FoundationRightObj Q))
  map_add' f g := rfl
  map_smul' r f := rfl

theorem foundationRepresentableYonedaEquiv_comp (i : Q.Vertex)
    {M N : A.FoundationRightModule Q} (f : A.foundationRepresentable Q i ⟶ M) (g : M ⟶ N) :
    A.foundationRepresentableYonedaEquiv Q i N (f ≫ g)=
      (A.foundationRightEvaluation Q i).map g (A.foundationRepresentableYonedaEquiv Q i M f) := rfl

end ASGinzburg.ZAlgebra
