import ASGinzburg.ZAlgebraLinearEquivalence

/-! Directedness forces isomorphic vertex objects to have the same index.
Consequently the chosen inverse of a vertex-fixing equivalence also fixes
indices, even though its objects are selected through essential surjectivity. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A B : ZAlgebra.{u,v} k}

theorem objIso_index_eq {X Y : A.Obj} (e : X≅Y) : X.index=Y.index := by
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hz : e.inv=0 := A.positive hlt e.inv
    have hi : (𝟙 X : X⟶X)=0 := by
      rw [← e.hom_inv_id,hz]
      simp
    exact A.id_nonzero X.index hi
  · have hz : e.hom=0 := A.positive hgt e.hom
    have hi : (𝟙 X : X⟶X)=0 := by
      rw [← e.hom_inv_id,hz]
      simp
    exact A.id_nonzero X.index hi

theorem Isomorphism.linearEquivalence_inverse_index (E : Isomorphism A B) (X : B.Obj) :
    (E.linearEquivalence.inverse.obj X).index=X.index :=
  objIso_index_eq (E.linearEquivalence.counitIso.app X)

end ASGinzburg.ZAlgebra
