import ASGinzburg.LeftModules

/-! Actual directed-algebra objects can be isomorphic only at equal
integer indices; positivity and the nonzero identity prove this. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem objIndex_eq_of_iso {X Y : A.Obj} (e : X ≅ Y) : X.index = Y.index := by
  rcases lt_trichotomy X.index Y.index with h | h | h
  · have hz : e.inv = 0 := A.positive h e.inv
    have hh := e.hom_inv_id
    rw [hz, comp_zero] at hh
    exact False.elim (A.id_nonzero X.index hh.symm)
  · exact h
  · have hz : e.hom = 0 := A.positive h e.hom
    have hh := e.hom_inv_id
    rw [hz, zero_comp] at hh
    exact False.elim (A.id_nonzero X.index hh.symm)

theorem obj_eq_of_iso {X Y : A.Obj} (e : X ≅ Y) : X = Y := by
  have h := A.objIndex_eq_of_iso e
  cases X
  cases Y
  congr 1

end ASGinzburg.ZAlgebra
