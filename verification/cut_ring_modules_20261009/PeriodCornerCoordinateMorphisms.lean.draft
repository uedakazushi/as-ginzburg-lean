import ASGinzburg.PeriodCornerCoverRecovery
import ASGinzburg.Representables

/-! Reindexing the native corner category by vertex and sheet coordinates.
The coordinate morphisms preserve the ring multiplication and idempotent units. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

def cornerCoordinateObject (x : Q.LiftVertex) : (E.cornerCoverZAlgebra Q).Obj :=
  ⟨Q.heightEquiv x⟩

noncomputable def cornerCoordinateHomEquiv (x y : Q.LiftVertex) :
    E.CornerCoverHom Q x y ≃ₗ[k]
      (E.cornerCoordinateObject Q x ⟶ E.cornerCoordinateObject Q y) := by
  change E.CornerCoverHom Q x y ≃ₗ[k]
    E.CornerCoverHom Q (Q.heightEquiv.symm (Q.heightEquiv x))
      (Q.heightEquiv.symm (Q.heightEquiv y))
  exact submoduleEqualityEquiv _ _ (by simp only [Equiv.symm_apply_apply])

theorem cornerCoordinateHomEquiv_val {x y : Q.LiftVertex} (f : E.CornerCoverHom Q x y) :
    (E.cornerCoordinateHomEquiv Q x y f).val=f.val :=
  submoduleEqualityEquiv_val _ _ _ f

theorem cornerCoordinateHomEquiv_comp {x y z : Q.LiftVertex}
    (f : E.CornerCoverHom Q x y) (g : E.CornerCoverHom Q y z) :
    E.cornerCoordinateHomEquiv Q x z (E.cornerCoverComp Q g f)=
      E.cornerCoordinateHomEquiv Q x y f ≫ E.cornerCoordinateHomEquiv Q y z g := by
  apply Subtype.ext
  rw [E.cornerCoordinateHomEquiv_val,cornerCoverComp_val]
  change g.val*f.val=
    (E.cornerCoordinateHomEquiv Q y z g).val*(E.cornerCoordinateHomEquiv Q x y f).val
  rw [E.cornerCoordinateHomEquiv_val,E.cornerCoordinateHomEquiv_val]

theorem cornerCoordinateHomEquiv_id (x : Q.LiftVertex) :
    E.cornerCoordinateHomEquiv Q x x (E.cornerCoverId Q x)=𝟙 (E.cornerCoordinateObject Q x) := by
  apply Subtype.ext
  rw [E.cornerCoordinateHomEquiv_val]
  change E.cutVertexIdempotent (fun i : Q.Vertex => (i.val:ℤ)) x.1=
    E.cutVertexIdempotent (fun i : Q.Vertex => (i.val:ℤ))
      (Q.heightEquiv.symm (Q.heightEquiv x)).1
  rw [Equiv.symm_apply_apply]

end ASGinzburg.ZAlgebra.PeriodIso
