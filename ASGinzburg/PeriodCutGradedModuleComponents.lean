import ASGinzburg.PeriodCutGradedRightModules
import ASGinzburg.PeriodIntegerCornerAbsorption

/-! Recover genuine vertex/sheet component spaces from actual graded right R modules. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

noncomputable def vertexProjection (M : E.CutGradedRightModule Q) (i : Q.Vertex) :
    Module.End k M.space :=
  (M.representation (E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) i)).unop

theorem vertexProjection_idempotent (M : E.CutGradedRightModule Q) (i : Q.Vertex) :
    (M.vertexProjection i).comp (M.vertexProjection i)=M.vertexProjection i := by
  have h := congrArg (fun r => (M.representation r).unop)
    (E.cutVertexIdempotent_mul_self (fun t : Q.Vertex => (t.val:ℤ)) i)
  simpa only [map_mul,MulOpposite.unop_mul] using h

theorem vertexProjection_preserves_grade (M : E.CutGradedRightModule Q) (i : Q.Vertex)
    (q : ℤ) (x : M.space) (hx : x∈M.grade q) : M.vertexProjection i x∈M.grade q := by
  have h := M.homogeneous 0
    (E.cutMatrixComponent (fun t : Q.Vertex => (t.val:ℤ)) 0 i i
      (E.cutGradedId (i.val:ℤ))) q x hx
  simpa only [vertexProjection,cutVertexIdempotent,Nat.cast_zero,add_zero] using h

noncomputable def componentSubmodule (M : E.CutGradedRightModule Q) (x : Q.LiftVertex) :
    Submodule k M.space :=
  M.grade (-x.2) ⊓ LinearMap.ker (M.vertexProjection x.1-LinearMap.id)

theorem mem_componentSubmodule_iff (M : E.CutGradedRightModule Q) (x : Q.LiftVertex)
    (v : M.space) :
    v∈M.componentSubmodule x ↔ v∈M.grade (-x.2) ∧ M.vertexProjection x.1 v=v := by
  simp only [componentSubmodule,Submodule.mem_inf,LinearMap.mem_ker,
    LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero]

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
