import ASGinzburg.PeriodCutGradedModuleComponents
import ASGinzburg.PeriodCutGradedModuleCategory

/-! Genuine graded R-module morphisms restrict to the recovered components. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

theorem map_mem_componentSubmodule {M N : E.CutGradedRightModule Q} (f : M⟶N)
    (x : Q.LiftVertex) (v : M.space) (hv : v∈M.componentSubmodule x) :
    f.val v∈N.componentSubmodule x := by
  rw [M.mem_componentSubmodule_iff] at hv
  rw [N.mem_componentSubmodule_iff]
  constructor
  · exact f.property.2 (-x.2) v hv.1
  · change (N.representation
      (E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) x.1)).unop (f.val v)=f.val v
    rw [← f.property.1]
    exact congrArg f.val hv.2

noncomputable def recoveredComponentLinearMap {M N : E.CutGradedRightModule Q}
    (f : M⟶N) (x : Q.LiftVertex) : M.componentSubmodule x →ₗ[k] N.componentSubmodule x where
  toFun v := ⟨f.val v.val,map_mem_componentSubmodule f x v.val v.property⟩
  map_add' := by intro v w;apply Subtype.ext;exact f.val.map_add v.val w.val
  map_smul' := by intro c v;apply Subtype.ext;exact f.val.map_smul c v.val

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
