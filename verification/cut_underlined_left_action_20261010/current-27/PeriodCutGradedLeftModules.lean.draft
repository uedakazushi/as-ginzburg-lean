import ASGinzburg.PeriodCutGradedRightModules

/-! A concrete model of integer-graded left modules over the native cut
ring, using actual algebra representations and internal decompositions. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped DirectSum
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

structure CutGradedLeftModule where
  space : ModuleCat.{w} k
  representation : E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) →ₐ[k] Module.End k space
  grade : ℤ → Submodule k space
  decomposition : DirectSum.Decomposition grade
  homogeneous : ∀ (m : ℕ) (r : E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) m)
    (q : ℤ) (x : space),x∈grade q →
      representation (E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val:ℤ)) m r) x∈
        grade (q+(m:ℤ))

namespace CutGradedLeftModule
variable {Q E}
noncomputable instance leftModule (M : E.CutGradedLeftModule Q) :
    Module (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) M.space :=
  Module.compHom _ M.representation.toRingHom

noncomputable instance scalarTower (M : E.CutGradedLeftModule Q) :
    IsScalarTower k (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) M.space where
  smul_assoc c r x := by
    change M.representation (c • r) x=c • M.representation r x
    rw [map_smul,LinearMap.smul_apply]

noncomputable def ringModule (M : E.CutGradedLeftModule Q) :
    ModuleCat (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) := ModuleCat.of _ M.space

end CutGradedLeftModule
end ASGinzburg.ZAlgebra.PeriodIso
