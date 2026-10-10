import ASGinzburg.PeriodCutGradedLeftModules
import ASGinzburg.PeriodCutVertexLeftModule
import ASGinzburg.SingleDegreeGrading

/-! The actual vertex simple left module has degree-zero grading.
Its positive homogeneous action is zero by the genuine augmentation. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutVertexGradedLeftModule (i : Q.Vertex) : CutGradedLeftModule.{u,v,u} Q E where
  space := ModuleCat.of k k
  representation := (Algebra.lsmul k k k).comp (E.cutVertexCharacter Q i)
  grade := singleDegreeSpace (k:=k) k 0
  decomposition := singleDegreeGradeDecomposition (k:=k) k 0
  homogeneous m a q x hx := by
    change E.cutVertexCharacter Q i
      (E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m a) • x∈
        singleDegreeSpace (k:=k) k 0 (q+(m:ℤ))
    cases m with
    | zero =>
      simpa only [Nat.cast_zero,add_zero] using
        Submodule.smul_mem (singleDegreeSpace (k:=k) k 0 q)
          (E.cutVertexCharacter Q i (E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) 0 a)) hx
    | succ m =>
      rw [E.cutVertexCharacter_apply,E.cutAugmentation_positive_component]
      change (0:k) • x∈singleDegreeSpace (k:=k) k 0 (q+((m+1:ℕ):ℤ))
      rw [zero_smul]
      exact Submodule.zero_mem _

theorem cutVertexGradedLeftModule_isSimple (i : Q.Vertex) :
    IsSimpleModule (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))
      (E.cutVertexGradedLeftModule Q i).space :=
  E.cutVertexLeft_isSimple Q i

end ASGinzburg.ZAlgebra.PeriodIso
