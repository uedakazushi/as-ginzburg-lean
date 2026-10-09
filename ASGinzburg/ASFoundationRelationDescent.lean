import ASGinzburg.ASFoundationRelationNative
import ASGinzburg.UnrolledErasureLengthFiltration

/-! The original AS conditions produce genuine non-cut finite-quiver
relation representatives of length at least two. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

set_option synthInstance.maxHeartbeats 200000 in
noncomputable def ASRegular.foundationPathRelation (hAS : A.ASRegular Q)
    (i j : Q.Vertex) (a : Q.FoundationRelationArrow i j) : Q.PathComponent k i j :=
  Q.unrolledPathEraseLinearMap k (i,0) (j,0)
    (hAS.foundationRelationNative A Q i j a).val

set_option synthInstance.maxHeartbeats 200000 in
theorem ASRegular.foundationPathRelation_cut (hAS : A.ASRegular Q)
    (i j : Q.Vertex) (a : Q.FoundationRelationArrow i j) :
    hAS.foundationPathRelation A Q i j a ∈ Q.pathCutComponent k i j 0 := by
  exact Q.unrolledPathEraseLinearMap_cut k
    (hAS.foundationRelationNative A Q i j a).val

set_option synthInstance.maxHeartbeats 200000 in
theorem ASRegular.foundationPathRelation_mem_long (hAS : A.ASRegular Q)
    (i j : Q.Vertex) (a : Q.FoundationRelationArrow i j) :
    hAS.foundationPathRelation A Q i j a ∈ Q.pathLengthFiltration k 2 i j :=
  Q.unrolledPathEraseLinearMap_mem_lengthFiltration k 2
    (hAS.foundationRelationNative_mem_long A Q i j a)

set_option synthInstance.maxHeartbeats 200000 in
theorem ASRegular.foundationPathRelation_support (hAS : A.ASRegular Q)
    (i j : Q.Vertex) (a : Q.FoundationRelationArrow i j) :
    hAS.foundationPathRelation A Q i j a ∈ Finsupp.supported k k
      {p : Q.Path i j | 2 ≤ p.length ∧ p.cutDegree=0} := by
  apply (Finsupp.mem_supported k _).mpr
  intro p hp
  have hl := (Finsupp.mem_supported k _).mp
    (hAS.foundationPathRelation_mem_long A Q i j a) hp
  have hc := (Finsupp.mem_supported k _).mp
    (hAS.foundationPathRelation_cut A Q i j a) hp
  exact ⟨hl,by exact_mod_cast hc⟩

end ASGinzburg.ZAlgebra
