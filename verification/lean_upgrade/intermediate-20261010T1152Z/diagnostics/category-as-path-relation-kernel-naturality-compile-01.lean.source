import ASGinzburg.ASFirstKernelComponentComparison
import ASGinzburg.ASLastArrowCoverNaturality

/-! Prepending an actual path to a relation corresponds to the
existing right action on the genuine categorical AS kernel. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

noncomputable def prependPathRelation {u v w : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k u v)
    (g : LinearMap.ker (A.unrolledPathLinearEvaluation Q R v w)) :
    LinearMap.ker (A.unrolledPathLinearEvaluation Q R u w) :=
  ⟨Q.unrolledPathComp k g.val f,by
    change A.unrolledPathLinearEvaluation Q R u w (Q.unrolledPathComp k g.val f)=0
    rw [A.unrolledPathLinearEvaluation_comp,g.property]
    simp⟩

theorem pathRelationsToCategoricalASFirstKernel_action {u v w : Q.LiftVertex}
    (huw : u≠w) (hvw : v≠w) (f : Q.UnrolledPathComponent k u v)
    (g : LinearMap.ker (A.unrolledPathLinearEvaluation Q R v w)) :
    A.pathRelationsToCategoricalASFirstKernel Q R u w huw (A.prependPathRelation Q R f g)=
      (kernel (R w).d₁).obj.map
        (show (⟨Q.height u⟩ : A.Obj) ⟶ ⟨Q.height v⟩ from
          A.unrolledPathLinearEvaluation Q R u v f).op
        (A.pathRelationsToCategoricalASFirstKernel Q R v w hvw g) := by
  apply (ModuleCat.mono_iff_injective
    ((A.rightModuleEvaluation (Q.height u)).map (kernel.ι (R w).d₁))).mp inferInstance
  rw [A.pathRelationsToCategoricalASFirstKernel_ι]
  have hn := congrArg (fun t => t.hom (A.pathRelationsToCategoricalASFirstKernel Q R v w hvw g))
    ((kernel.ι (R w).d₁).naturality
      (show (⟨Q.height u⟩ : A.Obj) ⟶ ⟨Q.height v⟩ from
        A.unrolledPathLinearEvaluation Q R u v f).op)
  have hi := A.pathRelationsToCategoricalASFirstKernel_ι Q R v w hvw g
  have hc := A.lastArrowToASFirstTerm_action Q R huw hvw f g.val
  change A.lastArrowToASFirstTerm Q R u w huw (Q.unrolledPathComp k g.val f)=_
  rw [hc,←hi]
  exact hn.symm

end ASGinzburg.ZAlgebra
