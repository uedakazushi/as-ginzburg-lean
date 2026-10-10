import work.ASGinzburgDraft.PeriodCutEnvelopingAugmentationKernelSpan
import work.ASGinzburgDraft.PeriodCutEnvelopingVertexIdempotents
import Mathlib.Algebra.Algebra.Tower

/-! Positive operators on every actual enveloping module are genuine
positive-degree homogeneous elements acting by the original left action. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))
attribute [local instance 2000] cutEnvelopingOppositeFactorScalarTower
  cutEnvelopingOppositeFactorScalarComm cutGradedRingSelfScalarTower cutGradedRingSelfScalarComm

abbrev CutEnvelopingPositiveOperator :=
  Σ n : {n : ℕ // 0 < n},
    E.cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) n.val

def cutEnvelopingPositiveOperatorDegree (t : E.CutEnvelopingPositiveOperator Q) : ℕ := t.1.val

theorem cutEnvelopingPositiveOperatorDegree_pos (t : E.CutEnvelopingPositiveOperator Q) :
    0 < E.cutEnvelopingPositiveOperatorDegree Q t := t.1.property

def cutEnvelopingPositiveOperatorValue (t : E.CutEnvelopingPositiveOperator Q) :
    AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))) := t.2.val

theorem cutEnvelopingPositiveOperatorValue_mem (t : E.CutEnvelopingPositiveOperator Q) :
    E.cutEnvelopingPositiveOperatorValue Q t ∈
      E.cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ))
        (E.cutEnvelopingPositiveOperatorDegree Q t) := t.2.property

theorem mem_cutEnvelopingPositiveHomogeneousOperators_iff
    (a : AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :
    a ∈ E.cutEnvelopingPositiveHomogeneousOperators Q ↔
      ∃ t : E.CutEnvelopingPositiveOperator Q, E.cutEnvelopingPositiveOperatorValue Q t = a := by
  constructor
  · intro ha
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ha
    exact ⟨⟨n,⟨a,hn⟩⟩,rfl⟩
  · rintro ⟨t,rfl⟩
    exact Set.mem_iUnion.mpr ⟨t.1,t.2.property⟩

variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (AlgebraEnvelopingRing k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M]
  [IsScalarTower k (AlgebraEnvelopingRing k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M]

noncomputable def cutEnvelopingPositiveModuleOperator (t : E.CutEnvelopingPositiveOperator Q) :
    M →ₗ[k] M := by
  letI : SMulCommClass (AlgebraEnvelopingRing k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) k M :=
    IsScalarTower.to_smulCommClass'
  exact DistribMulAction.toLinearMap k M (E.cutEnvelopingPositiveOperatorValue Q t)

theorem cutEnvelopingPositiveModuleOperator_apply (t : E.CutEnvelopingPositiveOperator Q)
    (x : M) :
    E.cutEnvelopingPositiveModuleOperator Q M t x =
      E.cutEnvelopingPositiveOperatorValue Q t • x := rfl

end ASGinzburg.ZAlgebra.PeriodIso
