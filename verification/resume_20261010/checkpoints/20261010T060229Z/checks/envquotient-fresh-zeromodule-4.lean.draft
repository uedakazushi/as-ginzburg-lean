import work.ASGinzburgDraft.PeriodCutEnvelopingAugmentationComparison
import work.ASGinzburgDraft.PeriodCutEnvelopingVertexIdempotents
import Mathlib.Algebra.Algebra.Tower

/-! Every actual left enveloping module restricts along the genuine
degree-zero enveloping inclusion. Both scalar towers use those actual
restricted actions. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))
attribute [local instance 2000] cutEnvelopingOppositeFactorScalarTower
  cutEnvelopingOppositeFactorScalarComm cutGradedRingSelfScalarTower cutGradedRingSelfScalarComm

noncomputable def cutEnvelopingZeroRestrictedRingModule :
    Module (AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :=
  by
    letI : Semiring (AlgebraEnvelopingRing k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :=
      Algebra.TensorProduct.instSemiring
    letI : Module (AlgebraEnvelopingRing k
        (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
        (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :=
      Semiring.toModule
    exact Module.compHom _ (E.cutEnvelopingZeroInclusion Q).toRingHom

noncomputable def cutEnvelopingZeroRestrictedRingSMul :
    SMul (AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :=
  (E.cutEnvelopingZeroRestrictedRingModule Q).toSMul

theorem cutEnvelopingZeroRestrictedRingModule_smul
    (a : AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
    (b : AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :
    letI := E.cutEnvelopingZeroRestrictedRingSMul Q
    a • b = E.cutEnvelopingZeroInclusion Q a * b := rfl

theorem cutEnvelopingZeroRestrictedRingScalarTower :
    letI := E.cutEnvelopingZeroRestrictedRingSMul Q
    IsScalarTower k (AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) := by
  letI := E.cutEnvelopingZeroRestrictedRingSMul Q
  constructor
  intro c a b
  change E.cutEnvelopingZeroInclusion Q (c • a) * b =
    c • (E.cutEnvelopingZeroInclusion Q a * b)
  have hs : E.cutEnvelopingZeroInclusion Q (c • a) =
      c • E.cutEnvelopingZeroInclusion Q a :=
    (E.cutEnvelopingZeroInclusion Q).toLinearMap.map_smul c a
  rw [hs]
  exact Algebra.smul_mul_assoc c _ b

variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (AlgebraEnvelopingRing k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M]
  [IsScalarTower k (AlgebraEnvelopingRing k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M]

noncomputable def cutEnvelopingZeroRestrictedModule :
    Module (AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0)) M :=
  Module.compHom M (E.cutEnvelopingZeroInclusion Q).toRingHom

noncomputable def cutEnvelopingZeroRestrictedSMul :
    SMul (AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0)) M :=
  (E.cutEnvelopingZeroRestrictedModule Q M).toSMul

omit [Module k M] [IsScalarTower k (AlgebraEnvelopingRing k
  (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M] in
theorem cutEnvelopingZeroRestrictedModule_smul
    (a : AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0)) (x : M) :
    letI := E.cutEnvelopingZeroRestrictedSMul Q M
    a • x = E.cutEnvelopingZeroInclusion Q a • x := rfl

theorem cutEnvelopingZeroRestrictedModuleScalarTower :
    letI := E.cutEnvelopingZeroRestrictedSMul Q M
    IsScalarTower k (AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0)) M := by
  letI := E.cutEnvelopingZeroRestrictedSMul Q M
  constructor
  intro c a x
  change E.cutEnvelopingZeroInclusion Q (c • a) • x =
    c • (E.cutEnvelopingZeroInclusion Q a • x)
  have hs : E.cutEnvelopingZeroInclusion Q (c • a) =
      c • E.cutEnvelopingZeroInclusion Q a :=
    (E.cutEnvelopingZeroInclusion Q).toLinearMap.map_smul c a
  rw [hs]
  exact smul_assoc c _ x

omit [Module k M] [IsScalarTower k (AlgebraEnvelopingRing k
  (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M] in
theorem cutEnvelopingZeroRestrictedModuleEnvelopingScalarTower :
    letI := E.cutEnvelopingZeroRestrictedRingSMul Q
    letI := E.cutEnvelopingZeroRestrictedSMul Q M
    IsScalarTower (AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M := by
  letI := E.cutEnvelopingZeroRestrictedRingSMul Q
  letI := E.cutEnvelopingZeroRestrictedSMul Q M
  constructor
  intro a b x
  change (E.cutEnvelopingZeroInclusion Q a * b) • x =
    E.cutEnvelopingZeroInclusion Q a • (b • x)
  exact mul_smul _ _ x

end ASGinzburg.ZAlgebra.PeriodIso
