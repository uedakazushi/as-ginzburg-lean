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
  Module.compHom _ (E.cutEnvelopingZeroInclusion Q).toRingHom

attribute [local instance 2000] cutEnvelopingZeroRestrictedRingModule

theorem cutEnvelopingZeroRestrictedRingModule_smul
    (a : AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
    (b : AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :
    a • b = E.cutEnvelopingZeroInclusion Q a * b := rfl

theorem cutEnvelopingZeroRestrictedRingScalarTower :
    IsScalarTower k (AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) := by
  constructor
  intro c a b
  change E.cutEnvelopingZeroInclusion Q (c • a) * b =
    c • (E.cutEnvelopingZeroInclusion Q a * b)
  rw [(E.cutEnvelopingZeroInclusion Q).toLinearMap.map_smul]
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

attribute [local instance 2000] cutEnvelopingZeroRestrictedModule

theorem cutEnvelopingZeroRestrictedModule_smul
    (a : AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0)) (x : M) :
    a • x = E.cutEnvelopingZeroInclusion Q a • x := rfl

theorem cutEnvelopingZeroRestrictedModuleScalarTower :
    IsScalarTower k (AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0)) M := by
  constructor
  intro c a x
  change E.cutEnvelopingZeroInclusion Q (c • a) • x =
    c • (E.cutEnvelopingZeroInclusion Q a • x)
  rw [(E.cutEnvelopingZeroInclusion Q).toLinearMap.map_smul]
  exact smul_assoc c _ x

theorem cutEnvelopingZeroRestrictedModuleEnvelopingScalarTower :
    IsScalarTower (AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M := by
  constructor
  intro a b x
  change (E.cutEnvelopingZeroInclusion Q a * b) • x =
    E.cutEnvelopingZeroInclusion Q a • (b • x)
  exact mul_smul _ _ x

end ASGinzburg.ZAlgebra.PeriodIso
