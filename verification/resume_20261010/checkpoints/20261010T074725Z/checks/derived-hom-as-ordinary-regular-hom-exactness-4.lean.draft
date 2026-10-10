import ASGinzburg.ModuleCatHomUniverseExt
import work.ASGinzburgDraft.ASCutOrdinaryHomogeneousRegularHomExactness
import work.ASGinzburgDraft.ASCutForgottenGradedSimpleResolution
import work.ASGinzburgDraft.GradedOrdinaryRingDualExactness
import work.ASGinzburgDraft.PeriodCutOrdinaryRingDualHomExactness
import work.ASGinzburgDraft.PeriodCutOppositeRingDecomposition
import work.ASGinzburgDraft.PeriodCutIntegerHomogeneousMultiplication

/-! Original AS regularity gives genuine ordinary-ring Hom exactness.
Each ordinary cocycle has finitely many actual homogeneous components;
the graded AS Hom exactness provides boundary preimages for each component. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
attribute [local instance 2500] moduleCatHomUniverseHasExt
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

 theorem ASRegular.cutOrdinarySimpleHomComplex_regular_exact_zero
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    ((hAS.cutForgottenGradedSimpleProjectiveResolution A Q i).homComplex (k := k)
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ)).ExactAt 0 := by
  let E := hAS.periodIso A Q
  let R := (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
  let P := hAS.cutForgottenGradedSimpleProjectiveResolution A Q i
  let G := hAS.cutGradedSimpleProjectiveResolution A Q (i,0)
  let M := hAS.cutOrdinarySimpleResolutionTermData A Q i 0
  let N := hAS.cutOrdinarySimpleResolutionTermData A Q i 1
  letI := E.cutIntegerOppositeGradeDecomposition Q
  apply (P.homComplex_exactAt_zero_iff (k := k) (ModuleCat.of R R)).mpr
  intro f hf
  have hc : ordinaryRingDualMap R (P.complex.d 1 0) f.hom = 0 :=
    congrArg ModuleCat.Hom.hom hf
  have hz : f.hom = 0 := M.ringDualCycle_eq_zero_of_homogeneous_cycles_eq_zero N
    (E.cutIntegerOppositeHomogeneousSpace_mul_mem Q) (P.complex.d 1 0)
    (hAS.cutForgottenGradedSimpleResolution_d_preservesGrade A Q i 0)
    (fun q g hg hcycle => hAS.cutOrdinarySimpleHomogeneousRegular_cycle_zero A Q i q g hg hcycle)
    f.hom hc
  exact ModuleCat.hom_ext hz

 theorem ASRegular.cutOrdinarySimpleHomComplex_regular_exact_succ_low
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) (hn : n + 1 < 3) :
    ((hAS.cutForgottenGradedSimpleProjectiveResolution A Q i).homComplex (k := k)
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ)).ExactAt (n+1) := by
  let E := hAS.periodIso A Q
  let R := (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
  let P := hAS.cutForgottenGradedSimpleProjectiveResolution A Q i
  let M := hAS.cutOrdinarySimpleResolutionTermData A Q i (n+1)
  let N := hAS.cutOrdinarySimpleResolutionTermData A Q i (n+2)
  let L := hAS.cutOrdinarySimpleResolutionTermData A Q i n
  letI := E.cutIntegerOppositeGradeDecomposition Q
  letI : Module.Finite R M.ringModule :=
    hAS.cutOrdinarySimpleResolutionTermData_finite A Q i (n+1)
  apply (P.homComplex_exactAt_succ_iff (k := k) (ModuleCat.of R R) n).mpr
  intro f hf
  have hc : ordinaryRingDualMap R (P.complex.d (n+2) (n+1)) f.hom = 0 :=
    congrArg ModuleCat.Hom.hom hf
  obtain ⟨g,hg⟩ := M.ringDualCycle_exists_boundary_of_homogeneous_exactness N
    (E.cutIntegerOppositeHomogeneousSpace_mul_mem Q) L
    (P.complex.d (n+1) n) (P.complex.d (n+2) (n+1))
    (hAS.cutForgottenGradedSimpleResolution_d_preservesGrade A Q i (n+1))
    (fun q g hg hcycle => hAS.cutOrdinarySimpleHomogeneousRegular_boundary_low A Q i n hn q g hg hcycle)
    f.hom hc
  exact ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩

 theorem ASRegular.cutOrdinarySimpleHomComplex_regular_exact_low
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) (hn : n < 3) :
    ((hAS.cutForgottenGradedSimpleProjectiveResolution A Q i).homComplex (k := k)
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ)).ExactAt n := by
  cases n with
  | zero => exact hAS.cutOrdinarySimpleHomComplex_regular_exact_zero A Q i
  | succ n => exact hAS.cutOrdinarySimpleHomComplex_regular_exact_succ_low A Q i n hn

 theorem ASRegular.cutOrdinarySimpleExt_regular_eq_zero_low
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) (hn : n < 3)
    (e : Abelian.Ext.{v} (hAS.cutOrdinarySimple A Q (i,0))
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ) n) : e = 0 :=
  (hAS.cutForgottenGradedSimpleProjectiveResolution A Q i).ext_low_eq_zero_of_homComplex_exact
    (k := k) (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ)
    n hn (hAS.cutOrdinarySimpleHomComplex_regular_exact_low A Q i n hn) e

end ASGinzburg.ZAlgebra
