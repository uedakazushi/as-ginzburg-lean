import work.ASGinzburgDraft.ASCutGradedRegularHomExactness
import work.ASGinzburgDraft.ASCutOrdinarySimpleGradedResolution
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
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

 theorem ASRegular.cutOrdinarySimpleHomComplex_regular_exact_zero
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    ((hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)).homComplex (k := k)
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ)).ExactAt 0 := by
  let E := hAS.periodIso A Q
  let R := (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
  let P := hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)
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
    (hAS.cutOrdinarySimpleResolution_d_preservesGrade A Q i 0) (by
      intro q g hg hcycle
      apply E.cutOrdinaryRingDual_homogeneous_cycle_eq_zero Q
        (G.complex.d 1 0) q ⟨g,hg⟩ hcycle
      exact (G.homComplex_exactAt_zero_iff (k := k)
        ((E.cutRegularGradedRightModule Q).shifted q)).mp
        (hAS.cutGradedSimpleHomComplex_regular_exact_low A Q i q 0 (by omega)))
    f.hom hc
  exact ModuleCat.hom_ext hz

 theorem ASRegular.cutOrdinarySimpleHomComplex_regular_exact_succ_low
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) (hn : n + 1 < 3) :
    ((hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)).homComplex (k := k)
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ)).ExactAt (n+1) := by
  have hCases : n = 0 ∨ n = 1 := by omega
  rcases hCases with rfl | rfl
  · let E := hAS.periodIso A Q
    let R := (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
    let P := hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)
    let G := hAS.cutGradedSimpleProjectiveResolution A Q (i,0)
    let M := hAS.cutOrdinarySimpleResolutionTermData A Q i (0+1)
    let N := hAS.cutOrdinarySimpleResolutionTermData A Q i (0+2)
    let L := hAS.cutOrdinarySimpleResolutionTermData A Q i 0
    letI := E.cutIntegerOppositeGradeDecomposition Q
    letI : Module.Finite R M.ringModule :=
      hAS.cutOrdinarySimpleResolutionTermData_finite A Q i (0+1)
    apply (P.homComplex_exactAt_succ_iff (k := k) (ModuleCat.of R R) 0).mpr
    intro f hf
    have hc : ordinaryRingDualMap R (P.complex.d (0+2) (0+1)) f.hom = 0 :=
      congrArg ModuleCat.Hom.hom hf
    obtain ⟨g,hg⟩ := M.ringDualCycle_exists_boundary_of_homogeneous_exactness N
      (E.cutIntegerOppositeHomogeneousSpace_mul_mem Q) L
      (P.complex.d (0+1) 0) (P.complex.d (0+2) (0+1))
      (hAS.cutOrdinarySimpleResolution_d_preservesGrade A Q i (0+1)) (by
        intro q g hg hcycle
        apply E.cutOrdinaryRingDual_homogeneous_boundary Q
          (G.complex.d (0+1) 0) (G.complex.d (0+2) (0+1)) q ⟨g,hg⟩ hcycle
        exact (G.homComplex_exactAt_succ_iff (k := k)
          ((E.cutRegularGradedRightModule Q).shifted q) 0).mp
          (hAS.cutGradedSimpleHomComplex_regular_exact_low A Q i q (0+1) (by decide)))
      f.hom hc
    exact ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩
  · let E := hAS.periodIso A Q
    let R := (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
    let P := hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)
    let G := hAS.cutGradedSimpleProjectiveResolution A Q (i,0)
    let M := hAS.cutOrdinarySimpleResolutionTermData A Q i (1+1)
    let N := hAS.cutOrdinarySimpleResolutionTermData A Q i (1+2)
    let L := hAS.cutOrdinarySimpleResolutionTermData A Q i 1
    letI := E.cutIntegerOppositeGradeDecomposition Q
    letI : Module.Finite R M.ringModule :=
      hAS.cutOrdinarySimpleResolutionTermData_finite A Q i (1+1)
    apply (P.homComplex_exactAt_succ_iff (k := k) (ModuleCat.of R R) 1).mpr
    intro f hf
    have hc : ordinaryRingDualMap R (P.complex.d (1+2) (1+1)) f.hom = 0 :=
      congrArg ModuleCat.Hom.hom hf
    obtain ⟨g,hg⟩ := M.ringDualCycle_exists_boundary_of_homogeneous_exactness N
      (E.cutIntegerOppositeHomogeneousSpace_mul_mem Q) L
      (P.complex.d (1+1) 1) (P.complex.d (1+2) (1+1))
      (hAS.cutOrdinarySimpleResolution_d_preservesGrade A Q i (1+1)) (by
        intro q g hg hcycle
        apply E.cutOrdinaryRingDual_homogeneous_boundary Q
          (G.complex.d (1+1) 1) (G.complex.d (1+2) (1+1)) q ⟨g,hg⟩ hcycle
        exact (G.homComplex_exactAt_succ_iff (k := k)
          ((E.cutRegularGradedRightModule Q).shifted q) 1).mp
          (hAS.cutGradedSimpleHomComplex_regular_exact_low A Q i q (1+1) (by decide)))
      f.hom hc
    exact ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩

 theorem ASRegular.cutOrdinarySimpleHomComplex_regular_exact_low
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) (hn : n < 3) :
    ((hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)).homComplex (k := k)
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ)).ExactAt n := by
  cases n with
  | zero => exact hAS.cutOrdinarySimpleHomComplex_regular_exact_zero A Q i
  | succ n => exact hAS.cutOrdinarySimpleHomComplex_regular_exact_succ_low A Q i n hn

 theorem ASRegular.cutOrdinarySimpleExt_regular_eq_zero_low
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) (hn : n < 3)
    (e : Abelian.Ext.{v} (hAS.cutOrdinarySimple A Q (i,0))
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ) n) : e = 0 :=
  (hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)).ext_low_eq_zero_of_homComplex_exact
    (k := k) (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ)
    n hn (hAS.cutOrdinarySimpleHomComplex_regular_exact_low A Q i n hn) e

end ASGinzburg.ZAlgebra
