import ASGinzburg.PeriodCutModuleDegreeComponents

/-! A genuine graded R-module is the actual finite-support direct sum
of its recovered vertex/sheet components. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

noncomputable def degreeComponentEquiv (M : E.CutGradedRightModule Q) (q : ℤ) :
    M.grade q ≃ₗ[k] ⨁ i : Q.Vertex,M.componentSubmodule (i,-q) :=
  (M.degreeVertexEquiv q).trans
    (DirectSum.linearEquivFunOnFintype k Q.Vertex (fun i => ↥(M.componentSubmodule (i,-q)))).symm

noncomputable def totalDegreeComponentEquiv (M : E.CutGradedRightModule Q) :
    M.space ≃ₗ[k] ⨁ q : ℤ,⨁ i : Q.Vertex,M.componentSubmodule (i,-q) := by
  letI : DirectSum.Decomposition M.grade := M.decomposition
  exact (DirectSum.decomposeLinearEquiv M.grade).trans
    (DFinsupp.mapRange.linearEquiv M.degreeComponentEquiv)

noncomputable def componentRegroupEquiv (M : E.CutGradedRightModule Q) :
    (⨁ x : Q.LiftVertex,M.componentSubmodule x) ≃ₗ[k]
      ⨁ q : ℤ,⨁ i : Q.Vertex,M.componentSubmodule (i,-q) :=
  (DirectSum.lequivCongrLeft k (M:=fun x => ↥(M.componentSubmodule x))
    Q.moduleDegreeVertexEquiv).trans
    (DirectSum.sigmaLcurryEquiv k (δ:=fun q i => ↥(M.componentSubmodule (i,-q))))

noncomputable def componentTotalEquiv (M : E.CutGradedRightModule Q) :
    M.space ≃ₗ[k] ⨁ x : Q.LiftVertex,M.componentSubmodule x :=
  M.totalDegreeComponentEquiv.trans M.componentRegroupEquiv.symm

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
