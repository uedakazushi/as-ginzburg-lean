import ASGinzburg.GinzburgCutCochainComplex

/-! The actual homology of every fixed cut component is finite dimensional,
via mathlib's kernel/image quotient description of short complex homology. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

instance ginzburgCutHomology_finite (φ : Q.Potential k) (u v : Q.Vertex) (c q : ℤ) :
    Module.Finite k (Q.ginzburgCutHomology k φ u v c q) := by
  let S := (Q.ginzburgCutCochainComplex k φ u v c).sc q
  haveI : Module.Finite k S.X₂ := by
    change Module.Finite k (Q.ginzburgCutCohomologicalComponent k u v q c)
    infer_instance
  haveI : Module.Finite k S.moduleCatLeftHomologyData.H := by
    change Module.Finite k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

end ASGinzburg.CutQuiver
