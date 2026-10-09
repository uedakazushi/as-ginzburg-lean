import ASGinzburg.GinzburgLoopProjectiveConnectingClasses

/-! Actual filtered representatives cover the entire native loop
coefficient projective term, so the class formula determines every value. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

set_option maxRecDepth 2000 in
theorem ginzburgLoopCoefficientClass_surjective (φ : Q.Potential k)
    (x v : Q.LiftVertex) : Function.Surjective (Q.ginzburgLoopCoefficientClass k φ x v) := by
  intro y
  let e := Q.ginzburgLayerProjectiveComponentIso k φ x v (-2)
  obtain ⟨z,hz,he⟩ := moduleCochainHomologyClass_exists
    (Q.ginzburgAssociatedGradedComplex k φ x.1 v.1 (-2) (v.2-x.2)) (-2) (e.inv y)
  obtain ⟨f,rfl⟩ := (Q.ginzburgGeneratorHigherLayer k x.1 v.1 (-2) (-2)
    (v.2-x.2)).mkQ_surjective z
  refine ⟨f,?_⟩
  change e.hom (moduleCochainHomologyClass
    (Q.ginzburgAssociatedGradedComplex k φ x.1 v.1 (-2) (v.2-x.2)) (-2)
    (Submodule.Quotient.mk f) (Q.ginzburgLoopLayerQuotient_cycle k φ x.1 v.1 (v.2-x.2) f))=y
  rw [show moduleCochainHomologyClass
    (Q.ginzburgAssociatedGradedComplex k φ x.1 v.1 (-2) (v.2-x.2)) (-2)
    (Submodule.Quotient.mk f) (Q.ginzburgLoopLayerQuotient_cycle k φ x.1 v.1 (v.2-x.2) f)=e.inv y from he]
  change (e.inv ≫ e.hom) y=y
  rw [e.inv_hom_id]
  rfl

end ASGinzburg.CutQuiver
