import ASGinzburg.GinzburgCutZeroQuotientProducts

/-! Arithmetic transport of actual fixed-cut degree-zero spaces and
their actual differential-boundary quotients preserves coefficient classes. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgCutZeroEquivOfCutEq (u v : Q.Vertex) (c d : ℤ) (h : c=d) :
    Q.ginzburgCutCohomologicalComponent k u v 0 c ≃ₗ[k]
      Q.ginzburgCutCohomologicalComponent k u v 0 d := by
  cases h
  exact LinearEquiv.refl k _

noncomputable def ginzburgCutZeroQuotientEquivOfCutEq (φ : Q.Potential k)
    (u v : Q.Vertex) (c d : ℤ) (h : c=d) :
    (Q.ginzburgCutCohomologicalComponent k u v 0 c ⧸
      LinearMap.range (Q.ginzburgCutNegativeOneDifferential k φ u v c)) ≃ₗ[k]
    (Q.ginzburgCutCohomologicalComponent k u v 0 d ⧸
      LinearMap.range (Q.ginzburgCutNegativeOneDifferential k φ u v d)) := by
  cases h
  exact LinearEquiv.refl k _

theorem ginzburgCutZeroEquivOfCutEq_apply_coe (u v : Q.Vertex) (c d : ℤ) (h : c=d)
    (f : Q.ginzburgCutCohomologicalComponent k u v 0 c) :
    (Q.ginzburgCutZeroEquivOfCutEq k u v c d h f).val=f.val := by
  cases h
  rfl

theorem ginzburgCutZeroQuotientEquivOfCutEq_mk (φ : Q.Potential k)
    (u v : Q.Vertex) (c d : ℤ) (h : c=d)
    (f : Q.ginzburgCutCohomologicalComponent k u v 0 c) :
    Q.ginzburgCutZeroQuotientEquivOfCutEq k φ u v c d h (Submodule.Quotient.mk f)=
      Submodule.Quotient.mk (Q.ginzburgCutZeroEquivOfCutEq k u v c d h f) := by
  cases h
  rfl

end ASGinzburg.CutQuiver
