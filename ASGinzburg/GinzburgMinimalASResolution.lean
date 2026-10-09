import ASGinzburg.GinzburgASMiddleMinimality
import ASGinzburg.GinzburgASEndpointMinimality
import ASGinzburg.GinzburgASProjectiveExactness

/-! Genuine Ginzburg regularity implies the original finite minimal
AS-resolution condition, on the existing right-module definitions.
The Ext/rank condition of ASRegular remains a separate theorem. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def GinzburgRegular.minimalASResolution {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).ASResolution Q v where
  d₁ := Q.ginzburgASProjectiveD₁ k φ v
  d₂ := Q.ginzburgASProjectiveD₂ k φ v
  d₃ := Q.ginzburgASProjectiveD₃ k φ v
  d₁_π := Q.ginzburgASProjectiveD₁_comp_simpleπ k φ v
  d₂_d₁ := Q.ginzburgASProjectiveD₂_comp_D₁ k φ v
  d₃_d₂ := Q.ginzburgASProjectiveD₃_comp_D₂ k φ v
  exact₀ := Q.ginzburgASProjectiveOriginalSimpleShortComplex_exact k φ v
  exact₁ := Q.ginzburgASProjectiveDualOriginalShortComplex_exact k φ v
  exact₂ := h.asProjectiveConnectingShortComplex_exact Q k v
  mono_d₃ := h.asProjectiveD₃_mono Q k v
  minimal₁ := Q.ginzburgASProjectiveD₁_minimal k φ v
  minimal₂ := Q.ginzburgASProjectiveD₂_minimal k φ v
  minimal₃ := Q.ginzburgASProjectiveD₃_minimal k φ v

theorem GinzburgRegular.exists_ASResolution {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    Nonempty ((Q.unrolledJacobianZAlgebra k φ).ASResolution Q v) :=
  ⟨h.minimalASResolution Q k v⟩

end ASGinzburg.CutQuiver
