import ASGinzburg.GinzburgMinimalASResolution
import ASGinzburg.GinzburgFirstProjectiveYoneda
import ASGinzburg.GinzburgArrowPathClasses
import ASGinzburg.ASGenerators

/-! The genuine canonical native AS first differential has exactly the
literal original-arrow classes, with its actual coproduct indexing. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgOriginalTermIso_inclusion (φ : Q.Potential k)
    (v : Q.LiftVertex) (a : Q.incomingArrows v) :
    Sigma.ι (fun b : Q.incomingArrows v =>
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height (Q.incomingSource v b))) a ≫
      ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorOriginalTermIso Q v).inv =
    Sigma.ι (fun b : Q.GinzburgIncomingDegree v.1 0 =>
      (Q.unrolledJacobianZAlgebra k φ).representable
        (Q.height (Q.ginzburgPrefixGeneratorEndpoint v b.val)))
      (Q.ginzburgOriginalGeneratorEquiv v a) := by
  simp [ZAlgebra.ginzburgGeneratorOriginalTermIso, Sigma.whiskerEquiv]
  exact Category.id_comp _

theorem GinzburgRegular.nativeIncomingElement {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) (a : Q.incomingArrows v) :
    (h.minimalASResolution Q k v).incomingElement a =
      Q.ginzburgGeneratorOriginalArrowEntry k φ v (Q.ginzburgOriginalGeneratorEquiv v a) := by
  unfold ZAlgebra.ASResolution.incomingElement
  dsimp only [GinzburgRegular.minimalASResolution]
  rw [ginzburgASProjectiveD₁, ← Category.assoc, Q.ginzburgOriginalTermIso_inclusion]
  simpa only [Q.ginzburgOriginalGeneratorEndpoint] using
    Q.ginzburgOriginalRepresentableProjectiveMap_yoneda_entry k φ v
      (Q.ginzburgOriginalGeneratorEquiv v a)

end ASGinzburg.CutQuiver
