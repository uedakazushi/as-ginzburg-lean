import ASGinzburg.GinzburgFirstProjectiveBasis
import ASGinzburg.GinzburgProjectiveBasisYoneda

/-! The actual first differential's Yoneda row is its original-arrow
Jacobian class, with the unchanged generator coproduct indexing. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgOriginalRepresentableProjectiveMap_yoneda_entry
    (φ : Q.Potential k) (v : Q.LiftVertex) (a : Q.GinzburgIncomingDegree v.1 0) :
    (Q.unrolledJacobianZAlgebra k φ).representableYonedaEquiv
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))
      ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height v))
      (Sigma.ι (fun b : Q.GinzburgIncomingDegree v.1 0 =>
        (Q.unrolledJacobianZAlgebra k φ).representable
          (Q.height (Q.ginzburgPrefixGeneratorEndpoint v b.val))) a ≫
        Q.ginzburgOriginalRepresentableProjectiveMap k φ v)=
      Q.ginzburgGeneratorOriginalArrowEntry k φ v a := by
  rw [(Q.unrolledJacobianZAlgebra k φ).representableYonedaEquiv_comp]
  have h := congrArg (fun y =>
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))).map
      (Q.ginzburgOriginalRepresentableProjectiveMap k φ v) y)
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientYoneda_inclusion Q v 0 a)
  exact h.trans (Q.ginzburgOriginalRepresentableProjectiveMap_unit_basis k φ v a)

end ASGinzburg.CutQuiver
