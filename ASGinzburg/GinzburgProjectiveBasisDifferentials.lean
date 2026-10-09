import ASGinzburg.GinzburgSingleGeneratorProjectiveBasis

/-! The native projective differentials on actual identity basis vectors
are the concrete differential-prefix quotient classes already computed. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgDualOriginalProjectiveMap_basis (φ : Q.Potential k)
    (v : Q.LiftVertex) (a : Q.GinzburgIncomingDegree v.1 (-1))
    (f : Q.ginzburgGeneratorFiltrationAtDegree k
      (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 (-1) (-1)
      (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2))
    (hf : f.val=Q.ginzburgIncomingArrowPolynomial k v.1 (-1) a) :
    (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v 0
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))
      (((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation
        (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))).map
        (Q.ginzburgDualOriginalProjectiveMap k φ v)
        (((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v (-1)
          (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))).symm
          (Pi.single a ((Q.unrolledJacobianZAlgebra k φ).id
            (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))))))=
      Q.ginzburgOriginalDifferentialCoefficients k φ
        (Q.ginzburgPrefixGeneratorEndpoint v a.val) v f := by
  rw [←Q.ginzburgDualCoefficientClass_single k φ v a f hf]
  exact Q.ginzburgDualOriginalProjectiveMap_class k φ _ v f

theorem ginzburgLoopDualProjectiveMap_basis (φ : Q.Potential k)
    (v : Q.LiftVertex) (a : Q.GinzburgIncomingDegree v.1 (-2))
    (f : Q.ginzburgGeneratorFiltrationAtDegree k
      (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 (-2) (-2)
      (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2))
    (hf : f.val=Q.ginzburgIncomingArrowPolynomial k v.1 (-2) a) :
    (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v (-1)
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))
      (((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation
        (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))).map
        (Q.ginzburgLoopDualProjectiveMap k φ v)
        (((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v (-2)
          (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))).symm
          (Pi.single a ((Q.unrolledJacobianZAlgebra k φ).id
            (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))))))=
      Q.ginzburgDualDifferentialCoefficients k φ
        (Q.ginzburgPrefixGeneratorEndpoint v a.val) v f := by
  rw [←Q.ginzburgLoopCoefficientClass_single k φ v a f hf]
  exact Q.ginzburgLoopDualProjectiveMap_class k φ _ v f

end ASGinzburg.CutQuiver
