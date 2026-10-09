import ASGinzburg.GinzburgProjectiveBasisDifferentials

/-! Every genuine incoming generator has a concrete filtered
single-arrow representative at its own integer-sheet prefix endpoint. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgGeneratorUnitRepresentative
    (v : Q.LiftVertex) (r : ℤ) (a : Q.GinzburgIncomingDegree v.1 r) :
    Q.ginzburgGeneratorFiltrationAtDegree k
      (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r r
      (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2) :=
  Submodule.inclusion (Q.ginzburgGeneratorLayerAtDegree_le_filtration k _ _ _ _ _)
    (Q.ginzburgGeneratorPrefixSingleLayer k
      (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r r
      (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2) a
      (Q.ginzburgGeneratorUnitPrefix k v r a))

theorem ginzburgGeneratorUnitRepresentative_val
    (v : Q.LiftVertex) (r : ℤ) (a : Q.GinzburgIncomingDegree v.1 r) :
    (Q.ginzburgGeneratorUnitRepresentative k v r a).val=
      Q.ginzburgIncomingArrowPolynomial k v.1 r a :=
  Q.ginzburgGeneratorPrefixSingleLayer_unit_val k v r a

theorem ginzburgDualOriginalProjectiveMap_unit_basis (φ : Q.Potential k)
    (v : Q.LiftVertex) (a : Q.GinzburgIncomingDegree v.1 (-1)) :
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
        (Q.ginzburgPrefixGeneratorEndpoint v a.val) v
        (Q.ginzburgGeneratorUnitRepresentative k v (-1) a) :=
  Q.ginzburgDualOriginalProjectiveMap_basis k φ v a _
    (Q.ginzburgGeneratorUnitRepresentative_val k v (-1) a)

theorem ginzburgLoopDualProjectiveMap_unit_basis (φ : Q.Potential k)
    (v : Q.LiftVertex) (a : Q.GinzburgIncomingDegree v.1 (-2)) :
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
        (Q.ginzburgPrefixGeneratorEndpoint v a.val) v
        (Q.ginzburgGeneratorUnitRepresentative k v (-2) a) :=
  Q.ginzburgLoopDualProjectiveMap_basis k φ v a _
    (Q.ginzburgGeneratorUnitRepresentative_val k v (-2) a)

end ASGinzburg.CutQuiver
