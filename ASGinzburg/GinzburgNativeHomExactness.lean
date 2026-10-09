import ASGinzburg.GinzburgADualShortComplexes

/-! The native Hom sequence has a zero initial kernel and actual
lifts of every closed Hom element, without any Ext vanishing assumption. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k] (φ : Q.Potential k)

theorem GinzburgRegular.nativeHom_zero_kernel
    (h : Q.GinzburgRegular k φ) (v l : Q.LiftVertex)
    (f : (Q.unrolledJacobianZAlgebra k φ).representable (Q.height v) ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height l))
    (hf : Q.ginzburgOriginalRepresentableProjectiveMap k φ v ≫ f=0) : f=0 := by
  have hm := (h.opposite Q k).loopDualProjectiveMap_mono Q.opposite k
    (Q.ginzburgDualOppositeBase v)
  have hi := ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).rightModule_mono_iff_injective _).mp hm
    (Q.opposite.height (Q.oppositeLiftVertexEquiv l))
  apply (Q.ginzburgRepresentableADualOppositeLoopComponentEquiv k φ v l).injective
  rw [map_zero]
  apply hi
  rw [map_zero,←Q.ginzburgOriginalRepresentableProjectiveMap_adual_opposite]
  change Q.ginzburgOriginalADualOppositeComponentEquiv k φ v l
    (Q.ginzburgOriginalRepresentableProjectiveMap k φ v ≫ f)=0
  rw [hf,map_zero]

theorem GinzburgRegular.nativeHom_lift_one
    (h : Q.GinzburgRegular k φ) (v l : Q.LiftVertex)
    (f : (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v 0 ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height l))
    (hf : Q.ginzburgDualOriginalProjectiveMap k φ v ≫ f=0) :
    ∃ g : (Q.unrolledJacobianZAlgebra k φ).representable (Q.height v) ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height l),
      Q.ginzburgOriginalRepresentableProjectiveMap k φ v ≫ g=f := by
  have he := h.homOriginalDualShortComplex_exact Q k φ v l
  rw [ShortComplex.moduleCat_exact_iff] at he
  exact he f hf

theorem ginzburgNativeHom_lift_two (v l : Q.LiftVertex)
    (f : (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-1) ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height l))
    (hf : Q.ginzburgLoopDualProjectiveMap k φ v ≫ f=0) :
    ∃ g : (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v 0 ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height l),
      Q.ginzburgDualOriginalProjectiveMap k φ v ≫ g=f := by
  have he := Q.ginzburgHomDualLoopShortComplex_exact k φ v l
  rw [ShortComplex.moduleCat_exact_iff] at he
  exact he f hf

end ASGinzburg.CutQuiver
