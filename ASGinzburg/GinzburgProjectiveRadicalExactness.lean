import ASGinzburg.GinzburgProjectiveRadicalMap

/-! Actual right-module exactness at the original generator projective,
and its genuine radical epimorphism. No regularity hypothesis is needed. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgDualOriginalProjectiveMap_comp_radical (φ : Q.Potential k) (v : Q.LiftVertex) :
    Q.ginzburgDualOriginalProjectiveMap k φ v ≫
      Q.ginzburgOriginalRadicalProjectiveMap k φ v=0 := by
  apply (Q.unrolledJacobianZAlgebra k φ).rightModuleHom_ext_lift Q
  intro x
  rw [Functor.map_comp,Functor.map_zero,ginzburgDualOriginalProjectiveMap_component,
    ginzburgOriginalRadicalProjectiveMap_component]
  exact Q.ginzburgDualOriginalProjectiveComponent_comp_radical k φ x v

noncomputable def ginzburgProjectiveDualRadicalShortComplex (φ : Q.Potential k)
    (v : Q.LiftVertex) : ShortComplex (Q.unrolledJacobianZAlgebra k φ).RightModule :=
  ShortComplex.mk (Q.ginzburgDualOriginalProjectiveMap k φ v)
    (Q.ginzburgOriginalRadicalProjectiveMap k φ v)
    (Q.ginzburgDualOriginalProjectiveMap_comp_radical k φ v)

theorem ginzburgProjectiveDualRadicalShortComplex_exact (φ : Q.Potential k)
    (v : Q.LiftVertex) :
    (Q.ginzburgProjectiveDualRadicalShortComplex k φ v).Exact := by
  apply ((Q.unrolledJacobianZAlgebra k φ).rightModule_exact_iff_lift Q _).mpr
  intro x
  simpa only [ginzburgProjectiveDualRadicalShortComplex,ShortComplex.map,
    ginzburgDualOriginalProjectiveMap_component,ginzburgOriginalRadicalProjectiveMap_component,
    ginzburgProjectiveDualRadicalComponentShortComplex] using
    Q.ginzburgProjectiveDualRadicalComponentShortComplex_exact k φ x v

noncomputable def ginzburgOriginalRepresentableProjectiveMap (φ : Q.Potential k)
    (v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v 0 ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height v) :=
  Q.ginzburgOriginalRadicalProjectiveMap k φ v ≫
    ((Q.unrolledJacobianZAlgebra k φ).representableRadical (Q.height v)).inclusion

theorem ginzburgDualOriginalProjectiveMap_comp_representable (φ : Q.Potential k)
    (v : Q.LiftVertex) :
    Q.ginzburgDualOriginalProjectiveMap k φ v ≫
      Q.ginzburgOriginalRepresentableProjectiveMap k φ v=0 := by
  rw [ginzburgOriginalRepresentableProjectiveMap,← Category.assoc,
    ginzburgDualOriginalProjectiveMap_comp_radical,zero_comp]

theorem ginzburgOriginalRepresentableProjectiveMap_comp_simpleπ (φ : Q.Potential k)
    (v : Q.LiftVertex) :
    Q.ginzburgOriginalRepresentableProjectiveMap k φ v ≫
      (Q.unrolledJacobianZAlgebra k φ).simpleRightModuleπ (Q.height v)=0 := by
  rw [ginzburgOriginalRepresentableProjectiveMap,Category.assoc]
  simp only [ZAlgebra.simpleRightModuleπ,ZAlgebra.RightSubmodule.quotientπ,
    cokernel.condition,comp_zero]

noncomputable def ginzburgProjectiveOriginalSimpleShortComplex (φ : Q.Potential k)
    (v : Q.LiftVertex) : ShortComplex (Q.unrolledJacobianZAlgebra k φ).RightModule :=
  ShortComplex.mk (Q.ginzburgOriginalRepresentableProjectiveMap k φ v)
    ((Q.unrolledJacobianZAlgebra k φ).simpleRightModuleπ (Q.height v))
    (Q.ginzburgOriginalRepresentableProjectiveMap_comp_simpleπ k φ v)

theorem ginzburgProjectiveOriginalSimpleShortComplex_exact (φ : Q.Potential k)
    (v : Q.LiftVertex) :
    (Q.ginzburgProjectiveOriginalSimpleShortComplex k φ v).Exact := by
  let A := Q.unrolledJacobianZAlgebra k φ
  let S := (A.representableRadical (Q.height v)).quotientShortComplex
  let f : Q.ginzburgProjectiveOriginalSimpleShortComplex k φ v ⟶ S :=
    ShortComplex.homMk (Q.ginzburgOriginalRadicalProjectiveMap k φ v) (𝟙 _) (𝟙 _)
      (by simp [S,ginzburgProjectiveOriginalSimpleShortComplex,
        ginzburgOriginalRepresentableProjectiveMap,ZAlgebra.RightSubmodule.quotientShortComplex,A])
      (by simp [S,ginzburgProjectiveOriginalSimpleShortComplex,ZAlgebra.simpleRightModuleπ,
        ZAlgebra.RightSubmodule.quotientShortComplex,A])
  haveI : Epi f.τ₁ := Q.ginzburgOriginalRadicalProjectiveMap_epi k φ v
  haveI : IsIso f.τ₂ := by dsimp [f]; infer_instance
  haveI : Mono f.τ₃ := by dsimp [f]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mpr
    (A.simpleRightModule_shortExact (Q.height v)).exact

end ASGinzburg.CutQuiver
