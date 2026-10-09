import ASGinzburg.GinzburgLayerProjectiveNaturality
import ASGinzburg.GinzburgGeneratorUpperFiltration

/-! The actual upper filtered homology comparison with the projective
original-generator module preserves genuine right precomposition. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgUpperProjectiveComponentIso (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgGeneratorFilteredHomology k φ x.1 v.1 0 (v.2-x.2) 0 ≅
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v 0) :=
  Q.ginzburgGeneratorFilteredZeroHomologyIso k φ x.1 v.1 (v.2-x.2) 0 ≪≫
    Q.ginzburgLayerProjectiveComponentIso k φ x v 0

theorem ginzburgUpperProjectiveComponentIso_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgFilteredLeftHomology k φ (v:=v) 0 0 f ≫
        (Q.ginzburgUpperProjectiveComponentIso k φ x v).hom=
      (Q.ginzburgUpperProjectiveComponentIso k φ y v).hom ≫
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v 0).obj.map
          (show (⟨Q.height x⟩ : (Q.unrolledJacobianZAlgebra k φ).Obj) ⟶ ⟨Q.height y⟩ from
            Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y (Submodule.Quotient.mk f)).op := by
  have he : Q.ginzburgFilteredLeftHomology k φ (v:=v) 0 0 f ≫
        (Q.ginzburgGeneratorFilteredZeroHomologyIso k φ x.1 v.1 (v.2-x.2) 0).hom=
      (Q.ginzburgGeneratorFilteredZeroHomologyIso k φ y.1 v.1 (v.2-y.2) 0).hom ≫
        Q.ginzburgAssociatedLeftHomology k φ (v:=v) 0 0 f :=
    Q.ginzburgFilteredQuotientHomology_left_naturality k φ 0 0 f
  simp only [ginzburgUpperProjectiveComponentIso,Iso.trans_hom]
  rw [← Category.assoc,he,Category.assoc,
    Q.ginzburgLayerProjectiveComponentIso_left_naturality,← Category.assoc]

end ASGinzburg.CutQuiver
