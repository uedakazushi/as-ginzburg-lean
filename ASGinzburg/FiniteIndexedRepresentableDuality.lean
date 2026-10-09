import ASGinzburg.FiniteRepresentableDualMatrix
import ASGinzburg.FiniteProjectiveDuality

/-! Actual A-duality preserves every finite indexed representable sum,
and its actual component maps obey the genuine transposed matrix formula. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
variable {I J : Type} [Fintype I] [Fintype J]

noncomputable def rightIndexedFiniteSumADualIso (i : I → ℤ) :
    A.rightModuleADual (∐ fun a => A.representable (i a)) ≅
      ∐ fun a => A.leftRepresentable (i a) := by
  letI : HasFiniteBiproducts A.RightModuleᵒᵖ := HasFiniteBiproducts.of_hasFiniteProducts
  exact A.rightModuleADualFunctor.mapIso
    (opCoproductIsoProduct (fun a => A.representable (i a)) ≪≫
      (biproduct.isoProduct (fun a => op (A.representable (i a)))).symm ≪≫
        biproduct.isoCoproduct _) ≪≫
    PreservesCoproduct.iso A.rightModuleADualFunctor (fun a => op (A.representable (i a))) ≪≫
      HasColimit.isoOfNatIso (Discrete.natIso (fun a => A.representableADualIso (i a.as)))

noncomputable def leftIndexedFiniteSumADualIso (i : I → ℤ) :
    A.leftModuleADual (∐ fun a => A.leftRepresentable (i a)) ≅
      ∐ fun a => A.representable (i a) := by
  letI : HasFiniteBiproducts A.LeftModuleᵒᵖ := HasFiniteBiproducts.of_hasFiniteProducts
  exact A.leftModuleADualFunctor.mapIso
    (opCoproductIsoProduct (fun a => A.leftRepresentable (i a)) ≪≫
      (biproduct.isoProduct (fun a => op (A.leftRepresentable (i a)))).symm ≪≫
        biproduct.isoCoproduct _) ≪≫
    PreservesCoproduct.iso A.leftModuleADualFunctor (fun a => op (A.leftRepresentable (i a))) ≪≫
      HasColimit.isoOfNatIso (Discrete.natIso (fun a => A.leftRepresentableADualIso (i a.as)))

theorem rightModuleADualMap_indexed_matrix [DecidableEq J]
    (i : I → ℤ) (j : J → ℤ) (l : ℤ)
    (d : ∐ (fun a => A.representable (i a)) ⟶ ∐ (fun b => A.representable (j b)))
    (f : ∐ (fun b => A.representable (j b)) ⟶ A.representable l) (a : I) :
    A.rightRepresentableCoproductHomEquiv i (A.representable l)
      ((A.rightModuleADualMap d).app ⟨l⟩ f) a=
      ∑ b, A.comp (A.rightRepresentableCoproductHomEquiv j (A.representable l) f b)
        (A.rightFiniteCoproductPiEquiv (fun b => A.representable (j b)) (i a)
          (A.representableYonedaEquiv (i a) (∐ fun b => A.representable (j b))
            (Sigma.ι (fun a => A.representable (i a)) a ≫ d)) b) :=
  A.rightRepresentableCoproductHomEquiv_precomp i j l d f a

end ASGinzburg.ZAlgebra
