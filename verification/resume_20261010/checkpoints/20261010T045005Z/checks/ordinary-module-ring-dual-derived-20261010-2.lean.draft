import work.ASGinzburgDraft.OrdinaryModuleRingDual
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.CategoryTheory.Abelian.RightDerived

/-! The actual right-derived contravariant ring dual carries its natural
opposite-ring module structure. Ordinary projective resolutions compute
it after passing to the opposite category. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits Opposite
universe v
variable (R : Type v) [Ring R]

noncomputable def ordinarySingleZeroOppositeIso (M : ModuleCat.{v} R) :
    (CochainComplex.single₀ (ModuleCat.{v} R)ᵒᵖ).obj (op M) ≅
      ((ChainComplex.single₀ (ModuleCat.{v} R)).obj M).op := by
  apply HomologicalComplex.Hom.isoOfComponents
    (fun n => ?_) (fun i j _ => by
      simp only [HomologicalComplex.single_obj_d, HomologicalComplex.op_d,
        op_zero, comp_zero, zero_comp])
  cases n with
  | zero => exact Iso.refl _
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
        (op M) (n + 1) (by simp)).iso
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
          M (n + 1) (by simp)).op

noncomputable def ordinaryProjectiveResolutionOpposite {M : ModuleCat.{v} R}
    (P : ProjectiveResolution M) : InjectiveResolution (op M) where
  cocomplex := P.complex.op
  injective n := by
    letI := P.projective n
    exact inferInstanceAs (Injective (op (P.complex.X n)))
  ι := (ordinarySingleZeroOppositeIso R M).hom ≫
    (HomologicalComplex.opFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ)).map P.π.op
  quasiIso := by infer_instance

noncomputable def ordinaryRingDualExtFunctor (n : ℕ) :
    (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{v} Rᵐᵒᵖ :=
  (ordinaryRingDualFunctor R).rightDerived n

noncomputable def ordinaryRingDualResolutionHomologyIso {M : ModuleCat.{v} R}
    (P : ProjectiveResolution M) (n : ℕ) :
    (ordinaryRingDualExtFunctor R n).obj (op M) ≅
      (((ordinaryRingDualFunctor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        P.complex.op).homology n :=
  (ordinaryProjectiveResolutionOpposite R P).isoRightDerivedObj (ordinaryRingDualFunctor R) n

theorem ordinaryRingDualExt_isZero_of_resolution_term {M : ModuleCat.{v} R}
    (P : ProjectiveResolution M) (n : ℕ) (hn : IsZero (P.complex.X n)) :
    IsZero ((ordinaryRingDualExtFunctor R n).obj (op M)) := by
  let K := ((ordinaryRingDualFunctor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    P.complex.op
  have hK : IsZero (K.homology n) :=
    (K.sc n).isZero_homology_of_isZero_X₂
      ((ordinaryRingDualFunctor R).map_isZero hn.op)
  exact IsZero.of_iso hK (ordinaryRingDualResolutionHomologyIso R P n)

theorem ordinaryRingDualExt_isZero_ge_four {M : ModuleCat.{v} R}
    (P : ProjectiveResolution M) (hP : ∀ n : ℕ, IsZero (P.complex.X (n + 4))) (n : ℕ) :
    IsZero ((ordinaryRingDualExtFunctor R (n + 4)).obj (op M)) :=
  ordinaryRingDualExt_isZero_of_resolution_term R P (n + 4) (hP n)

end ASGinzburg
