import work.ASGinzburgDraft.OrdinaryFiniteProjectiveRingBidual
import Mathlib.Algebra.Homology.Additive

/-! Canonical ring bidual evaluation is a genuine chain isomorphism
for every homological complex of actual finite projective modules. -/
namespace ASGinzburg
open CategoryTheory
universe v w
variable (R : Type v) [Ring R]

instance ordinaryRingBidualFunctorAdditive : (ordinaryRingBidualFunctor R).Additive where
  map_add := by
    intro P Q f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply LinearMap.ext
    intro a
    let h' : ordinaryRingDual R P →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ := h
    change h' (ordinaryRingDualMap R (f + g) a) =
      h' (ordinaryRingDualMap R f a) + h' (ordinaryRingDualMap R g a)
    rw [← h'.map_add]
    congr 1
    apply LinearMap.ext
    intro x
    exact a.map_add (f x) (g x)

variable {ι : Type w} {c : ComplexShape ι}

noncomputable def ordinaryFiniteProjectiveRingBidualComplexIso
    (K : HomologicalComplex (ModuleCat.{v} R) c)
    (hK : ∀ i, ordinaryFiniteProjectiveProperty R (K.X i)) :
    K ≅ ((ordinaryRingBidualFunctor R).mapHomologicalComplex c).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => ordinaryFiniteProjectiveRingBidualIso R (hK i)) (by
      intro i j _
      simpa only [ordinaryFiniteProjectiveRingBidualIso_hom] using
        (ordinaryRingBidualEvaluationNatTrans R).naturality (K.d i j))

@[simp] theorem ordinaryFiniteProjectiveRingBidualComplexIso_hom_f
    (K : HomologicalComplex (ModuleCat.{v} R) c)
    (hK : ∀ i, ordinaryFiniteProjectiveProperty R (K.X i)) (i : ι) :
    (ordinaryFiniteProjectiveRingBidualComplexIso R K hK).hom.f i =
      ordinaryRingBidualEvaluation R (K.X i) := rfl

@[simp] theorem ordinaryFiniteProjectiveRingBidualComplexIso_inv_f
    (K : HomologicalComplex (ModuleCat.{v} R) c)
    (hK : ∀ i, ordinaryFiniteProjectiveProperty R (K.X i)) (i : ι) :
    (ordinaryFiniteProjectiveRingBidualComplexIso R K hK).inv.f i =
      (ordinaryFiniteProjectiveRingBidualIso R (hK i)).inv := rfl

theorem ordinaryFiniteProjectiveRingBidualComplexIso_hom_naturality
    {K L : HomologicalComplex (ModuleCat.{v} R) c}
    (hK : ∀ i, ordinaryFiniteProjectiveProperty R (K.X i))
    (hL : ∀ i, ordinaryFiniteProjectiveProperty R (L.X i)) (f : K ⟶ L) :
    f ≫ (ordinaryFiniteProjectiveRingBidualComplexIso R L hL).hom =
      (ordinaryFiniteProjectiveRingBidualComplexIso R K hK).hom ≫
        ((ordinaryRingBidualFunctor R).mapHomologicalComplex c).map f := by
  apply HomologicalComplex.hom_ext
  intro i
  exact (ordinaryRingBidualEvaluationNatTrans R).naturality (f.f i)

end ASGinzburg
