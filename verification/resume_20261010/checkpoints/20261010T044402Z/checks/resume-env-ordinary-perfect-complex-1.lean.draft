import work.ASGinzburgDraft.OrdinaryModuleFiniteFreeRetract
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Single

/-! Perfect ordinary module complexes are bounded cochain complexes of
actual finitely generated projective modules. Each term is specified by
genuine splitting maps exhibiting a retract of a finite free module. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe v
variable (R : Type v) [Ring R]

def ordinaryFiniteProjectiveCochainProperty (K : CochainComplex (ModuleCat.{v} R) ℤ) : Prop :=
  (∀ i : ℤ, ordinaryFiniteProjectiveProperty R (K.X i)) ∧
  ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)

/-- A module is perfect when an actual bounded complex of finitely
generated projective modules augments to it by a quasi-isomorphism. -/
def ordinaryPerfectModuleProperty (X : ModuleCat.{v} R) : Prop :=
  ∃ K : CochainComplex (ModuleCat.{v} R) ℤ, ordinaryFiniteProjectiveCochainProperty R K ∧
    ∃ f : K ⟶ (HomologicalComplex.single (ModuleCat R) (ComplexShape.up ℤ) 0).obj X,
      QuasiIso f

theorem ordinaryFiniteProjectiveCochainProperty_term_finite
    {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (hK : ordinaryFiniteProjectiveCochainProperty R K) (i : ℤ) :
    Module.Finite R (K.X i) :=
  ((ordinaryFiniteProjectiveProperty_iff R (K.X i)).mp (hK.1 i)).1

theorem ordinaryFiniteProjectiveCochainProperty_term_projective
    {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (hK : ordinaryFiniteProjectiveCochainProperty R K) (i : ℤ) :
    Projective (K.X i) :=
  ((ordinaryFiniteProjectiveProperty_iff R (K.X i)).mp (hK.1 i)).2

end ASGinzburg
