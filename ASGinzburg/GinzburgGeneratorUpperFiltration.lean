import ASGinzburg.GinzburgGeneratorFiltrationSyzygy

/-! The upper filtered complex is its genuine degree-zero associated
graded complex, because the next filtration term is zero. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgGeneratorHigherLayer_zero (u v : Q.Vertex) (q c : ℤ) :
    Q.ginzburgGeneratorHigherLayer k u v 0 q c=⊥ := by
  apply bot_unique
  intro f hf
  change f.val ∈ Q.ginzburgGeneratorFiltrationAtDegree k u v (0+1) q c at hf
  rw [show (0:ℤ)+1=1 by norm_num,
    Q.ginzburgGeneratorFiltrationAtDegree_one,Submodule.mem_bot] at hf
  rw [Submodule.mem_bot]
  exact Subtype.ext hf

instance ginzburgFilteredToAssociatedGraded_zero_f_isIso (φ : Q.Potential k)
    (u v : Q.Vertex) (c q : ℤ) :
    IsIso ((Q.ginzburgFilteredToAssociatedGraded k φ u v 0 c).f q) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨?_,(Q.ginzburgGeneratorHigherLayer k u v 0 q c).mkQ_surjective⟩
  apply LinearMap.ker_eq_bot.mp
  change LinearMap.ker (Q.ginzburgGeneratorHigherLayer k u v 0 q c).mkQ=⊥
  rw [Submodule.ker_mkQ,Q.ginzburgGeneratorHigherLayer_zero]

instance ginzburgFilteredToAssociatedGraded_zero_isIso (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    IsIso (Q.ginzburgFilteredToAssociatedGraded k φ u v 0 c) :=
  HomologicalComplex.Hom.isIso_of_components _

noncomputable def ginzburgGeneratorFilteredZeroIso (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgGeneratorFilteredComplex k φ u v 0 c ≅
      Q.ginzburgAssociatedGradedComplex k φ u v 0 c :=
  asIso (Q.ginzburgFilteredToAssociatedGraded k φ u v 0 c)

noncomputable def ginzburgGeneratorFilteredZeroHomologyIso (φ : Q.Potential k)
    (u v : Q.Vertex) (c q : ℤ) :
    Q.ginzburgGeneratorFilteredHomology k φ u v 0 c q ≅
      Q.ginzburgAssociatedGradedHomology k φ u v 0 c q :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) q).mapIso
    (Q.ginzburgGeneratorFilteredZeroIso k φ u v c)

theorem GinzburgRegular.generatorFilteredZeroHomology_isZero {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (c q : ℤ) (hq : q≠0) :
    IsZero (Q.ginzburgGeneratorFilteredHomology k φ u v 0 c q) :=
  (h.associatedGradedHomology_isZero_of_ne Q k u v 0 c q hq).of_iso
    (Q.ginzburgGeneratorFilteredZeroHomologyIso k φ u v c q)

end ASGinzburg.CutQuiver
