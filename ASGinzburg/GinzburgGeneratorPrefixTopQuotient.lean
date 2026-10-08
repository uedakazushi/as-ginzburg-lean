import ASGinzburg.GinzburgGeneratorPrefixHomology
import ASGinzburg.GinzburgCutHomologyZero

/-! The actual top prefix homology is the quotient by the actual signed
incoming differential, before any comparison with algebra coefficients. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgGeneratorPrefixDifferential_top_zero (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) :
    Q.ginzburgGeneratorPrefixDifferential k φ u v r r c=0 := by
  apply LinearMap.ext
  intro f
  funext a
  apply Subtype.ext
  change ginzburgSign k r • Q.ginzburgDifferential k φ u (a.val.source Q) (f a).val=0
  have hf : (f a).val ∈ Q.ginzburgCohomologicalComponent k u (a.val.source Q) 0 := by
    simpa only [sub_self] using (f a).property.1
  rw [Q.ginzburgDifferential_degreeZero k φ hf,smul_zero]

noncomputable def ginzburgGeneratorPrefixIncomingDifferential (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) :
    Q.GinzburgGeneratorPrefix k u v r (r-1) c →ₗ[k]
      Q.GinzburgGeneratorPrefix k u v r r c :=
  ((Q.ginzburgGeneratorPrefixComplex k φ u v r c).d (r-1) r).hom

noncomputable def ginzburgGeneratorPrefixTopShortComplex (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) : ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.moduleCatMk (Q.ginzburgGeneratorPrefixIncomingDifferential k φ u v r c)
    (Q.ginzburgGeneratorPrefixDifferential k φ u v r r c)
    (by rw [Q.ginzburgGeneratorPrefixDifferential_top_zero,LinearMap.zero_comp])

theorem ginzburgGeneratorPrefixTopShortComplex_g (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) :
    (Q.ginzburgGeneratorPrefixTopShortComplex k φ u v r c).g=0 := by
  apply ModuleCat.hom_ext
  exact Q.ginzburgGeneratorPrefixDifferential_top_zero k φ u v r c

noncomputable def ginzburgGeneratorPrefixTopShortComplexIso (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) :
    (Q.ginzburgGeneratorPrefixComplex k φ u v r c).sc' (r-1) r (r+1) ≅
      Q.ginzburgGeneratorPrefixTopShortComplex k φ u v r c :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by rfl)
    (by simpa only [Category.id_comp,Category.comp_id] using
      (Q.ginzburgGeneratorPrefixComplex_d k φ u v r c r).symm)

noncomputable def ginzburgGeneratorPrefixTopHomologyQuotientIso (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) :
    Q.ginzburgGeneratorPrefixHomology k φ u v r c r ≅
      ModuleCat.of k (Q.GinzburgGeneratorPrefix k u v r r c ⧸
        LinearMap.range (Q.ginzburgGeneratorPrefixIncomingDifferential k φ u v r c)) :=
  ShortComplex.homologyMapIso ((Q.ginzburgGeneratorPrefixComplex k φ u v r c).isoSc'
    (i:=r-1) (j:=r) (k:=r+1) (by simp) (by simp)) ≪≫
  ShortComplex.homologyMapIso (Q.ginzburgGeneratorPrefixTopShortComplexIso k φ u v r c) ≪≫
  (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
    (Q.ginzburgGeneratorPrefixTopShortComplex k φ u v r c)
      (Q.ginzburgGeneratorPrefixTopShortComplex_g k φ u v r c)
      (ModuleCat.cokernelCocone (Q.ginzburgGeneratorPrefixTopShortComplex k φ u v r c).f)
      (ModuleCat.cokernelIsColimit (Q.ginzburgGeneratorPrefixTopShortComplex k φ u v r c).f)).homologyIso

end ASGinzburg.CutQuiver
