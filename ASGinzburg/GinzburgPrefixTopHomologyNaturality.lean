import ASGinzburg.GinzburgPrefixTopNaturality

/-! The actual prefix top homology and its actual incoming-boundary
quotient presentation commute with genuine degree-zero path multiplication. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgPrefixTopShortComplexIso_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    (HomologicalComplex.shortComplexFunctor' (ModuleCat k) (ComplexShape.up ℤ)
      (r-1) r (r+1)).map (Q.ginzburgPrefixLeftCochainMap k φ (v:=v) r f) ≫
        (Q.ginzburgGeneratorPrefixTopShortComplexIso k φ x.1 v.1 r (v.2-x.2)).hom=
      (Q.ginzburgGeneratorPrefixTopShortComplexIso k φ y.1 v.1 r (v.2-y.2)).hom ≫
        Q.ginzburgPrefixTopShortComplexLeftMap k φ (v:=v) r f := by
  ext <;> simp [ginzburgGeneratorPrefixTopShortComplexIso,ginzburgPrefixTopShortComplexLeftMap,
    ginzburgPrefixLeftCochainMap]

theorem ginzburgPrefixTopCanonicalShortComplexIso_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    (HomologicalComplex.shortComplexFunctor (ModuleCat k) (ComplexShape.up ℤ) r).map
        (Q.ginzburgPrefixLeftCochainMap k φ (v:=v) r f) ≫
        ((Q.ginzburgGeneratorPrefixComplex k φ x.1 v.1 r (v.2-x.2)).isoSc'
          (i:=r-1) (j:=r) (k:=r+1) (by simp) (by simp) ≪≫
          Q.ginzburgGeneratorPrefixTopShortComplexIso k φ x.1 v.1 r (v.2-x.2)).hom=
      ((Q.ginzburgGeneratorPrefixComplex k φ y.1 v.1 r (v.2-y.2)).isoSc'
        (i:=r-1) (j:=r) (k:=r+1) (by simp) (by simp) ≪≫
        Q.ginzburgGeneratorPrefixTopShortComplexIso k φ y.1 v.1 r (v.2-y.2)).hom ≫
          Q.ginzburgPrefixTopShortComplexLeftMap k φ (v:=v) r f := by
  have he : (HomologicalComplex.shortComplexFunctor (ModuleCat k) (ComplexShape.up ℤ) r).map
        (Q.ginzburgPrefixLeftCochainMap k φ (v:=v) r f) ≫
        ((Q.ginzburgGeneratorPrefixComplex k φ x.1 v.1 r (v.2-x.2)).isoSc'
          (i:=r-1) (j:=r) (k:=r+1) (by simp) (by simp)).hom=
      ((Q.ginzburgGeneratorPrefixComplex k φ y.1 v.1 r (v.2-y.2)).isoSc'
        (i:=r-1) (j:=r) (k:=r+1) (by simp) (by simp)).hom ≫
      (HomologicalComplex.shortComplexFunctor' (ModuleCat k) (ComplexShape.up ℤ)
        (r-1) r (r+1)).map (Q.ginzburgPrefixLeftCochainMap k φ (v:=v) r f) :=
    (HomologicalComplex.natIsoSc' (ModuleCat k) (ComplexShape.up ℤ)
      (r-1) r (r+1) (by simp) (by simp)).hom.naturality
        (Q.ginzburgPrefixLeftCochainMap k φ (v:=v) r f)
  simp only [Iso.trans_hom]
  rw [← Category.assoc,he,Category.assoc,
    Q.ginzburgPrefixTopShortComplexIso_left_naturality,← Category.assoc]

theorem ginzburgPrefixTopHomologyQuotientIso_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgPrefixLeftHomology k φ (v:=v) r r f ≫
        (Q.ginzburgGeneratorPrefixTopHomologyQuotientIso k φ x.1 v.1 r (v.2-x.2)).hom=
      (Q.ginzburgGeneratorPrefixTopHomologyQuotientIso k φ y.1 v.1 r (v.2-y.2)).hom ≫
        moduleCatShortComplexQuotientMap (Q.ginzburgPrefixTopShortComplexLeftMap k φ (v:=v) r f) := by
  have he := congrArg (ShortComplex.homologyFunctor (ModuleCat k)).map
    (Q.ginzburgPrefixTopCanonicalShortComplexIso_left_naturality k φ (v:=v) r f)
  simp only [ShortComplex.homologyFunctor,Functor.map_comp,Iso.trans_hom,
    ShortComplex.homologyMap_comp] at he
  have he' := congrArg (fun g => g ≫
    (moduleCatCokernelHomologyIso _
      (Q.ginzburgGeneratorPrefixTopShortComplex_g k φ x.1 v.1 r (v.2-x.2))).hom) he
  dsimp only at he'
  rw [Category.assoc _ (ShortComplex.homologyMap
    (Q.ginzburgPrefixTopShortComplexLeftMap k φ (v:=v) r f)),
    Q.ginzburgPrefixTopShortComplexCokernel_left_naturality] at he'
  simpa only [ginzburgGeneratorPrefixTopHomologyQuotientIso,ShortComplex.homologyMapIso,
    Iso.trans_hom,moduleCatCokernelHomologyIso,ginzburgPrefixLeftHomology,
    HomologicalComplex.homologyMap,Category.assoc] using he'

end ASGinzburg.CutQuiver
