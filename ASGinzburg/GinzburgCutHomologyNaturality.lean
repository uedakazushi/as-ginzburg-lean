import ASGinzburg.GinzburgCutLeftAction
import ASGinzburg.ModuleCatCokernelHomologyNaturality

/-! Naturality of genuine cut H-zero and its genuine boundary quotient. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgCutZeroShortComplexLeftMap (φ : Q.Potential k)
    {x y v : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgCutZeroShortComplex k φ y.1 v.1 (v.2-y.2) ⟶
      Q.ginzburgCutZeroShortComplex k φ x.1 v.1 (v.2-x.2) :=
  ShortComplex.homMk (ModuleCat.ofHom (Q.ginzburgCutLeftTerm k (-1) f))
    (ModuleCat.ofHom (Q.ginzburgCutLeftTerm k 0 f))
    (ModuleCat.ofHom (Q.ginzburgCutLeftTerm k 1 f))
    (by apply ModuleCat.hom_ext; exact Q.ginzburgCutLeftTerm_differential k φ (-1) f)
    (by apply ModuleCat.hom_ext; exact Q.ginzburgCutLeftTerm_differential k φ 0 f)

theorem ginzburgCutZeroShortComplexIso_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    (HomologicalComplex.shortComplexFunctor' (ModuleCat k) (ComplexShape.up ℤ)
      (-1) 0 1).map (Q.ginzburgCutLeftCochainMap k φ (v:=v) f) ≫
        (Q.ginzburgCutZeroShortComplexIso k φ x.1 v.1 (v.2-x.2)).hom=
      (Q.ginzburgCutZeroShortComplexIso k φ y.1 v.1 (v.2-y.2)).hom ≫
        Q.ginzburgCutZeroShortComplexLeftMap k φ (v:=v) f := by
  ext <;> simp [ginzburgCutZeroShortComplexIso,ginzburgCutZeroShortComplexLeftMap,
    ginzburgCutLeftCochainMap]

theorem ginzburgCutCanonicalShortComplexIso_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    (HomologicalComplex.shortComplexFunctor (ModuleCat k) (ComplexShape.up ℤ) 0).map
        (Q.ginzburgCutLeftCochainMap k φ (v:=v) f) ≫
        ((Q.ginzburgCutCochainComplex k φ x.1 v.1 (v.2-x.2)).isoSc'
          (i:=(-1)) (j:=0) (k:=1) (by simp) (by simp) ≪≫
          Q.ginzburgCutZeroShortComplexIso k φ x.1 v.1 (v.2-x.2)).hom=
      ((Q.ginzburgCutCochainComplex k φ y.1 v.1 (v.2-y.2)).isoSc'
        (i:=(-1)) (j:=0) (k:=1) (by simp) (by simp) ≪≫
        Q.ginzburgCutZeroShortComplexIso k φ y.1 v.1 (v.2-y.2)).hom ≫
          Q.ginzburgCutZeroShortComplexLeftMap k φ (v:=v) f := by
  have he : (HomologicalComplex.shortComplexFunctor (ModuleCat k) (ComplexShape.up ℤ) 0).map
        (Q.ginzburgCutLeftCochainMap k φ (v:=v) f) ≫
        ((Q.ginzburgCutCochainComplex k φ x.1 v.1 (v.2-x.2)).isoSc'
          (i:=(-1)) (j:=0) (k:=1) (by simp) (by simp)).hom=
      ((Q.ginzburgCutCochainComplex k φ y.1 v.1 (v.2-y.2)).isoSc'
        (i:=(-1)) (j:=0) (k:=1) (by simp) (by simp)).hom ≫
      (HomologicalComplex.shortComplexFunctor' (ModuleCat k) (ComplexShape.up ℤ)
        (-1) 0 1).map (Q.ginzburgCutLeftCochainMap k φ (v:=v) f) :=
    (HomologicalComplex.natIsoSc' (ModuleCat k) (ComplexShape.up ℤ)
      (-1) 0 1 (by simp) (by simp)).hom.naturality
        (Q.ginzburgCutLeftCochainMap k φ (v:=v) f)
  simp only [Iso.trans_hom]
  rw [← Category.assoc,he,Category.assoc,
    Q.ginzburgCutZeroShortComplexIso_left_naturality,← Category.assoc]

theorem ginzburgCutHomologyZeroQuotientIso_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgCutLeftHomology k φ (v:=v) 0 f ≫
        (Q.ginzburgCutHomologyZeroQuotientIso k φ x.1 v.1 (v.2-x.2)).hom=
      (Q.ginzburgCutHomologyZeroQuotientIso k φ y.1 v.1 (v.2-y.2)).hom ≫
        moduleCatShortComplexQuotientMap (Q.ginzburgCutZeroShortComplexLeftMap k φ (v:=v) f) := by
  have he := congrArg (ShortComplex.homologyFunctor (ModuleCat k)).map
    (Q.ginzburgCutCanonicalShortComplexIso_left_naturality k φ (v:=v) f)
  simp only [ShortComplex.homologyFunctor,Functor.map_comp,Iso.trans_hom,
    ShortComplex.homologyMap_comp] at he
  have he' := congrArg (fun g => g ≫
    (moduleCatCokernelHomologyIso _
      (Q.ginzburgCutZeroShortComplex_g k φ x.1 v.1 (v.2-x.2))).hom) he
  dsimp only at he'
  rw [Category.assoc _ (ShortComplex.homologyMap
    (Q.ginzburgCutZeroShortComplexLeftMap k φ (v:=v) f)),
    moduleCatCokernelHomologyIso_naturality] at he'
  simpa only [ginzburgCutHomologyZeroQuotientIso,ShortComplex.homologyMapIso,
    Iso.trans_hom,moduleCatCokernelHomologyIso,ginzburgCutLeftHomology,
    HomologicalComplex.homologyMap,Category.assoc] using he'

end ASGinzburg.CutQuiver
