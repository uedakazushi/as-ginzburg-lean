import ASGinzburg.GinzburgPrefixLeftAction
import ASGinzburg.GinzburgGeneratorPrefixBoundaryFamily
import ASGinzburg.ModuleCatCokernelHomologyNaturality

/-! The actual top prefix short-complex maps and their genuine
cokernel homology presentation preserve degree-zero path multiplication. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgPrefixTopShortComplexLeftMap (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgGeneratorPrefixTopShortComplex k φ y.1 v.1 r (v.2-y.2) ⟶
      Q.ginzburgGeneratorPrefixTopShortComplex k φ x.1 v.1 r (v.2-x.2) :=
  ShortComplex.homMk (ModuleCat.ofHom (Q.ginzburgPrefixLeftTerm k r (r-1) f))
    (ModuleCat.ofHom (Q.ginzburgPrefixLeftTerm k r r f))
    (ModuleCat.ofHom (Q.ginzburgPrefixLeftTerm k r (r+1) f))
    ((Q.ginzburgPrefixLeftCochainMap k φ r f).comm (r-1) r)
    (by
      apply ModuleCat.hom_ext
      exact Q.ginzburgPrefixLeftTerm_differential k φ r r f)

theorem ginzburgPrefixTopShortComplexCokernel_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    ShortComplex.homologyMap (Q.ginzburgPrefixTopShortComplexLeftMap k φ (v:=v) r f) ≫
        (moduleCatCokernelHomologyIso _
          (Q.ginzburgGeneratorPrefixTopShortComplex_g k φ x.1 v.1 r (v.2-x.2))).hom=
      (moduleCatCokernelHomologyIso _
        (Q.ginzburgGeneratorPrefixTopShortComplex_g k φ y.1 v.1 r (v.2-y.2))).hom ≫
          moduleCatShortComplexQuotientMap (Q.ginzburgPrefixTopShortComplexLeftMap k φ (v:=v) r f) :=
  moduleCatCokernelHomologyIso_naturality _ _ _

end ASGinzburg.CutQuiver
