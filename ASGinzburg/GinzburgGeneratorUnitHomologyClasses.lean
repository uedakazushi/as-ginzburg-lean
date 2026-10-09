import ASGinzburg.GinzburgPrefixFamilyUnits
import ASGinzburg.GinzburgLayerHomologyClasses

/-! Concrete prefix unit cycles give the genuine identity basis vectors
of the existing finite representable coproduct, through actual layer homology. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgGeneratorPrefix_top_cycle (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) (f : Q.GinzburgGeneratorPrefix k u v r r c) :
    (Q.ginzburgGeneratorPrefixComplex k φ u v r c).d r (r+1) f=0 := by
  rw [Q.ginzburgGeneratorPrefixComplex_d]
  change Q.ginzburgGeneratorPrefixDifferential k φ u v r r c f=0
  rw [Q.ginzburgGeneratorPrefixDifferential_top_zero,LinearMap.zero_apply]

noncomputable def ginzburgGeneratorUnitLayer (φ : Q.Potential k)
    (v : Q.LiftVertex) (r : ℤ) (a : Q.GinzburgIncomingDegree v.1 r) :
    Q.GinzburgAssociatedGraded k (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r r
      (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2) :=
  (Q.ginzburgGeneratorPrefixGradedIso k φ
    (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r
    (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2)).hom.f r
      (Pi.single a (Q.ginzburgGeneratorUnitPrefix k v r a))

theorem ginzburgGeneratorUnitLayer_cycle (φ : Q.Potential k)
    (v : Q.LiftVertex) (r : ℤ) (a : Q.GinzburgIncomingDegree v.1 r) :
    (Q.ginzburgAssociatedGradedComplex k φ
      (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r
      (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2)).d r (r+1)
        (Q.ginzburgGeneratorUnitLayer k φ v r a)=0 := by
  let e := Q.ginzburgGeneratorPrefixGradedIso k φ
    (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r
    (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2)
  have h := congrArg (fun f => f (Pi.single a (Q.ginzburgGeneratorUnitPrefix k v r a)))
    (e.hom.comm r (r+1))
  simpa only [ModuleCat.comp_apply,Q.ginzburgGeneratorPrefix_top_cycle,map_zero] using h

theorem ginzburgGeneratorUnitLayer_coefficients (φ : Q.Potential k)
    (v : Q.LiftVertex) (r : ℤ) (a : Q.GinzburgIncomingDegree v.1 r) :
    (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v r
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))
      ((Q.ginzburgLayerProjectiveComponentIso k φ
        (Q.ginzburgPrefixGeneratorEndpoint v a.val) v r).hom
        (moduleCochainHomologyClass
          (Q.ginzburgAssociatedGradedComplex k φ
            (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r
            (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2)) r
          (Q.ginzburgGeneratorUnitLayer k φ v r a)
          (Q.ginzburgGeneratorUnitLayer_cycle k φ v r a)))=
      Pi.single a ((Q.unrolledJacobianZAlgebra k φ).id
        (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))) := by
  rw [Q.ginzburgLayerProjectiveComponentIso_class]
  let e := Q.ginzburgGeneratorPrefixGradedIso k φ
    (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r
    (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2)
  have he : e.inv.f r (Q.ginzburgGeneratorUnitLayer k φ v r a)=
      Pi.single a (Q.ginzburgGeneratorUnitPrefix k v r a) :=
    congrArg (fun f => f (Pi.single a (Q.ginzburgGeneratorUnitPrefix k v r a)))
      ((HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℤ) r).mapIso e).hom_inv_id
  rw [he]
  exact Q.ginzburgPrefixTopFixedUnrolledEquiv_unit k φ v r a

end ASGinzburg.CutQuiver
