import ASGinzburg.GinzburgUnitFilteredPrefix
import ASGinzburg.GinzburgUpperHomologyClasses

/-! The actual original-arrow unit representative is a filtered
cycle whose upper homology class is the genuine projective identity basis. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgOriginalFiltered_cycle (φ : Q.Potential k)
    (x v : Q.LiftVertex)
    (f : Q.ginzburgGeneratorFiltrationAtDegree k x.1 v.1 0 0 (v.2-x.2)) :
    (Q.ginzburgGeneratorFilteredComplex k φ x.1 v.1 0 (v.2-x.2)).d 0 1 f=0 := by
  have hd : (Q.ginzburgGeneratorFilteredComplex k φ x.1 v.1 0 (v.2-x.2)).d 0 1 =
      ModuleCat.ofHom (Q.ginzburgGeneratorFilteredDifferential k φ x.1 v.1 0 0
        (v.2-x.2)) := by
    simpa only [show (0:ℤ)+1=1 by norm_num] using
      Q.ginzburgGeneratorFilteredComplex_d k φ x.1 v.1 0 (v.2-x.2) 0
  rw [hd]
  apply Subtype.ext
  exact Q.ginzburgDifferential_degreeZero k φ
    ((Q.ginzburgGeneratorFiltrationAtDegree_eq_inf k x.1 v.1 0 0 (v.2-x.2)).le f.property).2.1

theorem ginzburgOriginalUnitProjectiveClass_coefficients (φ : Q.Potential k)
    (v : Q.LiftVertex) (a : Q.GinzburgIncomingDegree v.1 0) :
    (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v 0
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))
      ((Q.ginzburgUpperProjectiveComponentIso k φ
        (Q.ginzburgPrefixGeneratorEndpoint v a.val) v).hom
        (moduleCochainHomologyClass
          (Q.ginzburgGeneratorFilteredComplex k φ
            (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 0
            (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2)) 0
          (Q.ginzburgGeneratorUnitRepresentative k v 0 a)
          (Q.ginzburgOriginalFiltered_cycle k φ
            (Q.ginzburgPrefixGeneratorEndpoint v a.val) v _)))=
      Pi.single a ((Q.unrolledJacobianZAlgebra k φ).id
        (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))) := by
  rw [Q.ginzburgUpperProjectiveComponentIso_class]
  change Q.ginzburgPrefixTopFixedUnrolledEquiv k φ
    (Q.ginzburgPrefixGeneratorEndpoint v a.val) v 0
    (Submodule.Quotient.mk
      ((Q.ginzburgFilteredToPrefix k φ (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 0
        (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2)).f 0
          (Q.ginzburgGeneratorUnitRepresentative k v 0 a)))=_
  rw [Q.ginzburgFilteredToPrefix_unitRepresentative]
  exact Q.ginzburgPrefixTopFixedUnrolledEquiv_unit k φ v 0 a

end ASGinzburg.CutQuiver
