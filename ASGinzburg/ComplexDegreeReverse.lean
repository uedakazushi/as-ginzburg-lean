import Mathlib.Algebra.Homology.HomotopyCategory
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable (C : Type u) [Category.{v} C] [Preadditive C]

def reverseCochainComplex (X : CochainComplex C ℤ) : ChainComplex C ℤ where
  X i := X.X (-i)
  d i j := X.d (-i) (-j)
  shape i j hij := X.shape _ _ (by
    change ¬ (j + 1 = i) at hij
    change ¬ (-i + 1 = -j)
    omega)

def reverseChainComplex (X : ChainComplex C ℤ) : CochainComplex C ℤ where
  X i := X.X (-i)
  d i j := X.d (-i) (-j)
  shape i j hij := X.shape _ _ (by
    change ¬ (i + 1 = j) at hij
    change ¬ (-j + 1 = -i)
    omega)

def reverseCochainFunctor : CochainComplex C ℤ ⥤ ChainComplex C ℤ where
  obj := reverseCochainComplex C
  map f := { f := fun i => f.f (-i), comm' := fun i j _ => f.comm (-i) (-j) }

def reverseChainFunctor : ChainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := reverseChainComplex C
  map f := { f := fun i => f.f (-i), comm' := fun i j _ => f.comm (-i) (-j) }

def reverseCochainUnitIso : 𝟭 (CochainComplex C ℤ) ≅ reverseCochainFunctor C ⋙ reverseChainFunctor C :=
  NatIso.ofComponents (fun X =>
    HomologicalComplex.Hom.isoOfComponents (fun i => (X.XIsoOfEq (neg_neg i)).symm)
      (by
        intro i j _
        change (X.XIsoOfEq (neg_neg i)).inv ≫ X.d (-(-i)) (-(-j)) =
          X.d i j ≫ (X.XIsoOfEq (neg_neg j)).inv
        simp))
    (by
      intro X Y f
      ext i
      change f.f i ≫ (Y.XIsoOfEq (neg_neg i)).inv =
        (X.XIsoOfEq (neg_neg i)).inv ≫ f.f (-(-i))
      exact eqToHom_naturality f.f (neg_neg i).symm)

def reverseChainUnitIso : 𝟭 (ChainComplex C ℤ) ≅ reverseChainFunctor C ⋙ reverseCochainFunctor C :=
  NatIso.ofComponents (fun X =>
    HomologicalComplex.Hom.isoOfComponents (fun i => (X.XIsoOfEq (neg_neg i)).symm)
      (by
        intro i j _
        change (X.XIsoOfEq (neg_neg i)).inv ≫ X.d (-(-i)) (-(-j)) =
          X.d i j ≫ (X.XIsoOfEq (neg_neg j)).inv
        simp))
    (by
      intro X Y f
      ext i
      change f.f i ≫ (Y.XIsoOfEq (neg_neg i)).inv =
        (X.XIsoOfEq (neg_neg i)).inv ≫ f.f (-(-i))
      exact eqToHom_naturality f.f (neg_neg i).symm)

def reverseDegreeEquivalence : CochainComplex C ℤ ≌ ChainComplex C ℤ :=
  CategoryTheory.Equivalence.mk (reverseCochainFunctor C) (reverseChainFunctor C)
    (reverseCochainUnitIso C) (reverseChainUnitIso C).symm
end ASGinzburg
