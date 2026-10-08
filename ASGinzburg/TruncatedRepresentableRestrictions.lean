import ASGinzburg.TruncatedRepresentableHom
import ASGinzburg.FiniteWindowProjectives

/-!
# Canonical epimorphisms on changing the lower interval endpoint
-/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def rightTruncatedRepresentableRestriction (l' l i : ℤ) (hl : l' ≤ l) :
    A.rightTruncatedRepresentable l' i ⟶ A.rightTruncatedRepresentable l i :=
  A.rightTruncatedRepresentableDesc l' i (A.rightTruncatedRepresentable l i)
    (fun j hj => A.rightTruncatedRepresentable_below l i j (lt_of_lt_of_le hj hl))
    (A.rightTruncatedRepresentableπ l i)

@[reassoc] theorem rightTruncatedRepresentableπ_restriction (l' l i : ℤ) (hl : l' ≤ l) :
    A.rightTruncatedRepresentableπ l' i ≫ A.rightTruncatedRepresentableRestriction l' l i hl =
      A.rightTruncatedRepresentableπ l i := A.rightTruncatedRepresentableπ_desc _ _ _ _ _

instance rightTruncatedRepresentableRestrictionEpi (l' l i : ℤ) (hl : l' ≤ l) :
    Epi (A.rightTruncatedRepresentableRestriction l' l i hl) :=
  epi_of_epi_fac (A.rightTruncatedRepresentableπ_restriction l' l i hl)

@[reassoc] theorem rightTruncatedRepresentableRestriction_cover (l' l i : ℤ) (hl : l' ≤ l)
    (hli : l ≤ i) :
    A.rightTruncatedRepresentableRestriction l' l i hl ≫ A.rightTruncatedRepresentableSimpleCover l i hli =
      A.rightTruncatedRepresentableSimpleCover l' i (hl.trans hli) := by
  apply (cancel_epi (A.rightTruncatedRepresentableπ l' i)).mp
  rw [← Category.assoc,A.rightTruncatedRepresentableπ_restriction,
    A.rightTruncatedRepresentableπ_simpleCover,A.rightTruncatedRepresentableπ_simpleCover]

@[reassoc] theorem rightTruncatedRepresentableRestriction_hom (l' l i j : ℤ) (hl : l' ≤ l)
    (hli : l ≤ i) (x : A.Hom i j) :
    A.rightTruncatedRepresentableHomComponentEquiv l' i j (hl.trans hli) x ≫
        A.rightTruncatedRepresentableRestriction l' l j hl =
      A.rightTruncatedRepresentableRestriction l' l i hl ≫
        A.rightTruncatedRepresentableHomComponentEquiv l i j hli x := by
  apply (cancel_epi (A.rightTruncatedRepresentableπ l' i)).mp
  rw [← Category.assoc,A.rightTruncatedRepresentableHomComponentEquiv_π,Category.assoc,
    A.rightTruncatedRepresentableπ_restriction,← Category.assoc,
    A.rightTruncatedRepresentableπ_restriction,A.rightTruncatedRepresentableHomComponentEquiv_π]
end ASGinzburg.ZAlgebra
