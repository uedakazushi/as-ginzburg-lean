import ASGinzburg.TotalAlgebraLocalUnits

/-! Componentwise linear maps respecting the original product extend to
non-unital algebra homomorphisms from the actual total algebra. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped DirectSum
universe u v w
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
variable {B : Type w} [NonUnitalRing B] [Module k B]

noncomputable instance totalAlgebraAddZeroClass : AddZeroClass A.totalAlgebra :=
  A.totalAlgebraAddCommMonoid.toAddZeroClass

/-- Extend componentwise linear maps to the genuine finite-support total algebra. -/
noncomputable def totalAlgebraLiftLinear (F : ∀ i j, A.Hom i j →ₗ[k] B) :
    A.totalAlgebra →ₗ[k] B :=
  (DFinsupp.lsum k (fun p : ℤ × ℤ => F p.1 p.2)).comp A.totalAlgebraEquiv.symm.toLinearMap

@[simp] theorem totalAlgebraLiftLinear_component (F : ∀ i j, A.Hom i j →ₗ[k] B)
    {i j : ℤ} (a : A.Hom i j) :
    A.totalAlgebraLiftLinear F (A.totalAlgebraComponent a) = F i j a := by
  change DFinsupp.lsum k _ (A.totalAlgebraEquiv.symm
    (A.totalAlgebraEquiv (DFinsupp.single (i,j) a))) = _
  rw [LinearEquiv.symm_apply_apply, DFinsupp.lsum_single]

/-- Connected multiplication and zero off the connecting index suffice; there is
no additional relation or assumed conclusion about AS regularity. -/
theorem totalAlgebraLiftLinear_mul (F : ∀ i j, A.Hom i j →ₗ[k] B)
    (hcomp : ∀ i j l (a : A.Hom i j) (b : A.Hom j l),
      F i l (A.comp b a) = F j l b * F i j a)
    (hoff : ∀ i j p q (a : A.Hom i j) (b : A.Hom p q),
      j ≠ p → F p q b * F i j a = 0) (x y : A.totalAlgebra) :
    A.totalAlgebraLiftLinear F (x * y) =
      A.totalAlgebraLiftLinear F x * A.totalAlgebraLiftLinear F y := by
  obtain ⟨x,rfl⟩ := A.totalAlgebraEquiv.surjective x
  obtain ⟨y,rfl⟩ := A.totalAlgebraEquiv.surjective y
  induction x using DFinsupp.induction with
  | h0 => simp
  | ha p a x _ _ ih =>
    rw [map_add, add_mul, map_add, map_add, add_mul, ih]
    congr 1
    clear ih
    induction y using DFinsupp.induction with
    | h0 => simp
    | ha q b y _ _ ih =>
      rw [map_add, mul_add, map_add, map_add, mul_add, ih]
      congr 1
      rcases p with ⟨i,j⟩
      rcases q with ⟨l,m⟩
      change A.totalAlgebraLiftLinear F
        (A.totalAlgebraComponent a * A.totalAlgebraComponent b) =
          A.totalAlgebraLiftLinear F (A.totalAlgebraComponent a) *
            A.totalAlgebraLiftLinear F (A.totalAlgebraComponent b)
      by_cases h : m = i
      · subst m
        rw [A.totalAlgebraComponent_mul, A.totalAlgebraLiftLinear_component,
          A.totalAlgebraLiftLinear_component, A.totalAlgebraLiftLinear_component]
        exact hcomp l i j b a
      · rw [A.totalAlgebraComponent_mul_off b a h, map_zero,
          A.totalAlgebraLiftLinear_component, A.totalAlgebraLiftLinear_component]
        exact (hoff l m i j b a h).symm

noncomputable def totalAlgebraLift (F : ∀ i j, A.Hom i j →ₗ[k] B)
    (hcomp : ∀ i j l (a : A.Hom i j) (b : A.Hom j l),
      F i l (A.comp b a) = F j l b * F i j a)
    (hoff : ∀ i j p q (a : A.Hom i j) (b : A.Hom p q),
      j ≠ p → F p q b * F i j a = 0) : A.totalAlgebra →ₙₐ[k] B where
  toFun := A.totalAlgebraLiftLinear F
  map_zero' := (A.totalAlgebraLiftLinear F).map_zero
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' := A.totalAlgebraLiftLinear_mul F hcomp hoff

end ASGinzburg.ZAlgebra
