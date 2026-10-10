import ASGinzburg.ASRegularIsomorphismInvariance

/-! Genuine vertex-fixing isomorphism classes of the original AS algebras.
No periodicity or chosen presentation is part of the objects. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k] (Q : CutQuiver)

abbrev ASRegularAlgebra := {A : ZAlgebra.{u,v} k // A.ASRegular Q}

noncomputable def asRegularIsomorphismSetoid : Setoid (ASRegularAlgebra.{u,v} k Q) where
  r A B := Nonempty (ZAlgebra.Isomorphism A.val B.val)
  iseqv :=
    { refl := fun A => ⟨ZAlgebra.Isomorphism.refl A.val⟩
      symm := fun ⟨E⟩ => ⟨E.symm⟩
      trans := fun ⟨E⟩ ⟨F⟩ => ⟨E.trans F⟩ }

noncomputable abbrev ASRegularIsomorphismClass :=
  Quotient (asRegularIsomorphismSetoid.{u,v} k Q)

noncomputable def ASRegularAlgebra.isomorphismClass
    (A : ASRegularAlgebra.{u,v} k Q) : ASRegularIsomorphismClass.{u,v} k Q :=
  Quotient.mk (asRegularIsomorphismSetoid k Q) A

theorem ASRegularAlgebra.isomorphismClass_eq_iff
    (A B : ASRegularAlgebra.{u,v} k Q) :
    A.isomorphismClass k Q = B.isomorphismClass k Q ↔
      Nonempty (ZAlgebra.Isomorphism A.val B.val) :=
  Quotient.eq

theorem ASRegularAlgebra.isomorphismClass_eq_of_isomorphism
    (A B : ASRegularAlgebra.{u,v} k Q) (E : ZAlgebra.Isomorphism A.val B.val) :
    A.isomorphismClass k Q = B.isomorphismClass k Q :=
  Quotient.sound ⟨E⟩

end ASGinzburg
