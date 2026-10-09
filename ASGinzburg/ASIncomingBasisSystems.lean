import ASGinzburg.IndecomposableBasisLifts

/-! Actual arbitrary arrow bases of the indecomposable components
have concrete incoming-element lifts. AS regularity supplies such bases. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

structure IncomingBasisSystem where
  basis : ∀ (w : Q.LiftVertex) (i : ℤ), i<Q.height w →
    Module.Basis (ASResolution.GeneratorIndex (Q := Q) (w := w) i) k
      (A.Hom i (Q.height w) ⧸ Submodule.span k (A.products i (Q.height w)))

namespace IncomingBasisSystem
variable {A Q} (B : A.IncomingBasisSystem Q)

noncomputable def incomingElement (w : Q.LiftVertex) (a : Q.incomingArrows w) :
    A.Hom (Q.height (Q.incomingSource w a)) (Q.height w) :=
  A.indecomposableBasisLift _ _
    (B.basis w (Q.height (Q.incomingSource w a)) (Q.incomingSource_height_lt w a)) ⟨a,rfl⟩

noncomputable def incomingGenerator (w : Q.LiftVertex) (i : ℤ)
    (a : ASResolution.GeneratorIndex (Q := Q) (w := w) i) : A.Hom i (Q.height w) :=
  A.homTransport _ _ i (Q.height w) a.property rfl (B.incomingElement w a.val)

theorem incomingGenerator_eq_basisLift (w : Q.LiftVertex) (i : ℤ) (hi : i<Q.height w)
    (a : ASResolution.GeneratorIndex (Q := Q) (w := w) i) :
    B.incomingGenerator w i a=A.indecomposableBasisLift i (Q.height w) (B.basis w i hi) a := by
  rcases a with ⟨a,ha⟩
  subst i
  rfl

theorem incomingGenerator_class (w : Q.LiftVertex) (i : ℤ) (hi : i<Q.height w)
    (a : ASResolution.GeneratorIndex (Q := Q) (w := w) i) :
    (Submodule.span k (A.products i (Q.height w))).mkQ (B.incomingGenerator w i a)=
      B.basis w i hi a := by
  rw [B.incomingGenerator_eq_basisLift w i hi]
  exact A.indecomposableBasisLift_mkQ i (Q.height w) (B.basis w i hi) a

theorem incomingGenerator_decomposition (w : Q.LiftVertex) (i : ℤ) (hi : i<Q.height w) :
    Submodule.span k (Set.range (B.incomingGenerator w i)) ⊔
      Submodule.span k (A.products i (Q.height w))=⊤ := by
  have hf : B.incomingGenerator w i=A.indecomposableBasisLift i (Q.height w) (B.basis w i hi) :=
    funext (B.incomingGenerator_eq_basisLift w i hi)
  rw [hf]
  exact A.indecomposableBasisLift_decomposition i (Q.height w) (B.basis w i hi)

end IncomingBasisSystem

noncomputable def ASRegular.incomingBasisSystem (h : A.ASRegular Q) :
    A.IncomingBasisSystem Q where
  basis w i hi := (h.resolution A Q w).indecomposableGeneratorBasis i hi

theorem ASRegular.exists_incomingBasisSystem (h : A.ASRegular Q) :
    Nonempty (A.IncomingBasisSystem Q) := ⟨h.incomingBasisSystem A Q⟩

end ASGinzburg.ZAlgebra
