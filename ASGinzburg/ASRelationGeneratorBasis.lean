import ASGinzburg.ASSecondSyzygyTops
import ASGinzburg.FiniteRepresentableTopBasis
import ASGinzburg.FoundationSurvivingArrows

/-! The genuine second syzygy has the degree-two arrow-indexed top
basis prescribed by the AS sequence. On sheet zero its indices are
exactly the reverse cut arrows, without assuming a relation count. -/
namespace ASGinzburg.ZAlgebra.ASResolution
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}

noncomputable def secondSyzygyTopBasis {w : Q.LiftVertex} (R : A.ASResolution Q w) (i : ℤ) :
    Module.Basis {a : Q.outgoingArrows (Q.tau.symm w) //
      Q.height (Q.outgoingTarget (Q.tau.symm w) a)=i} k
      ((A.rightModuleEvaluation i).obj (kernel R.firstCover) ⧸
        A.positiveActionSpan (kernel R.firstCover) i) := by
  classical
  exact (A.finiteRepresentableTopBasis
    (fun a : Q.outgoingArrows (Q.tau.symm w) =>
      Q.height (Q.outgoingTarget (Q.tau.symm w) a)) i).map (R.secondSyzygyTopEquiv i)

noncomputable def foundationRelationTopBasis (i j : Q.Vertex)
    (R : A.ASResolution Q (j,0)) :
    Module.Basis (Q.FoundationRelationArrow i j) k
      ((A.rightModuleEvaluation (i.val : ℤ)).obj (kernel R.firstCover) ⧸
        A.positiveActionSpan (kernel R.firstCover) (i.val : ℤ)) :=
  (R.secondSyzygyTopBasis (i.val : ℤ)).reindex (Q.foundationRelationIndexEquiv i j)

theorem foundationRelationTop_finrank (i j : Q.Vertex)
    (R : A.ASResolution Q (j,0)) :
    Module.finrank k
      ((A.rightModuleEvaluation (i.val : ℤ)).obj (kernel R.firstCover) ⧸
        A.positiveActionSpan (kernel R.firstCover) (i.val : ℤ))=
      Fintype.card (Q.FoundationRelationArrow i j) := by
  classical
  exact Module.finrank_eq_card_basis (R.foundationRelationTopBasis i j)

end ASGinzburg.ZAlgebra.ASResolution
