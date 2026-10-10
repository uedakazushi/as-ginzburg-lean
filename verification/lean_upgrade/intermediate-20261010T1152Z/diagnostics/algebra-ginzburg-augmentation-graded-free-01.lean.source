import ASGinzburg.GinzburgLastGeneratorGradings
import ASGinzburg.GinzburgAugmentationIdeal
import ASGinzburg.GinzburgCutCochainComplex
import Mathlib.LinearAlgebra.Pi

/-! Genuine homogeneous augmentation components are free finite sums
of the actual Ginzburg components with the actual generator shifts. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

def GinzburgLastGeneratorData.degreeSigmaEquiv (u v : Q.Vertex) (q c : ℤ) :
    {d : Q.GinzburgLastGeneratorData u v //
      d.2.cohomologicalDegree=q-d.1.val.cohomologicalDegree Q ∧
      d.2.cutDegree=c-d.1.val.cutDegree Q} ≃
    Σ a : {a : Q.GinzburgArrow // a.target Q=v},
      {p : Q.GinzburgPath u (a.val.source Q) //
        p.cohomologicalDegree=q-a.val.cohomologicalDegree Q ∧
        p.cutDegree=c-a.val.cutDegree Q} where
  toFun d := ⟨d.val.1,⟨d.val.2,d.property⟩⟩
  invFun d := ⟨⟨d.1,d.2.val⟩,d.2.property⟩
  left_inv := by intro d; rfl
  right_inv := by intro d; rfl

universe u
variable (k : Type u) [Field k]

def ginzburgAugmentationAtDegree (u v : Q.Vertex) (q c : ℤ) :
    Submodule k (Q.GinzburgPathComponent k u v) :=
  Finsupp.supported k k {p | 0<p.length ∧ p.cohomologicalDegree=q ∧ p.cutDegree=c}

noncomputable def ginzburgCutComponentBasisEquiv (u v : Q.Vertex) (q c : ℤ) :
    Q.ginzburgCutCohomologicalComponent k u v q c ≃ₗ[k]
      ({p : Q.GinzburgPath u v // p.cohomologicalDegree=q ∧ p.cutDegree=c} →₀ k) :=
  (LinearEquiv.ofEq _ _ (show Q.ginzburgCutCohomologicalComponent k u v q c=
    Finsupp.supported k k {p | p.cohomologicalDegree=q ∧ p.cutDegree=c} by
      unfold ginzburgCutCohomologicalComponent ginzburgCohomologicalComponent ginzburgCutComponent
      rw [←Finsupp.supported_inter]
      rfl)).trans (Finsupp.supportedEquivFinsupp (M:=k) (R:=k) _)

noncomputable def ginzburgAugmentationGradedFreeEquiv (u v : Q.Vertex) (q c : ℤ) :
    Q.ginzburgAugmentationAtDegree k u v q c ≃ₗ[k]
      (Π a : {a : Q.GinzburgArrow // a.target Q=v},
        Q.ginzburgCutCohomologicalComponent k u (a.val.source Q)
          (q-a.val.cohomologicalDegree Q) (c-a.val.cutDegree Q)) := by
  classical
  letI := Fintype.ofFinite {a : Q.GinzburgArrow // a.target Q=v}
  exact (Finsupp.supportedEquivFinsupp (M:=k) (R:=k)
    {p : Q.GinzburgPath u v | 0<p.length ∧ p.cohomologicalDegree=q ∧ p.cutDegree=c}).trans
      ((Finsupp.domLCongr (GinzburgLastGeneratorData.atDegreeEquiv Q u v q c)).trans
        ((Finsupp.domLCongr (GinzburgLastGeneratorData.degreeSigmaEquiv Q u v q c)).trans
          ((Finsupp.sigmaFinsuppLEquivPiFinsupp k).trans
            (LinearEquiv.piCongrRight fun a =>
              (Q.ginzburgCutComponentBasisEquiv k u (a.val.source Q)
                (q-a.val.cohomologicalDegree Q) (c-a.val.cutDegree Q)).symm))))

theorem ginzburgAugmentationAtDegree_eq_cut_of_neg (u v : Q.Vertex) (q c : ℤ)
    (hq : q<0) : Q.ginzburgAugmentationAtDegree k u v q c=
      Q.ginzburgCutCohomologicalComponent k u v q c := by
  unfold ginzburgAugmentationAtDegree ginzburgCutCohomologicalComponent
    ginzburgCohomologicalComponent ginzburgCutComponent
  rw [←Finsupp.supported_inter]
  congr 1
  ext p
  change (0<p.length ∧ p.cohomologicalDegree=q ∧ p.cutDegree=c) ↔
    p.cohomologicalDegree=q ∧ p.cutDegree=c
  constructor
  · exact fun h => h.2
  · intro hp
    refine ⟨?_,hp⟩
    cases p with
    | nil => simp [GinzburgPath.cohomologicalDegree] at hp; omega
    | snoc p a h => simp [GinzburgPath.length]

end ASGinzburg.CutQuiver
