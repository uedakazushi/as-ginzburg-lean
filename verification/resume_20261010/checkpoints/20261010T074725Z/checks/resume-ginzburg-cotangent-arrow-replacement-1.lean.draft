import work.ASGinzburgDraft.GinzburgSubstitutedOccurrenceDifferential
import work.ASGinzburgDraft.GinzburgArrowSubstitution

/-! The actual cotangent lift on extended generators uses occurrences
in the genuine inverse ordinary automorphism. Its dual differential
compatibility is derived from the nonlinear inverse cyclic chain rule. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgCotangentDualImage
    (E : Q.VertexCutPathAutomorphism k) (a : Q.Arrow) :
    Q.GinzburgPathComponent k (Q.target a) (Q.source a) :=
  ∑ b : Q.Arrow,
    Q.ginzburgSubstitutedOccurrenceDerivative k E a (Q.source b) (Q.target b)
      (VertexCutPathAutomorphism.arrowReplacement Q k (E⁻¹) b)
      (Finsupp.single (Q.dualGinzburgArrowPath b) 1)

noncomputable def ginzburgCotangentArrowReplacement
    (E : Q.VertexCutPathAutomorphism k) : Q.GinzburgArrowReplacement k
  | .original a => Q.originalGinzburgLinearMap k (Q.source a) (Q.target a)
      (VertexCutPathAutomorphism.arrowReplacement Q k E a)
  | .dual a => Q.ginzburgCotangentDualImage k E a
  | .loop v => Finsupp.single (Q.ginzburgArrowPath (.loop v)) 1

theorem ginzburgCotangentArrowReplacement_original
    (E : Q.VertexCutPathAutomorphism k) (a : Q.Arrow) :
    Q.ginzburgCotangentArrowReplacement k E (.original a) =
      Q.originalGinzburgLinearMap k (Q.source a) (Q.target a)
        (VertexCutPathAutomorphism.arrowReplacement Q k E a) := rfl

theorem ginzburgCotangentDualImage_mem_cohomological
    (E : Q.VertexCutPathAutomorphism k) (a : Q.Arrow) :
    Q.ginzburgCotangentDualImage k E a ∈
      Q.ginzburgCohomologicalComponent k (Q.target a) (Q.source a) (-1) := by
  classical
  apply Submodule.sum_mem
  intro b _
  apply Q.ginzburgSubstitutedOccurrenceDerivative_mem_cohomological
  apply Finsupp.single_mem_supported
  simp [dualGinzburgArrowPath,GinzburgPath.cohomologicalDegree,
    GinzburgArrow.cohomologicalDegree]

theorem ginzburgCotangentArrowReplacement_mem_cohomological
    (E : Q.VertexCutPathAutomorphism k) (a : Q.GinzburgArrow) :
    Q.ginzburgCotangentArrowReplacement k E a ∈
      Q.ginzburgCohomologicalComponent k (a.source Q) (a.target Q)
        (a.cohomologicalDegree Q) := by
  cases a with
  | original a => exact Q.originalGinzburgLinearMap_degreeZero k _
  | dual a => exact Q.ginzburgCotangentDualImage_mem_cohomological k E a
  | loop v =>
    apply Finsupp.single_mem_supported
    simp [ginzburgArrowPath,GinzburgPath.cohomologicalDegree,
      GinzburgArrow.cohomologicalDegree]

theorem VertexCutPathAutomorphism.pathCyclicDerivative_inverse_chainRule
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) (a : Q.Arrow) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k E (Q.target a) (Q.source a)
      (Q.pathCyclicDerivative k a φ) =
      ∑ b : Q.Arrow,
        VertexCutPathAutomorphism.componentLinearEquiv Q k E (Q.target a) (Q.source a)
          (Q.pathOccurrenceDerivative k a (Q.source b) (Q.target b)
            (VertexCutPathAutomorphism.arrowReplacement Q k (E⁻¹) b)
            (VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹)
              (Q.target b) (Q.source b)
              (Q.pathCyclicDerivative k b
                (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ)))) := by
  have h := VertexCutPathAutomorphism.pathCyclicDerivative_chainRule Q k (E⁻¹)
    (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ) a
  have hi : VertexCutPathAutomorphism.potentialLinearEquiv Q k (E⁻¹)
      (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ) = φ :=
    (VertexCutPathAutomorphism.potentialLinearEquiv Q k E).symm_apply_apply φ
  rw [hi] at h
  simpa only [map_sum] using congrArg
    (VertexCutPathAutomorphism.componentLinearEquiv Q k E (Q.target a) (Q.source a)) h

theorem ginzburgCotangentDualImage_differential
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) (a : Q.Arrow) :
    Q.ginzburgDifferential k
      (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ)
      (Q.target a) (Q.source a) (Q.ginzburgCotangentDualImage k E a) =
      Q.originalGinzburgLinearMap k (Q.target a) (Q.source a)
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E (Q.target a) (Q.source a)
          (Q.pathCyclicDerivative k a φ)) := by
  classical
  rw [ginzburgCotangentDualImage,map_sum,
    VertexCutPathAutomorphism.pathCyclicDerivative_inverse_chainRule,map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Q.ginzburgSubstitutedOccurrenceDerivative_differential,
    Q.ginzburgDifferential_dualArrow]
  simpa only [VertexCutPathAutomorphism.componentLinearEquiv_inv,
    LinearEquiv.apply_symm_apply] using
    Q.ginzburgSubstitutedOccurrenceDerivative_original k E a (Q.source b) (Q.target b)
      (VertexCutPathAutomorphism.arrowReplacement Q k (E⁻¹) b)
      (VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) (Q.target b) (Q.source b)
        (Q.pathCyclicDerivative k b
          (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ)))

end ASGinzburg.CutQuiver
