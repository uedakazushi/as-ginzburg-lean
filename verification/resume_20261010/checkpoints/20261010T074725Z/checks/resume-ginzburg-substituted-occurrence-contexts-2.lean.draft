import ASGinzburg.PathAutomorphismJacobianChainRule
import ASGinzburg.GinzburgBoundaryProducts
import ASGinzburg.GinzburgDifferentialSign
import ASGinzburg.GinzburgSupportedProducts
import ASGinzburg.FiniteComponentAutomorphismProducts

/-! Genuine extended occurrence insertion. Ordinary before and after
contexts are sent through the actual free-path automorphism; the inserted
reversed-endpoint element is an arbitrary extended path polynomial. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem VertexCutPathAutomorphism.componentLinearEquiv_comp
    (E : Q.VertexCutPathAutomorphism k) {i j l : Q.Vertex}
    (f : Q.PathComponent k i j) (g : Q.PathComponent k j l) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k E i l (Q.pathComp k g f) =
      Q.pathComp k (VertexCutPathAutomorphism.componentLinearEquiv Q k E j l g)
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f) :=
  (Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_comp E.val
    (VertexCutPathAutomorphism.fixes_vertex Q k E) f g

noncomputable def ginzburgSubstitutedOccurrenceContextMap
    (E : Q.VertexCutPathAutomorphism k) {a : Q.Arrow} {i j : Q.Vertex}
    (C : Q.PathOccurrenceContext a i j) :
    Q.GinzburgPathComponent k j i →ₗ[k]
      Q.GinzburgPathComponent k (Q.target a) (Q.source a) :=
  (Q.ginzburgPathComp k (Q.originalGinzburgLinearMap k i (Q.source a)
    (VertexCutPathAutomorphism.componentLinearEquiv Q k E i (Q.source a)
      (Finsupp.single C.beforePath 1)))).comp
    ((Q.ginzburgPathComp k).flip (Q.originalGinzburgLinearMap k (Q.target a) j
      (VertexCutPathAutomorphism.componentLinearEquiv Q k E (Q.target a) j
        (Finsupp.single C.afterPath 1))))

theorem ginzburgSubstitutedOccurrenceContextMap_apply
    (E : Q.VertexCutPathAutomorphism k) {a : Q.Arrow} {i j : Q.Vertex}
    (C : Q.PathOccurrenceContext a i j) (h : Q.GinzburgPathComponent k j i) :
    Q.ginzburgSubstitutedOccurrenceContextMap k E C h =
      Q.ginzburgPathComp k (Q.originalGinzburgLinearMap k i (Q.source a)
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E i (Q.source a)
          (Finsupp.single C.beforePath 1)))
        (Q.ginzburgPathComp k h (Q.originalGinzburgLinearMap k (Q.target a) j
          (VertexCutPathAutomorphism.componentLinearEquiv Q k E (Q.target a) j
            (Finsupp.single C.afterPath 1)))) := rfl

noncomputable def ginzburgSubstitutedOccurrenceOperator
    (E : Q.VertexCutPathAutomorphism k) (a : Q.Arrow)
    {i j : Q.Vertex} (p : Q.Path i j) :
    Q.GinzburgPathComponent k j i →ₗ[k]
      Q.GinzburgPathComponent k (Q.target a) (Q.source a) :=
  ((p.occurrenceContexts Q a).map (Q.ginzburgSubstitutedOccurrenceContextMap k E)).sum

noncomputable def ginzburgSubstitutedOccurrenceDerivative
    (E : Q.VertexCutPathAutomorphism k) (a : Q.Arrow) (i j : Q.Vertex) :
    Q.PathComponent k i j →ₗ[k]
      (Q.GinzburgPathComponent k j i →ₗ[k]
        Q.GinzburgPathComponent k (Q.target a) (Q.source a)) :=
  Finsupp.linearCombination k (Q.ginzburgSubstitutedOccurrenceOperator k E a)

theorem ginzburgSubstitutedOccurrenceDerivative_single
    (E : Q.VertexCutPathAutomorphism k) (a : Q.Arrow)
    {i j : Q.Vertex} (p : Q.Path i j) (c : k) :
    Q.ginzburgSubstitutedOccurrenceDerivative k E a i j (Finsupp.single p c) =
      c • Q.ginzburgSubstitutedOccurrenceOperator k E a p := by
  simp [ginzburgSubstitutedOccurrenceDerivative]

theorem ginzburgSubstitutedOccurrenceContextMap_original
    (E : Q.VertexCutPathAutomorphism k) {a : Q.Arrow} {i j : Q.Vertex}
    (C : Q.PathOccurrenceContext a i j) (h : Q.PathComponent k j i) :
    Q.ginzburgSubstitutedOccurrenceContextMap k E C
      (Q.originalGinzburgLinearMap k j i
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E j i h)) =
      Q.originalGinzburgLinearMap k (Q.target a) (Q.source a)
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E (Q.target a) (Q.source a)
          (Q.pathOccurrenceContextMap k C h)) := by
  rw [ginzburgSubstitutedOccurrenceContextMap_apply,
    pathOccurrenceContextMap_apply,
    VertexCutPathAutomorphism.componentLinearEquiv_comp,
    VertexCutPathAutomorphism.componentLinearEquiv_comp,
    Q.originalGinzburgLinearMap_comp,Q.originalGinzburgLinearMap_comp]

theorem ginzburgSubstitutedOccurrenceOperator_original
    (E : Q.VertexCutPathAutomorphism k) (a : Q.Arrow)
    {i j : Q.Vertex} (p : Q.Path i j) (h : Q.PathComponent k j i) :
    Q.ginzburgSubstitutedOccurrenceOperator k E a p
      (Q.originalGinzburgLinearMap k j i
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E j i h)) =
      Q.originalGinzburgLinearMap k (Q.target a) (Q.source a)
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E (Q.target a) (Q.source a)
          (Q.pathOccurrenceContextOperator k a p h)) := by
  have hL : ∀ L : List (Q.PathOccurrenceContext a i j),
      (L.map (Q.ginzburgSubstitutedOccurrenceContextMap k E)).sum
        (Q.originalGinzburgLinearMap k j i
          (VertexCutPathAutomorphism.componentLinearEquiv Q k E j i h)) =
        Q.originalGinzburgLinearMap k (Q.target a) (Q.source a)
          (VertexCutPathAutomorphism.componentLinearEquiv Q k E (Q.target a) (Q.source a)
            ((L.map (Q.pathOccurrenceContextMap k)).sum h)) := by
    intro L
    induction L with
    | nil => simp
    | cons C L ih =>
      simp only [List.map_cons,List.sum_cons,LinearMap.add_apply,map_add,
        Q.ginzburgSubstitutedOccurrenceContextMap_original,ih]
  exact hL (p.occurrenceContexts Q a)

theorem ginzburgSubstitutedOccurrenceDerivative_original
    (E : Q.VertexCutPathAutomorphism k) (a : Q.Arrow) (i j : Q.Vertex)
    (f : Q.PathComponent k i j) (h : Q.PathComponent k j i) :
    Q.ginzburgSubstitutedOccurrenceDerivative k E a i j f
      (Q.originalGinzburgLinearMap k j i
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E j i h)) =
      Q.originalGinzburgLinearMap k (Q.target a) (Q.source a)
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E (Q.target a) (Q.source a)
          (Q.pathOccurrenceDerivative k a i j f h)) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp only [map_add,LinearMap.add_apply,ihf,ihg]
  | single p c =>
    simp only [Q.ginzburgSubstitutedOccurrenceDerivative_single,
      Q.pathOccurrenceDerivative_single,LinearMap.smul_apply,map_smul,
      Q.ginzburgSubstitutedOccurrenceOperator_original]

theorem ginzburgSubstitutedOccurrenceContextMap_mem_cohomological
    (E : Q.VertexCutPathAutomorphism k) {a : Q.Arrow} {i j : Q.Vertex}
    (C : Q.PathOccurrenceContext a i j) {q : ℤ}
    (h : Q.GinzburgPathComponent k j i)
    (hh : h ∈ Q.ginzburgCohomologicalComponent k j i q) :
    Q.ginzburgSubstitutedOccurrenceContextMap k E C h ∈
      Q.ginzburgCohomologicalComponent k (Q.target a) (Q.source a) q := by
  rw [ginzburgSubstitutedOccurrenceContextMap_apply]
  simpa only [zero_add,add_zero] using
    Q.ginzburgCohomologicalComponent_comp k
      (Q.ginzburgCohomologicalComponent_comp k
        (Q.originalGinzburgLinearMap_degreeZero k _) hh)
      (Q.originalGinzburgLinearMap_degreeZero k _)

theorem ginzburgSubstitutedOccurrenceContextMap_differential
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k)
    {a : Q.Arrow} {i j : Q.Vertex} (C : Q.PathOccurrenceContext a i j)
    (h : Q.GinzburgPathComponent k j i) :
    Q.ginzburgDifferential k φ (Q.target a) (Q.source a)
      (Q.ginzburgSubstitutedOccurrenceContextMap k E C h) =
      Q.ginzburgSubstitutedOccurrenceContextMap k E C
        (Q.ginzburgDifferential k φ j i h) := by
  rw [ginzburgSubstitutedOccurrenceContextMap_apply,
    Q.ginzburgDifferential_comp,Q.ginzburgDifferential_comp,
    Q.ginzburgDifferential_original,Q.ginzburgDifferential_original,
    Q.ginzburgSignMap_homogeneous k (Q.originalGinzburgLinearMap_degreeZero k _),
    ginzburgSign_zero]
  simp only [map_zero,LinearMap.zero_apply,zero_add,add_zero,one_smul,
    ginzburgSubstitutedOccurrenceContextMap_apply]

end ASGinzburg.CutQuiver
