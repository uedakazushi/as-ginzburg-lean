import ASGinzburg.PathCyclicHessian
import ASGinzburg.PathCyclicDerivativeDegrees

/-! The original potential conditions force the actual Hessian entries
to have positive path length and the complementary cut degree. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem cyclicHessianWord_potential_supported_degrees
    (a b : Q.Arrow) (φ : Q.Potential k) :
    cyclicHessianWord a b φ.val ∈ Finsupp.supported k k
      {w | 1 ≤ w.length ∧ wordCutDegree Q.cut w+Q.cutDegree b+Q.cutDegree a=1} := by
  apply (Finsupp.mem_supported' k _).mpr
  intro w hw
  rw [cyclicHessianWord_apply]
  apply (Finsupp.mem_supported' k _).mp
    (Q.cyclicDerivative_potential_supported_degrees k a φ)
  intro h
  apply hw
  simp only [Set.mem_setOf_eq,List.length_append,List.length_singleton,
    wordCutDegree_append,wordCutDegree] at h
  change 1 ≤ w.length ∧ wordCutDegree Q.cut w+Q.cutDegree b+Q.cutDegree a=1
  simpa only [CutQuiver.cutDegree,Nat.add_zero] using
    (show 1 ≤ w.length ∧ wordCutDegree Q.cut w+(if Q.cut b then 1 else 0)+Q.cutDegree a=1 by
      constructor
      · omega
      · simpa only [Nat.add_zero] using h.2)

theorem pathCyclicHessian_supported_degrees (a b : Q.Arrow) (φ : Q.Potential k) :
    Q.pathCyclicHessian k a b φ ∈ Finsupp.supported k k
      {p : Q.Path (Q.target a) (Q.source b) |
        1 ≤ p.length ∧ p.cutDegree+Q.cutDegree b+Q.cutDegree a=1} := by
  apply (Finsupp.mem_supported' k _).mpr
  intro p hp
  have hword : p.toList ∉ {w : List Q.Arrow |
      1 ≤ w.length ∧ wordCutDegree Q.cut w+Q.cutDegree b+Q.cutDegree a=1} := by
    simpa only [Set.mem_setOf_eq,p.length_toList,path_word_cutDegree] using hp
  have H := (Finsupp.mem_supported' k _).mp
    (Q.cyclicHessianWord_potential_supported_degrees k a b φ) p.toList hword
  rw [←Q.pathWordMap_pathCyclicHessian k a b φ] at H
  change (Finsupp.mapDomain Path.toList (Q.pathCyclicHessian k a b φ)) p.toList=0 at H
  rw [Finsupp.mapDomain_apply (Path.toList_injective (Q.target a) (Q.source b))] at H
  exact H

end ASGinzburg.CutQuiver
