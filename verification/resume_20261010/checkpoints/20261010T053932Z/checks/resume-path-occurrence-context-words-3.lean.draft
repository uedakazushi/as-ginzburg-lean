import work.ASGinzburgDraft.PathOccurrenceContextProperties
import work.ASGinzburgDraft.PathWordPolynomialSubstitution
import work.ASGinzburgDraft.WordOccurrenceContexts

/-! Actual occurrence-context insertion agrees with the unrestricted
word occurrence operator under the genuine path-to-word embedding. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathWordMap_occurrenceContextMap {b : Q.Arrow} {i j : Q.Vertex}
    (C : Q.PathOccurrenceContext b i j) (h : Q.PathComponent k j i) :
    Q.pathWordMap k (Q.target b) (Q.source b) (Q.pathOccurrenceContextMap k C h) =
      wordOccurrenceSandwich C.beforePath.toList C.afterPath.toList
        (Q.pathWordMap k j i h) := by
  rw [pathOccurrenceContextMap_apply, pathWordMap_comp, pathWordMap_comp,
    pathWordMap_single, pathWordMap_single, wordOccurrenceSandwich_eq_concatenation]

theorem pathOccurrenceContextMap_snoc {b : Q.Arrow} {i j : Q.Vertex}
    (C : Q.PathOccurrenceContext b i j) (a : Q.Arrow) (ha : Q.source a = j)
    (h : Q.PathComponent k (Q.target a) i) :
    Q.pathOccurrenceContextMap k (C.snoc Q a ha) h =
      Q.pathOccurrenceContextMap k C
        (Q.pathComp k h (Finsupp.single (Path.snoc (.nil j) a ha) 1)) := by
  have hC : Q.pathComp k (Finsupp.single (Path.snoc (.nil j) a ha) 1)
      (Finsupp.single C.afterPath 1) = Finsupp.single (Path.snoc C.afterPath a ha) 1 := by
    simp [pathComp_single, Path.comp]
  rw [pathOccurrenceContextMap_apply, pathOccurrenceContextMap_apply]
  change Q.pathComp k (Finsupp.single C.beforePath 1)
      (Q.pathComp k h (Finsupp.single (Path.snoc C.afterPath a ha) 1)) = _
  rw [← hC, Q.pathComp_assoc k (Finsupp.single C.afterPath 1)
    (Finsupp.single (Path.snoc (.nil j) a ha) 1) h]

theorem pathOccurrenceContext_snoc_sum {b : Q.Arrow} {i j : Q.Vertex}
    (L : List (Q.PathOccurrenceContext b i j)) (a : Q.Arrow) (ha : Q.source a = j)
    (h : Q.PathComponent k (Q.target a) i) :
    (L.map (fun C => Q.pathOccurrenceContextMap k (C.snoc Q a ha))).sum h =
      (L.map (Q.pathOccurrenceContextMap k)).sum
        (Q.pathComp k h (Finsupp.single (Path.snoc (.nil j) a ha) 1)) := by
  induction L with
  | nil => rfl
  | cons C L ih =>
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply,
      pathOccurrenceContextMap_snoc, ih]

theorem pathWordMap_occurrenceContextOperator (b : Q.Arrow)
    {i j : Q.Vertex} (p : Q.Path i j) (h : Q.PathComponent k j i) :
    Q.pathWordMap k (Q.target b) (Q.source b) (Q.pathOccurrenceContextOperator k b p h) =
      wordOccurrenceContextWord b p.toList (Q.pathWordMap k j i h) := by
  induction p with
  | nil =>
    simp [pathOccurrenceContextOperator, Path.occurrenceContexts, Path.toList,
      wordOccurrenceContextWord, wordOccurrenceContextAux]
  | @snoc j p a ha ih =>
    unfold pathOccurrenceContextOperator
    rw [Path.occurrenceContexts, List.map_append, List.sum_append,
      LinearMap.add_apply, map_add, List.map_map]
    simp only [Function.comp_def]
    rw [Q.pathOccurrenceContext_snoc_sum k (p.occurrenceContexts Q b) a ha h]
    change Q.pathWordMap k (Q.target b) (Q.source b)
        (Q.pathOccurrenceContextOperator k b p
          (Q.pathComp k h (Finsupp.single (Path.snoc (.nil j) a ha) 1))) + _ = _
    rw [ih, pathWordMap_comp, pathWordMap_single]
    simp only [Path.toList, List.nil_append]
    rw [wordOccurrenceContextWord_append]
    congr 1
    by_cases hab : a = b
    · subst a
      subst j
      simp [Path.transport, Path.toList, pathOccurrenceContextMap_apply,
        pathWordMap_comp, wordOccurrenceContextWord, wordOccurrenceContextAux,
        wordOccurrenceSandwich_eq_concatenation]
    · have hba : b ≠ a := Ne.symm hab
      simp [hab, hba, wordOccurrenceContextWord, wordOccurrenceContextAux]

theorem pathWordMap_occurrenceDerivative (b : Q.Arrow) (i j : Q.Vertex)
    (f : Q.PathComponent k i j) (h : Q.PathComponent k j i) :
    Q.pathWordMap k (Q.target b) (Q.source b) (Q.pathOccurrenceDerivative k b i j f h) =
      wordOccurrenceContext b (Q.pathWordMap k i j f) (Q.pathWordMap k j i h) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
  | single p c =>
    simp only [pathOccurrenceDerivative_single, LinearMap.smul_apply, map_smul,
      pathWordMap_occurrenceContextOperator, pathWordMap_single, wordOccurrenceContext_single]

end ASGinzburg.CutQuiver
