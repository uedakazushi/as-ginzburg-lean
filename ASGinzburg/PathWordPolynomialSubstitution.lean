import ASGinzburg.PathArrowSubstitution
import ASGinzburg.WordPolynomialSubstitution
import ASGinzburg.PathWordEmbeddings

/-! The actual composable path substitution is precisely the unrestricted
word-polynomial substitution under the genuine injective word embedding. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathWordMap_comp {i j l : Q.Vertex}
    (f : Q.PathComponent k i j) (g : Q.PathComponent k j l) :
    Q.pathWordMap k i l (Q.pathComp k g f) =
      wordConcatenation (Q.pathWordMap k i j f) (Q.pathWordMap k j l g) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [map_add, LinearMap.add_apply, hf, hf']
  | single p a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp only [map_add, LinearMap.add_apply, hg, hg']
    | single q b => simp [CutQuiver.Path.toList_comp, mul_comm]

theorem pathWordMap_substitutionPath (σ : Q.PathArrowReplacement k)
    {i j : Q.Vertex} (p : Q.Path i j) :
    Q.pathWordMap k i j (Q.pathArrowSubstitutionPath k σ p) =
      wordSubstitutionWord (fun a => Q.pathWordMap k (Q.source a) (Q.target a) (σ a))
        p.toList := by
  induction p with
  | nil => simp [pathArrowSubstitutionPath, pathId, Path.toList, wordSubstitutionWord]
  | @snoc j p a ha ih =>
    subst j
    simp only [pathArrowSubstitutionPath, pathWordMap_comp, ih, Path.toList,
      wordSubstitutionWord_append]
    simp [wordSubstitutionWord]

theorem pathWordMap_substitutionComponent (σ : Q.PathArrowReplacement k)
    (i j : Q.Vertex) (f : Q.PathComponent k i j) :
    Q.pathWordMap k i j (Q.pathArrowSubstitutionComponent k σ i j f) =
      wordSubstitution (fun a => Q.pathWordMap k (Q.source a) (Q.target a) (σ a))
        (Q.pathWordMap k i j f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single p c =>
    simp only [pathArrowSubstitutionComponent_single, map_smul,
      pathWordMap_substitutionPath, pathWordMap_single, wordSubstitution_single]

end ASGinzburg.CutQuiver
