import ASGinzburg.GinzburgGeneratorDifferentials

/-! The actual extended word embedding identifies original path
differentials with the genuine ordinary cyclic derivative polynomials. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def originalGinzburgWordMap :
    WordPolynomial k Q.Arrow →ₗ[k] WordPolynomial k Q.GinzburgArrow :=
  Finsupp.lmapDomain k k (List.map GinzburgArrow.original)

theorem ginzburgPathWordMap_original (i j : Q.Vertex) (f : Q.PathComponent k i j) :
    Q.ginzburgPathWordMap k i j (Q.originalGinzburgLinearMap k i j f) =
      Q.originalGinzburgWordMap k (Q.pathWordMap k i j f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | single p c =>
    simp [ginzburgPathWordMap,originalGinzburgWordMap,originalGinzburgLinearMap_single,
      pathWordMap,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,Path.originalGinzburg_toList]

theorem ginzburgPathWordMap_dualGeneratorDifferential (φ : Q.Potential k) (a : Q.Arrow) :
    Q.ginzburgPathWordMap k (Q.target a) (Q.source a)
      (Q.ginzburgGeneratorDifferential k φ (.dual a)) =
        Q.originalGinzburgWordMap k (cyclicDerivative a φ.val) := by
  change Q.ginzburgPathWordMap k _ _ (Q.originalGinzburgLinearMap k _ _ _) = _
  rw [Q.ginzburgPathWordMap_original,Q.pathWordMap_pathCyclicDerivative]

end ASGinzburg.CutQuiver
