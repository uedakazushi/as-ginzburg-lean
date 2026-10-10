import work.ASGinzburgDraft.GinzburgArrowSubstitution
import ASGinzburg.WordPolynomialSubstitution

/-! The actual extended path embedding preserves products and literal
extended generator substitutions. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgPathWordMap_single {i j : Q.Vertex}
    (p : Q.GinzburgPath i j) (c : k) :
    Q.ginzburgPathWordMap k i j (Finsupp.single p c) =
      Finsupp.single p.toList c := by
  simp [ginzburgPathWordMap,Finsupp.lmapDomain_apply]

theorem ginzburgPathWordMap_comp {i j l : Q.Vertex}
    (f : Q.GinzburgPathComponent k i j) (g : Q.GinzburgPathComponent k j l) :
    Q.ginzburgPathWordMap k i l (Q.ginzburgPathComp k g f) =
      wordConcatenation (Q.ginzburgPathWordMap k i j f) (Q.ginzburgPathWordMap k j l g) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f h ihf ihh => simp only [map_add,LinearMap.add_apply,ihf,ihh]
  | single p c =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g h ihg ihh => simp only [map_add,LinearMap.add_apply,ihg,ihh]
    | single q d =>
      simp [Q.ginzburgPathWordMap_single,wordConcatenation_single,mul_comm]

noncomputable def ginzburgWordArrowReplacement
    (σ : Q.GinzburgArrowReplacement k) : Q.GinzburgArrow → WordPolynomial k Q.GinzburgArrow :=
  fun a => Q.ginzburgPathWordMap k (a.source Q) (a.target Q) (σ a)

theorem ginzburgPathWordMap_substitutionPath
    (σ : Q.GinzburgArrowReplacement k) {i j : Q.Vertex} (p : Q.GinzburgPath i j) :
    Q.ginzburgPathWordMap k i j (Q.ginzburgArrowSubstitutionPath k σ p) =
      wordSubstitutionWord (Q.ginzburgWordArrowReplacement k σ) p.toList := by
  induction p with
  | nil => simp [ginzburgArrowSubstitutionPath,ginzburgPathId,
      Q.ginzburgPathWordMap_single,GinzburgPath.toList,wordSubstitutionWord]
  | @snoc j p a ha ih =>
    subst j
    rw [ginzburgArrowSubstitutionPath,Q.ginzburgPathWordMap_comp,ih]
    simp [GinzburgPath.toList,wordSubstitutionWord_append,wordSubstitutionWord,
      ginzburgWordArrowReplacement]

theorem ginzburgPathWordMap_substitutionComponent
    (σ : Q.GinzburgArrowReplacement k) (i j : Q.Vertex)
    (f : Q.GinzburgPathComponent k i j) :
    Q.ginzburgPathWordMap k i j (Q.ginzburgArrowSubstitutionComponent k σ i j f) =
      wordSubstitution (Q.ginzburgWordArrowReplacement k σ) (Q.ginzburgPathWordMap k i j f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp only [map_add,ihf,ihg]
  | single p c =>
    simp only [Q.ginzburgArrowSubstitutionComponent_single,map_smul,
      Q.ginzburgPathWordMap_substitutionPath,Q.ginzburgPathWordMap_single,
      wordSubstitution_single]

end ASGinzburg.CutQuiver
