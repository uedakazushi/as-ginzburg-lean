import work.ASGinzburgDraft.GinzburgArrowSubstitution
import work.ASGinzburgDraft.PathArrowSubstitution

/-! The genuine extension to Ginzburg paths agrees with ordinary path
substitution on actual original paths whenever their generator images agree. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgArrowSubstitutionPath_original
    (σ : Q.GinzburgArrowReplacement k) (ρ : Q.PathArrowReplacement k)
    (hOriginal : ∀ a, σ (.original a) =
      Q.originalGinzburgLinearMap k (Q.source a) (Q.target a) (ρ a))
    {i j : Q.Vertex} (p : Q.Path i j) :
    Q.ginzburgArrowSubstitutionPath k σ (p.originalGinzburg Q) =
      Q.originalGinzburgLinearMap k i j (Q.pathArrowSubstitutionPath k ρ p) := by
  induction p with
  | nil =>
    simpa only [Path.originalGinzburg,ginzburgArrowSubstitutionPath,pathArrowSubstitutionPath]
      using (Q.originalGinzburgLinearMap_id k i).symm
  | @snoc j p a h ih =>
    subst j
    simp [Path.originalGinzburg,ginzburgArrowSubstitutionPath,pathArrowSubstitutionPath,
      hOriginal a,Q.originalGinzburgLinearMap_comp,ih]

theorem ginzburgArrowSubstitutionComponent_original
    (σ : Q.GinzburgArrowReplacement k) (ρ : Q.PathArrowReplacement k)
    (hOriginal : ∀ a, σ (.original a) =
      Q.originalGinzburgLinearMap k (Q.source a) (Q.target a) (ρ a))
    (i j : Q.Vertex) (f : Q.PathComponent k i j) :
    Q.ginzburgArrowSubstitutionComponent k σ i j (Q.originalGinzburgLinearMap k i j f) =
      Q.originalGinzburgLinearMap k i j (Q.pathArrowSubstitutionComponent k ρ i j f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ih ih' => simp [map_add,ih,ih']
  | single p a => simp [Q.ginzburgArrowSubstitutionPath_original k σ ρ hOriginal]

end ASGinzburg.CutQuiver
