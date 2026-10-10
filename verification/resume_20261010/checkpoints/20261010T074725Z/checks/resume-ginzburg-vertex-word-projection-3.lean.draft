import ASGinzburg.GinzburgPathWords
import ASGinzburg.GinzburgDegreeZeroAlgebra

/-! A genuine first-letter vertex filter localizes nonempty extended path
words. The first letter's source is derived from actual path composability. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def ginzburgWordStartsAt (v : Q.Vertex) : List Q.GinzburgArrow → Prop
  | [] => False
  | a :: _ => a.source Q = v

instance ginzburgWordStartsAtDecidable (v : Q.Vertex) (w : List Q.GinzburgArrow) :
    Decidable (Q.ginzburgWordStartsAt v w) := by
  cases w <;> dsimp only [ginzburgWordStartsAt] <;> infer_instance

theorem ginzburgWordStartsAt_append_of_nonempty (v : Q.Vertex)
    (p s : List Q.GinzburgArrow) (hp : p ≠ []) :
    Q.ginzburgWordStartsAt v (p ++ s) ↔ Q.ginzburgWordStartsAt v p := by
  cases p with
  | nil => exact (hp rfl).elim
  | cons a p => rfl

theorem GinzburgPath.wordStartsAt_source {i j : Q.Vertex}
    (p : Q.GinzburgPath i j) (hp : p.toList ≠ []) :
    Q.ginzburgWordStartsAt i p.toList := by
  induction p with
  | nil => exact (hp rfl).elim
  | @snoc j p a ha ih =>
    by_cases hpre : p.toList = []
    · have he : i = j := by
        cases p with
        | nil => rfl
        | snoc p a ha => simp [GinzburgPath.toList] at hpre
      change Q.ginzburgWordStartsAt i (p.toList ++ [a])
      rw [hpre]
      change a.source Q = i
      exact ha.trans he.symm
    · rw [GinzburgPath.toList]
      exact (Q.ginzburgWordStartsAt_append_of_nonempty i p.toList [a] hpre).mpr (ih hpre)

theorem GinzburgPath.wordStartsAt_iff {i j : Q.Vertex}
    (p : Q.GinzburgPath i j) (hp : p.toList ≠ []) (v : Q.Vertex) :
    Q.ginzburgWordStartsAt v p.toList ↔ i = v := by
  have hs := p.wordStartsAt_source Q hp
  cases hw : p.toList with
  | nil => exact (hp hw).elim
  | cons a s =>
    rw [hw] at hs
    change a.source Q = i at hs
    change a.source Q = v ↔ i = v
    rw [hs]

theorem GinzburgPath.toList_ne_nil_of_cohomologicalDegree_ne_zero {i j : Q.Vertex}
    (p : Q.GinzburgPath i j) (hp : p.cohomologicalDegree ≠ 0) : p.toList ≠ [] := by
  cases p with
  | nil => exact (hp rfl).elim
  | snoc p a ha => simp [GinzburgPath.toList]

noncomputable def ginzburgVertexWordProjection (v : Q.Vertex) :
    WordPolynomial k Q.GinzburgArrow →ₗ[k] WordPolynomial k Q.GinzburgArrow := by
  classical
  exact Finsupp.linearCombination k (fun w =>
    if Q.ginzburgWordStartsAt v w then Finsupp.single w 1 else 0)

theorem ginzburgVertexWordProjection_single (v : Q.Vertex)
    (w : List Q.GinzburgArrow) (c : k) :
    Q.ginzburgVertexWordProjection k v (Finsupp.single w c) =
      if Q.ginzburgWordStartsAt v w then Finsupp.single w c else 0 := by
  classical
  by_cases hw : Q.ginzburgWordStartsAt v w <;>
    simp [ginzburgVertexWordProjection, hw]

theorem ginzburgVertexWordProjection_pathWordMap_single_of_nonempty
    (v i j : Q.Vertex) (p : Q.GinzburgPath i j) (hp : p.toList ≠ []) (c : k) :
    Q.ginzburgVertexWordProjection k v (Q.ginzburgPathWordMap k i j (Finsupp.single p c)) =
      if i = v then Q.ginzburgPathWordMap k i j (Finsupp.single p c) else 0 := by
  classical
  simp only [ginzburgPathWordMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [ginzburgVertexWordProjection_single]
  by_cases hi : i = v
  · rw [if_pos hi, if_pos ((p.wordStartsAt_iff Q hp v).mpr hi)]
  · rw [if_neg hi, if_neg (fun H => hi ((p.wordStartsAt_iff Q hp v).mp H))]

theorem ginzburgVertexWordProjection_pathWordMap_of_nonempty
    (v i j : Q.Vertex) (f : Q.GinzburgPathComponent k i j)
    (hf : f ∈ Finsupp.supported k k {p : Q.GinzburgPath i j | p.toList ≠ []}) :
    Q.ginzburgVertexWordProjection k v (Q.ginzburgPathWordMap k i j f) =
      if i = v then Q.ginzburgPathWordMap k i j f else 0 := by
  classical
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨p, hp, rfl⟩ := hf
    exact Q.ginzburgVertexWordProjection_pathWordMap_single_of_nonempty k v i j p hp 1
  | zero => simp
  | add f g hf hg ihf ihg =>
    by_cases hi : i = v <;> simp only [map_add, ihf, ihg, hi, if_true, if_false, add_zero]
  | smul c f hf ih =>
    by_cases hi : i = v <;> simp only [map_smul, ih, hi, if_true, if_false, smul_zero]

theorem ginzburgVertexWordProjection_pathWordMap_of_cohomological
    (v i j : Q.Vertex) (q : ℤ) (hq : q ≠ 0)
    (f : Q.GinzburgPathComponent k i j)
    (hf : f ∈ Q.ginzburgCohomologicalComponent k i j q) :
    Q.ginzburgVertexWordProjection k v (Q.ginzburgPathWordMap k i j f) =
      if i = v then Q.ginzburgPathWordMap k i j f else 0 := by
  apply Q.ginzburgVertexWordProjection_pathWordMap_of_nonempty k v i j f
  apply Finsupp.supported_mono _ hf
  intro p hp
  exact p.toList_ne_nil_of_cohomologicalDegree_ne_zero Q (by rw [hp]; exact hq)

end ASGinzburg.CutQuiver
