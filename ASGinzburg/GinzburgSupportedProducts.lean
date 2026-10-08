import ASGinzburg.GinzburgGeneratorGradings

/-! Closure of actual supported extended path spaces under multiplication. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgSupported_comp {u v x : Q.Vertex}
    (S : Set (Q.GinzburgPath u v)) (T : Set (Q.GinzburgPath v x))
    (U : Set (Q.GinzburgPath u x))
    (hc : ∀ p ∈ S, ∀ q ∈ T, p.comp q ∈ U)
    {f : Q.GinzburgPathComponent k u v} (hf : f ∈ Finsupp.supported k k S)
    {g : Q.GinzburgPathComponent k v x} (hg : g ∈ Finsupp.supported k k T) :
    Q.ginzburgPathComp k g f ∈ Finsupp.supported k k U := by
  rw [Finsupp.supported_eq_span_single] at hf hg
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q,hq,rfl⟩ := hy
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p,hp,rfl⟩ := hy
      rw [Q.ginzburgPathComp_single]
      exact Finsupp.single_mem_supported _ _ (hc p hp q hq)
    | zero => simp
    | add f h hf hh ihf ihh => simpa only [map_add] using Submodule.add_mem _ ihf ihh
    | smul a f hf ih => simpa only [map_smul] using Submodule.smul_mem _ a ih
  | zero => simp
  | add g h hg hh ihg ihh =>
    simpa only [map_add,LinearMap.add_apply] using Submodule.add_mem _ ihg ihh
  | smul a g hg ih =>
    simpa only [map_smul,LinearMap.smul_apply] using Submodule.smul_mem _ a ih

theorem ginzburgCohomologicalComponent_comp {u v x : Q.Vertex} {q r : ℤ}
    {f : Q.GinzburgPathComponent k u v} (hf : f ∈ Q.ginzburgCohomologicalComponent k u v q)
    {g : Q.GinzburgPathComponent k v x} (hg : g ∈ Q.ginzburgCohomologicalComponent k v x r) :
    Q.ginzburgPathComp k g f ∈ Q.ginzburgCohomologicalComponent k u x (q+r) := by
  apply Q.ginzburgSupported_comp k _ _ _ _ hf hg
  intro p hp q hq
  exact (p.cohomologicalDegree_comp q).trans (congrArg₂ (·+·) hp hq)

theorem ginzburgCutComponent_comp {u v x : Q.Vertex} {c d : ℤ}
    {f : Q.GinzburgPathComponent k u v} (hf : f ∈ Q.ginzburgCutComponent k u v c)
    {g : Q.GinzburgPathComponent k v x} (hg : g ∈ Q.ginzburgCutComponent k v x d) :
    Q.ginzburgPathComp k g f ∈ Q.ginzburgCutComponent k u x (c+d) := by
  apply Q.ginzburgSupported_comp k _ _ _ _ hf hg
  intro p hp q hq
  exact (p.cutDegree_comp q).trans (congrArg₂ (·+·) hp hq)

end ASGinzburg.CutQuiver
