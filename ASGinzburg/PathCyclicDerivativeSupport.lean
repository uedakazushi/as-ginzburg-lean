import ASGinzburg.PathWordEmbeddings
import ASGinzburg.ClosedPathPotentials

/-! Cyclic derivatives of actual closed paths are supported on paths with
the reversed endpoints of the differentiated arrow. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def pathWordSpace (u v : Q.Vertex) : Submodule k (WordPolynomial k Q.Arrow) :=
  Finsupp.supported k k {w | ∃ p : Q.Path u v, p.toList=w}

theorem single_path_mem_wordSpace {u v : Q.Vertex} (p : Q.Path u v) (c : k) :
    Finsupp.single p.toList c ∈ Q.pathWordSpace k u v :=
  Finsupp.single_mem_supported k c ⟨p,rfl⟩

theorem derivativeAux_closed_path_mem (a : Q.Arrow) {u v : Q.Vertex}
    (pre : Q.Path u v) (suffix : Q.Path v u) :
    derivativeAux (k:=k) a pre.toList suffix.toList ∈
      Q.pathWordSpace k (Q.target a) (Q.source a) := by
  induction suffix with
  | nil => simp [Path.toList,derivativeAux]
  | @snoc w suffix b hb ih =>
    rw [Path.toList,derivativeAux_append]
    apply Submodule.add_mem
    · let first : Q.Path w (Q.target b) := .snoc (.nil w) b hb
      have H := ih (first.comp pre)
      simpa only [Path.toList_comp,first,Path.toList,List.nil_append] using H
    · by_cases hab : a=b
      · subst a
        have hp := Q.single_path_mem_wordSpace k (pre.comp suffix) (1:k)
        have hends : w=Q.source b := hb.symm
        subst w
        simpa [derivativeAux,Path.toList_comp] using hp
      · simp [derivativeAux,hab]

theorem cyclicDerivative_closed_path_mem (a : Q.Arrow) {v : Q.Vertex}
    (p : Q.Path v v) :
    cyclicDerivative a (traceWord (k:=k) p.toList) ∈
      Q.pathWordSpace k (Q.target a) (Q.source a) := by
  rw [cyclicDerivative_traceWord]
  exact Q.derivativeAux_closed_path_mem k a (.nil v) p

theorem cyclicDerivative_potential_mem (a : Q.Arrow) (φ : Q.Potential k) :
    cyclicDerivative a φ.val ∈ Q.pathWordSpace k (Q.target a) (Q.source a) := by
  obtain ⟨φ,hf⟩ := φ
  change cyclicDerivative a φ ∈ _
  change φ ∈ Q.potentialSpace k at hf
  rw [Q.potentialSpace_eq_span k] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,p,hc,hl,rfl⟩ := hx
    exact Q.cyclicDerivative_closed_path_mem k a p
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using Submodule.smul_mem _ c ih

end ASGinzburg.CutQuiver
