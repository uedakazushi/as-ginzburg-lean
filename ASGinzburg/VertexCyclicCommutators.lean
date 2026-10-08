import ASGinzburg.PathCyclicDerivativeDegrees
import ASGinzburg.CyclicDerivativeCommutators

/-! The global cyclic commutator identity splits into the actual vertex
identities needed for the square of each Ginzburg loop differential. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def wordSource (w : List Q.Arrow) : Option Q.Vertex := w.head?.map Q.source

@[simp] theorem wordSource_cons (a : Q.Arrow) (w : List Q.Arrow) :
    Q.wordSource (a::w)=some (Q.source a) := rfl

theorem wordSource_append_of_nonempty (w z : List Q.Arrow) (hw : w≠[]) :
    Q.wordSource (w++z)=Q.wordSource w := by
  unfold wordSource
  rw [List.head?_append_of_ne_nil _ hw]

theorem Path.wordSource_of_length_pos {u v : Q.Vertex} (p : Q.Path u v) (hp : 0<p.length) :
    Q.wordSource p.toList=some u := by
  induction p with
  | nil => simp [length] at hp
  | snoc p a h ih =>
    cases p with
    | nil => simp [toList,wordSource,h]
    | snoc p b hb =>
      rw [Path.toList,Q.wordSource_append_of_nonempty]
      · exact ih (by simp [length])
      · simp [toList]

noncomputable def vertexWordProjection (v : Q.Vertex) :
    WordPolynomial k Q.Arrow →ₗ[k] WordPolynomial k Q.Arrow :=
  Finsupp.linearCombination k (fun w => if Q.wordSource w=some v then Finsupp.single w 1 else 0)

@[simp] theorem vertexWordProjection_single (v : Q.Vertex) (w : List Q.Arrow) (c : k) :
    Q.vertexWordProjection k v (Finsupp.single w c)=
      if Q.wordSource w=some v then Finsupp.single w c else 0 := by
  classical
  by_cases h : Q.wordSource w=some v <;> simp [vertexWordProjection,h]

theorem vertexWordProjection_prepend (v : Q.Vertex) (a : Q.Arrow)
    (f : WordPolynomial k Q.Arrow) :
    Q.vertexWordProjection k v (prependWord a f)=
      if Q.source a=v then prependWord a f else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    by_cases h : Q.source a=v <;> simp [map_add,hf,hg,h]
  | single w c => simp [prependWord,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

@[simp] theorem pathWordMap_single {u v : Q.Vertex} (p : Q.Path u v) (c : k) :
    Q.pathWordMap k u v (Finsupp.single p c)=Finsupp.single p.toList c :=
  Finsupp.mapDomain_single

theorem vertexWordProjection_append_path (v : Q.Vertex) (a : Q.Arrow)
    {f : Q.PathComponent k (Q.target a) (Q.source a)}
    (hf : f ∈ Finsupp.supported k k {p | 0<p.length}) :
    Q.vertexWordProjection k v (appendWord a (Q.pathWordMap k _ _ f))=
      if Q.target a=v then appendWord a (Q.pathWordMap k _ _ f) else 0 := by
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    change 0<p.length at hp
    have hw : p.toList≠[] := by
      intro h
      have H := p.length_toList
      rw [h] at H
      simp only [List.length_nil] at H
      omega
    simp [appendWord,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
      Q.wordSource_append_of_nonempty _ _ hw,p.wordSource_of_length_pos Q hp]
  | zero => simp
  | add f g hf hg ihf ihg =>
    by_cases h : Q.target a=v <;> simp [map_add,ihf,ihg,h]
  | smul c f hf ih =>
    by_cases h : Q.target a=v <;> simp [map_smul,ih,h]

theorem vertexWordProjection_append_derivative (v : Q.Vertex) (a : Q.Arrow) (φ : Q.Potential k) :
    Q.vertexWordProjection k v (appendWord a (cyclicDerivative a φ.val))=
      if Q.target a=v then appendWord a (cyclicDerivative a φ.val) else 0 := by
  rw [←Q.pathWordMap_pathCyclicDerivative k a φ]
  apply Q.vertexWordProjection_append_path k
  apply Finsupp.supported_mono _ (Q.pathCyclicDerivative_supported_degrees k a φ)
  rintro p ⟨hp,_⟩
  change 0<p.length
  omega

theorem cyclicDerivative_vertex_commutator (v : Q.Vertex) (φ : Q.Potential k) :
    (∑ a : Q.Arrow, ((if Q.source a=v then prependWord a (cyclicDerivative a φ.val) else 0)-
      (if Q.target a=v then appendWord a (cyclicDerivative a φ.val) else 0)))=0 := by
  have h := congrArg (Q.vertexWordProjection k v) (cyclicDerivative_commutator φ.val)
  simpa only [map_sum,map_zero,wordCommutator,LinearMap.sub_apply,map_sub,
    Q.vertexWordProjection_prepend k,Q.vertexWordProjection_append_derivative k] using h

end ASGinzburg.CutQuiver
