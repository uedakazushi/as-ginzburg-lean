import ASGinzburg.PathLinearIdeals
import ASGinzburg.PathWordEmbeddings
import ASGinzburg.PathUnrolling

/-! Genuine occurrence contexts in a composable path. A reversed-endpoint
relation can be inserted at every occurrence of an arrow; every resulting
term remains in any actual two-sided path ideal containing that relation. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver)

structure PathOccurrenceContext (b : Q.Arrow) (i j : Q.Vertex) where
  beforePath : Q.Path i (Q.source b)
  afterPath : Q.Path (Q.target b) j

def PathOccurrenceContext.snoc {b : Q.Arrow} {i j : Q.Vertex}
    (C : Q.PathOccurrenceContext b i j) (a : Q.Arrow) (ha : Q.source a = j) :
    Q.PathOccurrenceContext b i (Q.target a) where
  beforePath := C.beforePath
  afterPath := .snoc C.afterPath a ha

def Path.occurrenceContexts (b : Q.Arrow) :
    {i j : Q.Vertex} → Q.Path i j → List (Q.PathOccurrenceContext b i j)
  | _, _, .nil _ => []
  | _, _, .snoc p a ha =>
    (occurrenceContexts b p).map (fun C => C.snoc Q a ha) ++
      if h : a = b then
        [⟨p.transport rfl (ha.symm.trans (congrArg Q.source h)),
          (Path.nil (Q := Q) (Q.target b)).transport rfl (congrArg Q.target h.symm)⟩]
      else []

variable (k : Type u) [Field k]

noncomputable def pathOccurrenceContextMap {b : Q.Arrow} {i j : Q.Vertex}
    (C : Q.PathOccurrenceContext b i j) :
    Q.PathComponent k j i →ₗ[k] Q.PathComponent k (Q.target b) (Q.source b) :=
  (Q.pathComp k (Finsupp.single C.beforePath 1)).comp
    ((Q.pathComp k).flip (Finsupp.single C.afterPath 1))

@[simp] theorem pathOccurrenceContextMap_apply {b : Q.Arrow} {i j : Q.Vertex}
    (C : Q.PathOccurrenceContext b i j) (h : Q.PathComponent k j i) :
    Q.pathOccurrenceContextMap k C h =
      Q.pathComp k (Finsupp.single C.beforePath 1)
        (Q.pathComp k h (Finsupp.single C.afterPath 1)) := rfl

theorem pathOccurrenceContextMap_mem_ideal {b : Q.Arrow} {i j : Q.Vertex}
    (C : Q.PathOccurrenceContext b i j) (I : Q.PathLinearIdeal k)
    (h : Q.PathComponent k j i) (hh : h ∈ I.hom j i) :
    Q.pathOccurrenceContextMap k C h ∈ I.hom (Q.target b) (Q.source b) :=
  I.comp_left (I.comp_right hh (Finsupp.single C.afterPath 1))
    (Finsupp.single C.beforePath 1)

noncomputable def pathOccurrenceContextOperator (b : Q.Arrow)
    {i j : Q.Vertex} (p : Q.Path i j) :
    Q.PathComponent k j i →ₗ[k] Q.PathComponent k (Q.target b) (Q.source b) :=
  ((p.occurrenceContexts Q b).map (Q.pathOccurrenceContextMap k)).sum

theorem pathOccurrenceContextOperator_mem_ideal (b : Q.Arrow)
    {i j : Q.Vertex} (p : Q.Path i j) (I : Q.PathLinearIdeal k)
    (h : Q.PathComponent k j i) (hh : h ∈ I.hom j i) :
    Q.pathOccurrenceContextOperator k b p h ∈ I.hom (Q.target b) (Q.source b) := by
  have hL : ∀ L : List (Q.PathOccurrenceContext b i j),
      (L.map (Q.pathOccurrenceContextMap k)).sum h ∈
        I.hom (Q.target b) (Q.source b) := by
    intro L
    induction L with
    | nil => exact (I.hom _ _).zero_mem
    | cons C L ih =>
      exact (I.hom _ _).add_mem (Q.pathOccurrenceContextMap_mem_ideal k C I h hh) ih
  exact hL (p.occurrenceContexts Q b)

noncomputable def pathOccurrenceDerivative (b : Q.Arrow) (i j : Q.Vertex) :
    Q.PathComponent k i j →ₗ[k]
      (Q.PathComponent k j i →ₗ[k] Q.PathComponent k (Q.target b) (Q.source b)) :=
  Finsupp.linearCombination k (Q.pathOccurrenceContextOperator k b)

@[simp] theorem pathOccurrenceDerivative_single (b : Q.Arrow)
    {i j : Q.Vertex} (p : Q.Path i j) (c : k) :
    Q.pathOccurrenceDerivative k b i j (Finsupp.single p c) =
      c • Q.pathOccurrenceContextOperator k b p := by
  simp [pathOccurrenceDerivative]

theorem pathOccurrenceDerivative_mem_ideal (b : Q.Arrow) (i j : Q.Vertex)
    (f : Q.PathComponent k i j) (I : Q.PathLinearIdeal k)
    (h : Q.PathComponent k j i) (hh : h ∈ I.hom j i) :
    Q.pathOccurrenceDerivative k b i j f h ∈ I.hom (Q.target b) (Q.source b) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simpa only [map_zero, LinearMap.zero_apply] using (I.hom _ _).zero_mem
  | add f g ihf ihg =>
    simpa only [map_add, LinearMap.add_apply] using (I.hom _ _).add_mem ihf ihg
  | single p c =>
    simpa only [pathOccurrenceDerivative_single, LinearMap.smul_apply] using
      (I.hom _ _).smul_mem c (Q.pathOccurrenceContextOperator_mem_ideal k b p I h hh)

end ASGinzburg.CutQuiver
