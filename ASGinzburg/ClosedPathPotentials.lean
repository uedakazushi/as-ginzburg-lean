import ASGinzburg.CyclicDerivative
import ASGinzburg.PathAlgebra
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! Actual potentials are finite cyclic polynomials supported on composable
closed quiver paths of cut degree one and length at least three. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def potentialClasses : Set (CyclicWord Q.Arrow) :=
  {c | ∃ v, ∃ p : Q.Path v v,
    p.cutDegree=1 ∧ 3 ≤ p.length ∧ wordClass p.toList=c}

def potentialSpace : Submodule k (CyclicPolynomial k Q.Arrow) :=
  Finsupp.supported k k Q.potentialClasses

abbrev Potential := Q.potentialSpace k

theorem traceWord_mem_potentialSpace {v : Q.Vertex} (p : Q.Path v v)
    (hc : p.cutDegree=1) (hl : 3 ≤ p.length) :
    traceWord (k:=k) p.toList ∈ Q.potentialSpace k :=
  Finsupp.single_mem_supported k 1 ⟨v,p,hc,hl,rfl⟩

theorem potentialSpace_eq_span :
    Q.potentialSpace k = Submodule.span k
      {φ | ∃ v, ∃ p : Q.Path v v,
        p.cutDegree=1 ∧ 3 ≤ p.length ∧ traceWord (k:=k) p.toList=φ} := by
  rw [potentialSpace,Finsupp.supported_eq_span_single]
  congr 1
  ext φ
  constructor
  · rintro ⟨c,⟨v,p,hc,hl,rfl⟩,rfl⟩
    exact ⟨v,p,hc,hl,rfl⟩
  · rintro ⟨v,p,hc,hl,rfl⟩
    exact ⟨wordClass p.toList,⟨v,p,hc,hl,rfl⟩,rfl⟩

theorem cyclicCutReconstruction_potential (φ : Q.Potential k) :
    cyclicCutReconstruction Q.cut φ.val = φ.val := by
  obtain ⟨φ,hf⟩ := φ
  change cyclicCutReconstruction Q.cut φ = φ
  change φ ∈ Q.potentialSpace k at hf
  rw [Q.potentialSpace_eq_span k] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,p,hc,hl,rfl⟩ := hx
    rw [cyclicCutReconstruction_traceWord,reconstructAux_euler,path_word_cutDegree,hc]
    simp
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy]
  | smul a x hx ih => simp only [map_smul,ih]

/-- The actual cut Euler identity (3.8) on the closed-path potential space. -/
theorem cut_cyclic_derivative_potential_identity (φ : Q.Potential k) :
    (∑ a : Q.Arrow, if Q.cut a then
      prependTrace a (cyclicDerivative a φ.val) else 0) = φ.val := by
  have H := Q.cyclicCutReconstruction_potential k φ
  simpa only [cyclicCutReconstruction,LinearMap.sum_apply,ite_linearMap_apply,
    LinearMap.comp_apply,LinearMap.zero_apply] using H

end ASGinzburg.CutQuiver
