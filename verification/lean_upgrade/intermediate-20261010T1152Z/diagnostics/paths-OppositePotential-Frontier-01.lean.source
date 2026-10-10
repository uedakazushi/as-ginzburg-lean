import ASGinzburg.OppositePathEquiv
import ASGinzburg.CyclicWordReversal

/-! Reversal of the actual closed-path, cut-one, length-at-least-three
potential space. No new potential admissibility assumption is used. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem reverseCyclicPolynomial_mem_oppositePotentialSpace
    (φ : CyclicPolynomial k Q.Arrow) (hφ : φ ∈ Q.potentialSpace k) :
    reverseCyclicPolynomial φ ∈ Q.opposite.potentialSpace k := by
  rw [Q.potentialSpace_eq_span k] at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,p,hc,hl,rfl⟩ := hx
    rw [reverseCyclicPolynomial_traceWord, ← Path.opposite_toList p]
    exact Q.opposite.traceWord_mem_potentialSpace k p.opposite
      (by simpa [Path.opposite_cutDegree] using hc)
      (by simpa [Path.opposite_length] using hl)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using
      (Q.opposite.potentialSpace k).add_mem ihx ihy
  | smul a x hx ih => simpa only [map_smul] using
      (Q.opposite.potentialSpace k).smul_mem a ih

theorem reverseCyclicPolynomial_mem_originalPotentialSpace
    (φ : CyclicPolynomial k Q.opposite.Arrow)
    (hφ : φ ∈ Q.opposite.potentialSpace k) :
    reverseCyclicPolynomial φ ∈ Q.potentialSpace k := by
  rw [Q.opposite.potentialSpace_eq_span k] at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,p,hc,hl,rfl⟩ := hx
    obtain ⟨q,hq⟩ := (oppositePathEquiv (Q := Q) v.rev v.rev).surjective
      (p.transport (Fin.rev_rev v).symm (Fin.rev_rev v).symm)
    have hw : q.toList.reverse = p.toList := by
      have hh := congrArg Path.toList hq
      simpa [oppositePathEquiv, Path.opposite_toList] using hh
    have hqc : q.cutDegree = 1 := by
      have hh : q.cutDegree = p.cutDegree := by
        simpa [oppositePathEquiv, Path.opposite_cutDegree] using congrArg Path.cutDegree hq
      exact hh.trans hc
    have hql : 3 ≤ q.length := by
      have hh : q.length = p.length := by
        simpa [oppositePathEquiv, Path.opposite_length] using congrArg Path.length hq
      simpa only [hh] using hl
    rw [reverseCyclicPolynomial_traceWord, ← hw, List.reverse_reverse]
    exact Q.traceWord_mem_potentialSpace k q hqc hql
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using
      (Q.potentialSpace k).add_mem ihx ihy
  | smul a x hx ih => simpa only [map_smul] using
      (Q.potentialSpace k).smul_mem a ih

noncomputable def oppositePotentialMap : Q.Potential k →ₗ[k] Q.opposite.Potential k where
  toFun φ := ⟨reverseCyclicPolynomial φ.val,
    Q.reverseCyclicPolynomial_mem_oppositePotentialSpace k φ.val φ.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

noncomputable def oppositePotentialEquiv : Q.Potential k ≃ₗ[k] Q.opposite.Potential k where
  __ := Q.oppositePotentialMap k
  invFun φ := ⟨reverseCyclicPolynomial φ.val,
    Q.reverseCyclicPolynomial_mem_originalPotentialSpace k φ.val φ.property⟩
  left_inv φ := Subtype.ext (reverseCyclicPolynomial_involutive φ.val)
  right_inv φ := Subtype.ext (reverseCyclicPolynomial_involutive φ.val)

@[simp] theorem oppositePotentialEquiv_val (φ : Q.Potential k) :
    (Q.oppositePotentialEquiv k φ).val = reverseCyclicPolynomial φ.val := rfl

end ASGinzburg.CutQuiver
