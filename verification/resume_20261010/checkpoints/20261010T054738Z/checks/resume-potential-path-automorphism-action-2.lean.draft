import work.ASGinzburgDraft.PathPotentialCyclicImage
import work.ASGinzburgDraft.PathAutomorphismGradings
import work.ASGinzburgDraft.PathAutomorphismLengthFiltration
import work.ASGinzburgDraft.AlgebraCyclicAutomorphismAction
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Genuine vertex- and cut-preserving path algebra automorphisms act on
the actual potential space. Preservation of the length condition follows
from fixing the vertices and is not an additional restriction. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem VertexCutPathAutomorphism.cyclicEquiv_closedPathClass
    (E : Q.VertexCutPathAutomorphism k) (i : Q.Vertex)
    (f : Q.PathComponent k i i) :
    algebraCyclicEquiv k E.val (Q.closedPathCyclicClass k i f) =
      Q.closedPathCyclicClass k i
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E i i f) := by
  change Submodule.Quotient.mk (E.val ((Q.pathComponentAlgebra k).totalComponent i i f)) =
    Submodule.Quotient.mk ((Q.pathComponentAlgebra k).totalComponent i i
      (VertexCutPathAutomorphism.componentLinearEquiv Q k E i i f))
  exact congrArg (fun x : Q.PathRing k => Submodule.Quotient.mk x)
    ((Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_component E.val
      (VertexCutPathAutomorphism.fixes_vertex Q k E) i i f).symm

theorem VertexCutPathAutomorphism.cyclicEquiv_closedPathClass_mem_potential_range
    (E : Q.VertexCutPathAutomorphism k) (i : Q.Vertex)
    (f : Q.PathComponent k i i)
    (hc : f ∈ Q.pathCutComponent k i i 1)
    (hl : f ∈ Q.pathLengthFiltration k 3 i i) :
    algebraCyclicEquiv k E.val (Q.closedPathCyclicClass k i f) ∈
      LinearMap.range (Q.potentialCyclicClass k) := by
  let g := VertexCutPathAutomorphism.componentLinearEquiv Q k E i i f
  have hgc : g ∈ Q.pathCutComponent k i i 1 :=
    (VertexCutPathAutomorphism.component_preserves_cut Q k E i i 1 f).mp hc
  have hgl : g ∈ Q.pathLengthFiltration k 3 i i :=
    Q.pathAlgEquivComponent_mem_lengthFiltration k E.val
      (VertexCutPathAutomorphism.fixes_vertex Q k E) 3 hl
  refine ⟨⟨Q.closedPathTrace k i g,
    Q.closedPathTrace_mem_potentialSpace_of_cut_length k i g hgc hgl⟩, ?_⟩
  rw [Q.potentialCyclicClass_closedPathTrace_of_cut_length k i g hgc hgl]
  exact (VertexCutPathAutomorphism.cyclicEquiv_closedPathClass Q k E i f).symm

theorem VertexCutPathAutomorphism.cyclicEquiv_potential_mem_range
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) :
    algebraCyclicEquiv k E.val (Q.potentialCyclicClass k φ) ∈
      LinearMap.range (Q.potentialCyclicClass k) := by
  let L : CyclicPolynomial k Q.Arrow →ₗ[k]
      AlgebraCyclicQuotient k (Q.PathRing k) :=
    (algebraCyclicEquiv k E.val).toLinearMap.comp
      (Finsupp.linearCombination k (Q.potentialWordCyclicClass k))
  change L φ.val ∈ LinearMap.range (Q.potentialCyclicClass k)
  have hφ := φ.property
  change φ.val ∈ Q.potentialSpace k at hφ
  rw [Q.potentialSpace_eq_span k] at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,p,hc,hl,rfl⟩ := hx
    have hsingle : Finsupp.single p 1 ∈ Q.pathCutComponent k i i 1 :=
      Finsupp.single_mem_supported k 1 (by exact_mod_cast hc)
    have hlength : Finsupp.single p 1 ∈ Q.pathLengthFiltration k 3 i i :=
      Finsupp.single_mem_supported k 1 hl
    change algebraCyclicEquiv k E.val
      (Q.potentialCyclicClass k ⟨traceWord (k:=k) p.toList,
        Q.traceWord_mem_potentialSpace k p hc hl⟩) ∈ _
    rw [Q.potentialCyclicClass_traceWord k i p hc hl]
    exact VertexCutPathAutomorphism.cyclicEquiv_closedPathClass_mem_potential_range
      Q k E i _ hsingle hlength
  | zero => simpa only [map_zero] using (LinearMap.range (Q.potentialCyclicClass k)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (LinearMap.range (Q.potentialCyclicClass k)).add_mem ihx ihy
  | smul a x hx ih =>
    simpa only [map_smul] using (LinearMap.range (Q.potentialCyclicClass k)).smul_mem a ih

noncomputable def VertexCutPathAutomorphism.potentialLinearMap
    (E : Q.VertexCutPathAutomorphism k) : Q.Potential k →ₗ[k] Q.Potential k :=
  (LinearEquiv.ofInjective (Q.potentialCyclicClass k)
    (Q.potentialCyclicClass_injective k)).symm.toLinearMap.comp
      (((algebraCyclicEquiv k E.val).toLinearMap.comp (Q.potentialCyclicClass k)).codRestrict
        _ (VertexCutPathAutomorphism.cyclicEquiv_potential_mem_range Q k E))

theorem VertexCutPathAutomorphism.potentialLinearMap_cyclicClass
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) :
    Q.potentialCyclicClass k (VertexCutPathAutomorphism.potentialLinearMap Q k E φ) =
      E • Q.potentialCyclicClass k φ := by
  exact LinearEquiv.ofInjective_symm_apply (Q.potentialCyclicClass k) _

noncomputable def VertexCutPathAutomorphism.potentialLinearEquiv
    (E : Q.VertexCutPathAutomorphism k) : Q.Potential k ≃ₗ[k] Q.Potential k where
  __ := VertexCutPathAutomorphism.potentialLinearMap Q k E
  invFun := VertexCutPathAutomorphism.potentialLinearMap Q k (E⁻¹)
  left_inv := by
    intro φ
    apply Q.potentialCyclicClass_injective k
    change Q.potentialCyclicClass k
      (VertexCutPathAutomorphism.potentialLinearMap Q k (E⁻¹)
        (VertexCutPathAutomorphism.potentialLinearMap Q k E φ)) = Q.potentialCyclicClass k φ
    rw [VertexCutPathAutomorphism.potentialLinearMap_cyclicClass,
      VertexCutPathAutomorphism.potentialLinearMap_cyclicClass,inv_smul_smul]
  right_inv := by
    intro φ
    apply Q.potentialCyclicClass_injective k
    change Q.potentialCyclicClass k
      (VertexCutPathAutomorphism.potentialLinearMap Q k E
        (VertexCutPathAutomorphism.potentialLinearMap Q k (E⁻¹) φ)) = Q.potentialCyclicClass k φ
    rw [VertexCutPathAutomorphism.potentialLinearMap_cyclicClass,
      VertexCutPathAutomorphism.potentialLinearMap_cyclicClass,smul_inv_smul]

theorem VertexCutPathAutomorphism.potentialLinearEquiv_cyclicClass
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) :
    Q.potentialCyclicClass k (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ) =
      E • Q.potentialCyclicClass k φ :=
  VertexCutPathAutomorphism.potentialLinearMap_cyclicClass Q k E φ

noncomputable def vertexCutPotentialAutomorphismHom :
    Q.VertexCutPathAutomorphism k →* (Q.Potential k ≃ₗ[k] Q.Potential k) where
  toFun := VertexCutPathAutomorphism.potentialLinearEquiv Q k
  map_one' := by
    apply LinearEquiv.ext
    intro φ
    apply Q.potentialCyclicClass_injective k
    rw [VertexCutPathAutomorphism.potentialLinearEquiv_cyclicClass,one_smul]
    rfl
  map_mul' E F := by
    apply LinearEquiv.ext
    intro φ
    apply Q.potentialCyclicClass_injective k
    change Q.potentialCyclicClass k
      (VertexCutPathAutomorphism.potentialLinearEquiv Q k (E*F) φ) =
      Q.potentialCyclicClass k (VertexCutPathAutomorphism.potentialLinearEquiv Q k E
        (VertexCutPathAutomorphism.potentialLinearEquiv Q k F φ))
    rw [VertexCutPathAutomorphism.potentialLinearEquiv_cyclicClass,
      VertexCutPathAutomorphism.potentialLinearEquiv_cyclicClass,
      VertexCutPathAutomorphism.potentialLinearEquiv_cyclicClass,mul_smul]

noncomputable instance vertexCutPotentialMulAction :
    MulAction (Q.VertexCutPathAutomorphism k) (Q.Potential k) where
  smul E φ := VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ
  one_smul φ := congrArg (fun E : Q.Potential k ≃ₗ[k] Q.Potential k => E φ)
    (Q.vertexCutPotentialAutomorphismHom k).map_one
  mul_smul E F φ := congrArg (fun E : Q.Potential k ≃ₗ[k] Q.Potential k => E φ)
    ((Q.vertexCutPotentialAutomorphismHom k).map_mul E F)

theorem potentialCyclicClass_vertexCut_smul
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) :
    Q.potentialCyclicClass k (E • φ) = E • Q.potentialCyclicClass k φ :=
  VertexCutPathAutomorphism.potentialLinearEquiv_cyclicClass Q k E φ

end ASGinzburg.CutQuiver
