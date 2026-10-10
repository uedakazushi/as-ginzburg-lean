import ASGinzburg.VertexCutPathAutomorphisms
import ASGinzburg.FiniteComponentAutomorphismCorners

/-! Fixing the actual vertices and preserving the actual cut grading
forces preservation of each path corner and its winding grading. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathRingCutSubspace_component_iff (i j : Q.Vertex)
    (f : Q.PathComponent k i j) (c : ℤ) :
    (Q.pathComponentAlgebra k).totalComponent i j f ∈ Q.pathRingCutSubspace k c ↔
      f ∈ Q.pathCutComponent k i j c := by
  constructor
  · intro h
    simpa only [LinearComponentAlgebra.totalComponent_apply_same] using h i j
  · intro h p q
    classical
    by_cases hp : p=i
    · subst p
      by_cases hq : q=j
      · subst q
        simpa only [LinearComponentAlgebra.totalComponent_apply_same] using h
      · simp [LinearComponentAlgebra.totalComponent,hq]
    · rw [LinearComponentAlgebra.totalComponent_apply_source_ne _ _ _ _ _ _ hp]
      exact (Q.pathCutComponent k p q c).zero_mem

noncomputable def VertexCutPathAutomorphism.componentLinearEquiv
    (E : Q.VertexCutPathAutomorphism k) (i j : Q.Vertex) :
    Q.PathComponent k i j ≃ₗ[k] Q.PathComponent k i j :=
  (Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv E.val
    (VertexCutPathAutomorphism.fixes_vertex Q k E) i j

theorem VertexCutPathAutomorphism.component_preserves_cut
    (E : Q.VertexCutPathAutomorphism k) (i j : Q.Vertex) (c : ℤ)
    (f : Q.PathComponent k i j) :
    f ∈ Q.pathCutComponent k i j c ↔
      VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f ∈
        Q.pathCutComponent k i j c := by
  rw [← Q.pathRingCutSubspace_component_iff k i j f c,
    ← Q.pathRingCutSubspace_component_iff k i j
      (VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f) c]
  rw [show (Q.pathComponentAlgebra k).totalComponent i j
      (VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f) =
      E.val ((Q.pathComponentAlgebra k).totalComponent i j f) from
    (Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_component E.val
      (VertexCutPathAutomorphism.fixes_vertex Q k E) i j f]
  exact VertexCutPathAutomorphism.preserves_cut Q k E c _

def pathWindingComponent (i j : Q.Vertex) (d : ℤ) : Submodule k (Q.PathComponent k i j) :=
  Finsupp.supported k k {p | p.winding=d}

theorem pathCutComponent_le_winding (i j : Q.Vertex) (c : ℤ) :
    Q.pathCutComponent k i j c ≤
      Q.pathWindingComponent k i j ((j.val:ℤ)-i.val+Q.vertices*c) := by
  apply Finsupp.supported_mono
  intro p hp
  change (p.cutDegree:ℤ)=c at hp
  change p.winding=_
  rw [p.winding_eq,hp]

theorem VertexCutPathAutomorphism.component_map_winding_mem
    (E : Q.VertexCutPathAutomorphism k) (i j : Q.Vertex) (d : ℤ)
    (f : Q.PathComponent k i j) (hf : f ∈ Q.pathWindingComponent k i j d) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f ∈
      Q.pathWindingComponent k i j d := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p,hp,rfl⟩ := hx
      have hc : Finsupp.single p 1 ∈ Q.pathCutComponent k i j (p.cutDegree:ℤ) :=
        Finsupp.single_mem_supported k 1 rfl
      have hec := (VertexCutPathAutomorphism.component_preserves_cut Q k E i j
        (p.cutDegree:ℤ) _).mp hc
      change p.winding=d at hp
      rw [← hp,p.winding_eq]
      exact Q.pathCutComponent_le_winding k i j (p.cutDegree:ℤ) hec
  | zero => simpa only [map_zero] using (Q.pathWindingComponent k i j d).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (Q.pathWindingComponent k i j d).add_mem ihx ihy
  | smul a x hx ih =>
      simpa only [map_smul] using (Q.pathWindingComponent k i j d).smul_mem a ih

theorem VertexCutPathAutomorphism.componentLinearEquiv_inv
    (E : Q.VertexCutPathAutomorphism k) (i j : Q.Vertex) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) i j =
      (VertexCutPathAutomorphism.componentLinearEquiv Q k E i j).symm := by
  apply LinearEquiv.ext
  intro f
  rfl

theorem VertexCutPathAutomorphism.component_preserves_winding
    (E : Q.VertexCutPathAutomorphism k) (i j : Q.Vertex) (d : ℤ)
    (f : Q.PathComponent k i j) :
    f ∈ Q.pathWindingComponent k i j d ↔
      VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f ∈
        Q.pathWindingComponent k i j d := by
  constructor
  · exact VertexCutPathAutomorphism.component_map_winding_mem Q k E i j d f
  · intro hf
    have h := VertexCutPathAutomorphism.component_map_winding_mem Q k (E⁻¹) i j d
      (VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f) hf
    rw [VertexCutPathAutomorphism.componentLinearEquiv_inv] at h
    simpa only [LinearEquiv.symm_apply_apply] using h

theorem VertexCutPathAutomorphism.componentLinearEquiv_projection
    (E : Q.VertexCutPathAutomorphism k) (i j : Q.Vertex) (x : Q.PathRing k) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k E i j (x i j) = E.val x i j := by
  change E.val ((Q.pathComponentAlgebra k).totalComponent i j (x i j)) i j = E.val x i j
  have h := congrArg (fun z : Q.PathRing k => z i j)
    ((Q.pathComponentAlgebra k).totalAlgEquiv_component_projection E.val
      (VertexCutPathAutomorphism.fixes_vertex Q k E) i j x)
  simpa only [LinearComponentAlgebra.totalComponent_apply_same] using h

noncomputable def pathRingWindingSubspace (d : ℤ) : Submodule k (Q.PathRing k) where
  carrier := {x | ∀ i j, x i j ∈ Q.pathWindingComponent k i j d}
  zero_mem' := fun i j => (Q.pathWindingComponent k i j d).zero_mem
  add_mem' := fun hx hy i j => (Q.pathWindingComponent k i j d).add_mem (hx i j) (hy i j)
  smul_mem' := fun a _ hx i j => (Q.pathWindingComponent k i j d).smul_mem a (hx i j)

theorem VertexCutPathAutomorphism.map_winding_mem
    (E : Q.VertexCutPathAutomorphism k) (d : ℤ) (x : Q.PathRing k)
    (hx : x ∈ Q.pathRingWindingSubspace k d) :
    E.val x ∈ Q.pathRingWindingSubspace k d := by
  intro i j
  have h := VertexCutPathAutomorphism.component_map_winding_mem Q k E i j d (x i j) (hx i j)
  rw [VertexCutPathAutomorphism.componentLinearEquiv_projection] at h
  exact h

theorem VertexCutPathAutomorphism.preserves_winding
    (E : Q.VertexCutPathAutomorphism k) (d : ℤ) (x : Q.PathRing k) :
    x ∈ Q.pathRingWindingSubspace k d ↔ E.val x ∈ Q.pathRingWindingSubspace k d := by
  constructor
  · exact VertexCutPathAutomorphism.map_winding_mem Q k E d x
  · intro hx
    have h := VertexCutPathAutomorphism.map_winding_mem Q k (E⁻¹) d (E.val x) hx
    change E.val.symm (E.val x) ∈ Q.pathRingWindingSubspace k d at h
    simpa only [AlgEquiv.symm_apply_apply] using h

end ASGinzburg.CutQuiver
