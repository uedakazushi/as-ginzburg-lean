import ASGinzburg.PathUnrolling
import ASGinzburg.UnrolledPathIdeals

/-! Actual linear reindexing between lifted vertices and the integer-indexed
free path Z-algebra, preserving the path-length filtration. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

@[simp] theorem heightEquiv_symm_height (v : Q.LiftVertex) :
    Q.heightEquiv.symm (Q.height v)=v := by
  rw [←Q.heightEquiv_apply]
  exact Q.heightEquiv.symm_apply_apply v

def UnrolledPath.endpointEquiv {u v u' v' : Q.LiftVertex}
    (hu : u=u') (hv : v=v') : Q.UnrolledPath u v ≃ Q.UnrolledPath u' v' where
  toFun := UnrolledPath.transport hu hv
  invFun := UnrolledPath.transport hu.symm hv.symm
  left_inv := by subst u' v'; intro p; rfl
  right_inv := by subst u' v'; intro p; rfl

def unrolledPathHeightEquiv (u v : Q.LiftVertex) :
    Q.UnrolledPath u v ≃
      Q.UnrolledPath (Q.heightEquiv.symm (Q.height u)) (Q.heightEquiv.symm (Q.height v)) :=
  UnrolledPath.endpointEquiv Q (Q.heightEquiv_symm_height u).symm (Q.heightEquiv_symm_height v).symm

@[simp] theorem unrolledPathHeightEquiv_length (u v : Q.LiftVertex) (p : Q.UnrolledPath u v) :
    (Q.unrolledPathHeightEquiv u v p).length=p.length := by
  simp [unrolledPathHeightEquiv,UnrolledPath.endpointEquiv]

noncomputable def unrolledComponentHeightEquiv (u v : Q.LiftVertex) :
    Q.UnrolledPathComponent k u v ≃ₗ[k] (Q.unrolledPathZAlgebra k).Hom (Q.height u) (Q.height v) :=
  Finsupp.mapDomain.linearEquiv k k (Q.unrolledPathHeightEquiv u v)

@[simp] theorem unrolledComponentHeightEquiv_single (u v : Q.LiftVertex)
    (p : Q.UnrolledPath u v) (c : k) :
    Q.unrolledComponentHeightEquiv k u v (Finsupp.single p c)=
      Finsupp.single (Q.unrolledPathHeightEquiv u v p) c := by
  change Finsupp.mapDomain (Q.unrolledPathHeightEquiv u v) (Finsupp.single p c)=_
  rw [Finsupp.mapDomain_single]

theorem unrolledComponentHeightEquiv_mem_filtration (n : ℕ) {u v : Q.LiftVertex}
    {f : Q.UnrolledPathComponent k u v} (hf : f ∈ Q.unrolledPathFiltration k n u v) :
    Q.unrolledComponentHeightEquiv k u v f ∈
      (Q.unrolledPathIdeal k n).hom (Q.height u) (Q.height v) := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    rw [Q.unrolledComponentHeightEquiv_single]
    apply Finsupp.single_mem_supported
    change n ≤ (Q.unrolledPathHeightEquiv u v p).length
    rw [Q.unrolledPathHeightEquiv_length]
    exact hp
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using Submodule.smul_mem _ c ih

end ASGinzburg.CutQuiver
