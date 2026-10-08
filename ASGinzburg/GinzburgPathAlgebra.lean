import ASGinzburg.GinzburgPaths
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! Actual bilinear multiplication on the extended path spaces and closure
of homogeneous components under composition. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

abbrev GinzburgPathComponent (u v : Q.Vertex) := Q.GinzburgPath u v →₀ k

noncomputable def ginzburgPathComp {u v w : Q.Vertex} :
    Q.GinzburgPathComponent k v w →ₗ[k] Q.GinzburgPathComponent k u v →ₗ[k]
      Q.GinzburgPathComponent k u w :=
  Finsupp.linearCombination k (fun q =>
    Finsupp.linearCombination k (fun p => Finsupp.single (p.comp q) 1))

@[simp] theorem ginzburgPathComp_single {u v w : Q.Vertex}
    (p : Q.GinzburgPath u v) (q : Q.GinzburgPath v w) (a b : k) :
    Q.ginzburgPathComp k (Finsupp.single q b) (Finsupp.single p a)=
      Finsupp.single (p.comp q) (b*a) := by
  simp [ginzburgPathComp,LinearMap.smul_apply,Finsupp.smul_single,smul_eq_mul]

noncomputable def ginzburgPathId (v : Q.Vertex) : Q.GinzburgPathComponent k v v :=
  Finsupp.single (.nil v) 1

theorem ginzburgPathComp_id {u v : Q.Vertex} (f : Q.GinzburgPathComponent k u v) :
    Q.ginzburgPathComp k (Q.ginzburgPathId k v) f=f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add,hf,hg]
  | single p c => simp [ginzburgPathId]

theorem id_ginzburgPathComp {u v : Q.Vertex} (f : Q.GinzburgPathComponent k u v) :
    Q.ginzburgPathComp k f (Q.ginzburgPathId k u)=f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add,LinearMap.add_apply,hf,hg]
  | single p c => simp [ginzburgPathId]

theorem ginzburgPathComp_assoc {u v w x : Q.Vertex}
    (f : Q.GinzburgPathComponent k u v) (g : Q.GinzburgPathComponent k v w)
    (h : Q.GinzburgPathComponent k w x) :
    Q.ginzburgPathComp k h (Q.ginzburgPathComp k g f)=
      Q.ginzburgPathComp k (Q.ginzburgPathComp k h g) f := by
  classical
  induction h using Finsupp.induction_linear with
  | zero => simp
  | add h h' ih ih' => simp [map_add,LinearMap.add_apply,ih,ih']
  | single r c =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' ih ih' => simp [map_add,ih,ih']
    | single q b =>
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f f' ih ih' => simp [map_add,ih,ih']
      | single p a => simp [GinzburgPath.comp_assoc,mul_assoc]

def ginzburgHomogeneousComponent (u v : Q.Vertex) (q c w : ℤ) :
    Submodule k (Q.GinzburgPathComponent k u v) :=
  Finsupp.supported k k {p |p.cohomologicalDegree=q ∧ p.cutDegree=c ∧ p.winding=w}

theorem ginzburgHomogeneousComponent_comp {u v x : Q.Vertex} {q c w q' c' w' : ℤ}
    {f : Q.GinzburgPathComponent k u v} (hf : f ∈ Q.ginzburgHomogeneousComponent k u v q c w)
    {g : Q.GinzburgPathComponent k v x} (hg : g ∈ Q.ginzburgHomogeneousComponent k v x q' c' w') :
    Q.ginzburgPathComp k g f ∈ Q.ginzburgHomogeneousComponent k u x (q+q') (c+c') (w+w') := by
  change f ∈ Finsupp.supported k k _ at hf
  change g ∈ Finsupp.supported k k _ at hg
  rw [Finsupp.supported_eq_span_single] at hf hg
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r,hr,rfl⟩ := hy
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p,hp,rfl⟩ := hy
      rw [Q.ginzburgPathComp_single]
      apply Finsupp.single_mem_supported
      exact ⟨by rw [GinzburgPath.cohomologicalDegree_comp,hp.1,hr.1],
        by rw [GinzburgPath.cutDegree_comp,hp.2.1,hr.2.1],
        by rw [GinzburgPath.winding_comp,hp.2.2,hr.2.2]⟩
    | zero => simp
    | add f h hf hh ihf ihh => simpa only [map_add] using Submodule.add_mem _ ihf ihh
    | smul a f hf ih => simpa only [map_smul] using Submodule.smul_mem _ a ih
  | zero => simp
  | add g h hg hh ihg ihh =>
    simpa only [map_add,LinearMap.add_apply] using Submodule.add_mem _ ihg ihh
  | smul a g hg ih =>
    simpa only [map_smul,LinearMap.smul_apply] using Submodule.smul_mem _ a ih

end ASGinzburg.CutQuiver
