import ASGinzburg.UnrolledPathWords
import ASGinzburg.UnrolledPathAlgebra
import ASGinzburg.PathCutGrading

/-! Forgetting sheets preserves genuine path composition and its linear
extension, while retaining the cut degree determined by the endpoints. -/
namespace ASGinzburg.CutQuiver
variable {Q : CutQuiver}

theorem Path.comp_transport_target {u v w w' : Q.Vertex} (h : w=w')
    (p : Q.Path u v) (q : Q.Path v w) :
    p.comp (q.transport rfl h)=(p.comp q).transport rfl h := by
  subst w'
  rfl

theorem UnrolledPath.erase_comp {u v w : Q.LiftVertex}
    (p : Q.UnrolledPath u v) (q : Q.UnrolledPath v w) :
    (p.comp q).erase=p.erase.comp q.erase := by
  induction q with
  | nil => simp [comp,erase]
  | snoc a q ih => simp [comp,erase,Path.comp_transport_target,Path.comp,ih]

universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def unrolledPathEraseLinearMap (u v : Q.LiftVertex) :
    Q.UnrolledPathComponent k u v →ₗ[k] Q.PathComponent k u.1 v.1 :=
  Finsupp.lmapDomain k k UnrolledPath.erase

@[simp] theorem unrolledPathEraseLinearMap_single {u v : Q.LiftVertex}
    (p : Q.UnrolledPath u v) (a : k) :
    Q.unrolledPathEraseLinearMap k u v (Finsupp.single p a)=Finsupp.single p.erase a :=
  Finsupp.mapDomain_single

theorem unrolledPathEraseLinearMap_injective (u v : Q.LiftVertex) :
    Function.Injective (Q.unrolledPathEraseLinearMap k u v) := by
  apply Finsupp.mapDomain_injective
  intro p q h
  apply UnrolledPath.erase_toList_injective
  exact congrArg Path.toList h

theorem unrolledPathEraseLinearMap_cut {u v : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k u v) :
    Q.unrolledPathEraseLinearMap k u v f ∈ Q.pathCutComponent k u.1 v.1 (v.2-u.2) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | single p a =>
    rw [unrolledPathEraseLinearMap_single]
    exact Finsupp.single_mem_supported _ _ p.erase_cutDegree

theorem unrolledPathEraseLinearMap_comp {u v w : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k u v) (g : Q.UnrolledPathComponent k v w) :
    Q.unrolledPathEraseLinearMap k u w (Q.unrolledPathComp k g f)=
      Q.pathComp k (Q.unrolledPathEraseLinearMap k v w g)
        (Q.unrolledPathEraseLinearMap k u v f) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g h hg hh => simp [map_add,LinearMap.add_apply,hg,hh]
  | single q b =>
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f h hf hh => simp [map_add,hf,hh]
    | single p a => simp [UnrolledPath.erase_comp]

end ASGinzburg.CutQuiver
