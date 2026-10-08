import ASGinzburg.ASPathPresentation

/-! Bilinear multiplication on the actual unrolled path components and
multiplicativity of the AS evaluation. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

abbrev UnrolledPathComponent (u v : Q.LiftVertex) := Q.UnrolledPath u v →₀ k

noncomputable def unrolledPathComp {u v w : Q.LiftVertex} :
    Q.UnrolledPathComponent k v w →ₗ[k] Q.UnrolledPathComponent k u v →ₗ[k]
      Q.UnrolledPathComponent k u w :=
  Finsupp.linearCombination k (fun q =>
    Finsupp.linearCombination k (fun p => Finsupp.single (p.comp q) 1))

noncomputable def unrolledPathId (v : Q.LiftVertex) : Q.UnrolledPathComponent k v v :=
  Finsupp.single (.nil v) 1

@[simp] theorem unrolledPathComp_single {u v w : Q.LiftVertex}
    (p : Q.UnrolledPath u v) (q : Q.UnrolledPath v w) (a b : k) :
    Q.unrolledPathComp k (Finsupp.single q b) (Finsupp.single p a) =
      Finsupp.single (p.comp q) (b * a) := by
  simp [unrolledPathComp,LinearMap.smul_apply,Finsupp.smul_single,smul_eq_mul]

theorem unrolledPathComp_id {u v : Q.LiftVertex} (f : Q.UnrolledPathComponent k u v) :
    Q.unrolledPathComp k (Q.unrolledPathId k v) f = f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add,hf,hg]
  | single p a => simp [unrolledPathId]

theorem id_unrolledPathComp {u v : Q.LiftVertex} (f : Q.UnrolledPathComponent k u v) :
    Q.unrolledPathComp k f (Q.unrolledPathId k u) = f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add,LinearMap.add_apply,hf,hg]
  | single p a => simp [unrolledPathId]

theorem unrolledPathComp_assoc {u v w x : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k u v) (g : Q.UnrolledPathComponent k v w)
    (h : Q.UnrolledPathComponent k w x) :
    Q.unrolledPathComp k h (Q.unrolledPathComp k g f) =
      Q.unrolledPathComp k (Q.unrolledPathComp k h g) f := by
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
      | single p a => simp [UnrolledPath.comp_assoc,mul_assoc]

end ASGinzburg.CutQuiver

namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
variable (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

theorem unrolledPathLinearEvaluation_id (v : Q.LiftVertex) :
    A.unrolledPathLinearEvaluation Q R v v (Q.unrolledPathId k v) = A.id (Q.height v) := by
  simp [CutQuiver.unrolledPathId,unrolledPathEvaluation]

theorem unrolledPathLinearEvaluation_comp {u v w : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k u v) (g : Q.UnrolledPathComponent k v w) :
    A.unrolledPathLinearEvaluation Q R u w (Q.unrolledPathComp k g f) =
      A.comp (A.unrolledPathLinearEvaluation Q R v w g)
        (A.unrolledPathLinearEvaluation Q R u v f) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' => simp [map_add,LinearMap.add_apply,hg,hg']
  | single q b =>
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f f' hf hf' => simp [map_add,hf,hf']
    | single p a =>
      simp [A.unrolledPathEvaluation_comp,LinearMap.smul_apply,smul_smul,mul_comm]

end ASGinzburg.ZAlgebra
