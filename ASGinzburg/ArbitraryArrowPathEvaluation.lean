import ASGinzburg.UnrolledPathPresentationMorphism

/-! The actual free unrolled path algebra evaluates multiplicatively
under any concrete incoming-arrow family, independent of AS differentials. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

abbrev IncomingElementFamily := ∀ (w : Q.LiftVertex) (a : Q.incomingArrows w),
  A.Hom (Q.height (Q.incomingSource w a)) (Q.height w)

variable (G : A.IncomingElementFamily Q)

noncomputable def arrowPathEvaluation (G : A.IncomingElementFamily Q) :
    {i j : Q.LiftVertex} → Q.UnrolledPath i j → A.Hom (Q.height i) (Q.height j)
  | _, _, .nil w => A.id (Q.height w)
  | _, w, .snoc a p => A.comp (G w a) (arrowPathEvaluation G p)

theorem arrowPathEvaluation_comp {u v w : Q.LiftVertex}
    (p : Q.UnrolledPath u v) (q : Q.UnrolledPath v w) :
    A.arrowPathEvaluation Q G (p.comp q) =
      A.comp (A.arrowPathEvaluation Q G q) (A.arrowPathEvaluation Q G p) := by
  induction q with
  | nil => simp [CutQuiver.UnrolledPath.comp,arrowPathEvaluation,A.comp_id]
  | snoc a q ih => simp only [CutQuiver.UnrolledPath.comp,arrowPathEvaluation,ih,A.comp_assoc]

noncomputable def arrowPathLinearEvaluation (u v : Q.LiftVertex) :
    (Q.UnrolledPath u v →₀ k) →ₗ[k] A.Hom (Q.height u) (Q.height v) :=
  Finsupp.linearCombination k (A.arrowPathEvaluation Q G)

@[simp] theorem arrowPathLinearEvaluation_single {u v : Q.LiftVertex}
    (p : Q.UnrolledPath u v) (c : k) :
    A.arrowPathLinearEvaluation Q G u v (Finsupp.single p c) =
      c • A.arrowPathEvaluation Q G p := by
  simp [arrowPathLinearEvaluation]

theorem arrowPathLinearEvaluation_snoc {u v : Q.LiftVertex}
    (a : Q.incomingArrows v) (p : Q.UnrolledPath u (Q.incomingSource v a) →₀ k) :
    A.arrowPathLinearEvaluation Q G u v
      (p.mapDomain (CutQuiver.UnrolledPath.snoc a)) =
      A.comp (G v a)
        (A.arrowPathLinearEvaluation Q G u (Q.incomingSource v a) p) := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [Finsupp.mapDomain_add,map_add,hp,hq]
  | single p c => simp [arrowPathEvaluation,Finsupp.mapDomain_single]

theorem arrowPathLinearEvaluation_id (v : Q.LiftVertex) :
    A.arrowPathLinearEvaluation Q G v v (Q.unrolledPathId k v) = A.id (Q.height v) := by
  simp [CutQuiver.unrolledPathId,arrowPathEvaluation]

theorem arrowPathLinearEvaluation_comp {u v w : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k u v) (g : Q.UnrolledPathComponent k v w) :
    A.arrowPathLinearEvaluation Q G u w (Q.unrolledPathComp k g f) =
      A.comp (A.arrowPathLinearEvaluation Q G v w g)
        (A.arrowPathLinearEvaluation Q G u v f) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' => simp [map_add,LinearMap.add_apply,hg,hg']
  | single q b =>
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f f' hf hf' => simp [map_add,hf,hf']
    | single p a =>
      simp [A.arrowPathEvaluation_comp,LinearMap.smul_apply,smul_smul,mul_comm]

end ASGinzburg.ZAlgebra
