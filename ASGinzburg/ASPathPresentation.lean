import ASGinzburg.ASGenerators
import ASGinzburg.PathAlgebra

/-! Actual directed paths in the unrolled quiver and their evaluation through
coefficients of the finite AS resolution. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

inductive UnrolledPath : Q.LiftVertex → Q.LiftVertex → Type
  | nil (v : Q.LiftVertex) : UnrolledPath v v
  | snoc {u v : Q.LiftVertex} (a : Q.incomingArrows v)
      (p : UnrolledPath u (Q.incomingSource v a)) : UnrolledPath u v

namespace UnrolledPath
variable {Q}

def comp {u v w : Q.LiftVertex} (p : Q.UnrolledPath u v) :
    Q.UnrolledPath v w → Q.UnrolledPath u w
  | .nil _ => p
  | .snoc a q => .snoc a (comp p q)

@[simp] theorem comp_nil {u v : Q.LiftVertex} (p : Q.UnrolledPath u v) :
    p.comp (.nil v) = p := rfl

@[simp] theorem nil_comp {u v : Q.LiftVertex} (p : Q.UnrolledPath u v) :
    (UnrolledPath.nil u).comp p = p := by
  induction p with
  | nil => rfl
  | snoc a p ih => simp [comp,ih]

theorem comp_assoc {u v w z : Q.LiftVertex} (p : Q.UnrolledPath u v)
    (q : Q.UnrolledPath v w) (r : Q.UnrolledPath w z) :
    (p.comp q).comp r = p.comp (q.comp r) := by
  induction r with
  | nil => rfl
  | snoc a r ih => simp [comp,ih]

end UnrolledPath
end ASGinzburg.CutQuiver

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
variable (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

noncomputable def unrolledPathEvaluation (R : ∀ w : Q.LiftVertex, A.ASResolution Q w) :
    {i j : Q.LiftVertex} → Q.UnrolledPath i j → A.Hom (Q.height i) (Q.height j)
  | _, _, .nil w => A.id (Q.height w)
  | _, w, .snoc a p => A.comp ((R w).incomingElement a) (unrolledPathEvaluation R p)

theorem unrolledPathEvaluation_comp {u v w : Q.LiftVertex}
    (p : Q.UnrolledPath u v) (q : Q.UnrolledPath v w) :
    A.unrolledPathEvaluation Q R (p.comp q) =
      A.comp (A.unrolledPathEvaluation Q R q) (A.unrolledPathEvaluation Q R p) := by
  induction q with
  | nil => simp [CutQuiver.UnrolledPath.comp,unrolledPathEvaluation,A.comp_id]
  | snoc a q ih => simp only [CutQuiver.UnrolledPath.comp,unrolledPathEvaluation,ih,A.comp_assoc]

noncomputable def unrolledPathLinearEvaluation (u v : Q.LiftVertex) :
    (Q.UnrolledPath u v →₀ k) →ₗ[k] A.Hom (Q.height u) (Q.height v) :=
  Finsupp.linearCombination k (A.unrolledPathEvaluation Q R)

@[simp] theorem unrolledPathLinearEvaluation_single {u v : Q.LiftVertex}
    (p : Q.UnrolledPath u v) (c : k) :
    A.unrolledPathLinearEvaluation Q R u v (Finsupp.single p c) =
      c • A.unrolledPathEvaluation Q R p := by
  simp [unrolledPathLinearEvaluation]

theorem unrolledPathLinearEvaluation_snoc {u v : Q.LiftVertex}
    (a : Q.incomingArrows v) (p : Q.UnrolledPath u (Q.incomingSource v a) →₀ k) :
    A.unrolledPathLinearEvaluation Q R u v
      (p.mapDomain (CutQuiver.UnrolledPath.snoc a)) =
      A.comp ((R v).incomingElement a)
        (A.unrolledPathLinearEvaluation Q R u (Q.incomingSource v a) p) := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [Finsupp.mapDomain_add,map_add,hp,hq]
  | single p c => simp [unrolledPathEvaluation,Finsupp.mapDomain_single]

theorem unrolledPathLinearEvaluation_surjective (u v : Q.LiftVertex) :
    Function.Surjective (A.unrolledPathLinearEvaluation Q R u v) := by
  have hmain : ∀ d : ℕ, ∀ u v : Q.LiftVertex, (Q.height v - Q.height u).toNat = d →
      ∀ f : A.Hom (Q.height u) (Q.height v),
        f ∈ LinearMap.range (A.unrolledPathLinearEvaluation Q R u v) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro u v hd f
      rcases lt_trichotomy (Q.height v) (Q.height u) with hlt | heq | hlt
      · rw [A.positive hlt f]
        exact (LinearMap.range _).zero_mem
      · have hvu := Q.height_bijective.injective heq
        subst v
        obtain ⟨c,rfl⟩ := A.connected (Q.height u) f
        exact ⟨Finsupp.single (.nil u) c, by simp [unrolledPathEvaluation]⟩
      · obtain ⟨x,rfl⟩ := (R v).incomingMultiplication_surjective (Q.height u) hlt f
        induction x using DirectSum.induction_on with
        | zero => simpa only [map_zero] using (LinearMap.range
            (A.unrolledPathLinearEvaluation Q R u v)).zero_mem
        | add x y hx hy => simpa only [map_add] using
            (LinearMap.range (A.unrolledPathLinearEvaluation Q R u v)).add_mem hx hy
        | of a x =>
          change ((R v).incomingMultiplication (Q.height u))
            (DirectSum.lof k (Q.incomingArrows v)
              (fun a => A.Hom (Q.height u) (Q.height (Q.incomingSource v a))) a x) ∈ _
          simp only [ASResolution.incomingMultiplication,DirectSum.toModule_lof]
          obtain ⟨p,hp⟩ := ih (Q.height (Q.incomingSource v a) - Q.height u).toNat
            (by have := Q.incomingSource_height_lt v a; omega)
            u (Q.incomingSource v a) rfl x
          exact ⟨p.mapDomain (CutQuiver.UnrolledPath.snoc a), by
            rw [A.unrolledPathLinearEvaluation_snoc,hp]⟩
  intro f
  exact hmain (Q.height v - Q.height u).toNat u v rfl f

end ASGinzburg.ZAlgebra
