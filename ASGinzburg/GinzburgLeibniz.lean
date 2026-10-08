import ASGinzburg.GinzburgPathDifferential

/-! The genuine signed Leibniz rule on the extended free path algebra. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgSignMap (u v : Q.Vertex) :
    Q.GinzburgPathComponent k u v →ₗ[k] Q.GinzburgPathComponent k u v :=
  Finsupp.linearCombination k (fun p => ginzburgSign k p.cohomologicalDegree • Finsupp.single p 1)

@[simp] theorem ginzburgSignMap_single {u v : Q.Vertex} (p : Q.GinzburgPath u v) (c : k) :
    Q.ginzburgSignMap k u v (Finsupp.single p c)=
      ginzburgSign k p.cohomologicalDegree • Finsupp.single p c := by
  simp [ginzburgSignMap,mul_comm,Finsupp.smul_single,smul_eq_mul]

theorem GinzburgPath.differential_comp (φ : Q.Potential k) {u v w : Q.Vertex}
    (p : Q.GinzburgPath u v) (q : Q.GinzburgPath v w) :
    (p.comp q).differential Q k φ=
      Q.ginzburgPathComp k (q.differential Q k φ) (Finsupp.single p 1)+
      ginzburgSign k q.cohomologicalDegree •
        Q.ginzburgPathComp k (Finsupp.single q 1) (p.differential Q k φ) := by
  induction q with
  | nil =>
    simpa only [cohomologicalDegree,comp_nil,differential_nil,ginzburgSign_zero,one_smul,
      map_zero,LinearMap.zero_apply,zero_add,ginzburgPathId] using (Q.ginzburgPathComp_id k (p.differential Q k φ)).symm
  | snoc q a h ih =>
    subst h
    have hpq : Finsupp.single (p.comp q) (1:k)=
        Q.ginzburgPathComp k (Finsupp.single q 1) (Finsupp.single p 1) := by simp
    have hqa : Finsupp.single (GinzburgPath.snoc q a rfl) (1:k)=
        Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1) (Finsupp.single q 1) := by
      simp [ginzburgArrowPath,comp]
    simp only [comp,differential,ih,cohomologicalDegree]
    rw [hpq,hqa]
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      ginzburgPathComp_assoc,ginzburgSign_add,smul_add,smul_smul,mul_comm,add_assoc]

set_option maxHeartbeats 800000 in
theorem ginzburgDifferential_comp (φ : Q.Potential k) {u v w : Q.Vertex}
    (f : Q.GinzburgPathComponent k u v) (g : Q.GinzburgPathComponent k v w) :
    Q.ginzburgDifferential k φ u w (Q.ginzburgPathComp k g f)=
      Q.ginzburgPathComp k (Q.ginzburgDifferential k φ v w g) f+
      Q.ginzburgPathComp k (Q.ginzburgSignMap k v w g) (Q.ginzburgDifferential k φ u v f) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g h hg hh =>
    simp only [map_add,LinearMap.add_apply,hg,hh]
    abel
  | single q b =>
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f h hf hh =>
      simp only [map_add,hf,hh]
      abel
    | single p a =>
      have hp : Finsupp.single p a=a • Finsupp.single p (1:k) := by simp
      have hq : Finsupp.single q b=b • Finsupp.single q (1:k) := by simp
      rw [hp,hq]
      simp only [map_smul,LinearMap.smul_apply,ginzburgPathComp_single,
        ginzburgDifferential_single,ginzburgSignMap_single,one_smul,mul_one,smul_smul]
      rw [GinzburgPath.differential_comp]
      simp only [smul_add,smul_smul,mul_assoc,mul_left_comm]

end ASGinzburg.CutQuiver
