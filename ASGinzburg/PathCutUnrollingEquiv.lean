import ASGinzburg.PathCutGrading
import ASGinzburg.UnrolledPathWords

/-! A fixed cut homogeneous component is linearly equivalent to the
actual fixed-sheet path space, before quotienting by relations. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

def Path.castCutDegreeEquiv (u v : Q.Vertex) (d : ℕ) :
    {p : Q.Path u v // (p.cutDegree:ℤ)=(d:ℤ)} ≃ Path.CutDegreePath (Q:=Q) u v d where
  toFun p := ⟨p.val,by exact_mod_cast p.property⟩
  invFun p := ⟨p.val,by exact_mod_cast p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

universe u
variable (k : Type u) [Field k]

noncomputable def pathCutComponentBasisEquiv (u v : Q.Vertex) (d : ℕ) :
    Q.pathCutComponent k u v (d:ℤ) ≃ₗ[k] (Path.CutDegreePath (Q:=Q) u v d →₀ k) :=
  (Finsupp.supportedEquivFinsupp (M:=k) (R:=k)
    {p : Q.Path u v | (p.cutDegree:ℤ)=(d:ℤ)}).trans
      (Finsupp.domLCongr (Path.castCutDegreeEquiv Q u v d))

noncomputable def pathCutUnrollingEquiv (u v : Q.Vertex) (d : ℕ) (m : ℤ) :
    Q.pathCutComponent k u v (d:ℤ) ≃ₗ[k]
      Q.UnrolledPathComponent k (u,m) (v,m+(d:ℤ)) :=
  (Q.pathCutComponentBasisEquiv k u v d).trans (Q.unrollDegreeLinearEquiv k u v d m)

theorem unrollDegreeLinearEquiv_eq_map (u v : Q.Vertex) (d : ℕ) (m : ℤ) :
    (Q.unrollDegreeLinearEquiv k u v d m).toLinearMap=Q.unrollDegreeLinearMap k u v d m := by
  classical
  apply LinearMap.ext
  intro f
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add,hf,hg]
  | single p a =>
    change Q.unrollDegreeLinearEquiv k u v d m (Finsupp.single p a)=_
    rw [Q.unrollDegreeLinearEquiv_single]
    exact Finsupp.mapDomain_single.symm

end ASGinzburg.CutQuiver
