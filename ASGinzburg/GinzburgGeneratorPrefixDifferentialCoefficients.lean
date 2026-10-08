import ASGinzburg.GinzburgGeneratorPrefixTopQuotient

/-! Coefficients of the actual top incoming prefix differential. The
degree transport in the mathlib complex preserves the underlying paths. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgGeneratorPrefix_eqToHom_apply_coe (u v : Q.Vertex) (r c q q' : ℤ)
    (h : q=q') (f : Q.GinzburgGeneratorPrefix k u v r q c)
    (a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r}) :
    ((eqToHom (congrArg (fun n => ModuleCat.of k (Q.GinzburgGeneratorPrefix k u v r n c)) h)
      f) a).val=(f a).val := by
  cases h
  rfl

theorem ginzburgGeneratorPrefixIncomingDifferential_apply_coe (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) (f : Q.GinzburgGeneratorPrefix k u v r (r-1) c)
    (a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r}) :
    (Q.ginzburgGeneratorPrefixIncomingDifferential k φ u v r c f a).val=
      ginzburgSign k r • Q.ginzburgDifferential k φ u (a.val.source Q) (f a).val := by
  have h : r-1+1=r := by omega
  unfold ginzburgGeneratorPrefixIncomingDifferential ginzburgGeneratorPrefixComplex
  simp only [CochainComplex.of]
  rw [dif_pos h]
  change ((eqToHom (congrArg (fun n => ModuleCat.of k
    (Q.GinzburgGeneratorPrefix k u v r n c)) h)
      (Q.ginzburgGeneratorPrefixDifferential k φ u v r (r-1) c f)) a).val=_
  rw [Q.ginzburgGeneratorPrefix_eqToHom_apply_coe k u v r c (r-1+1) r h]
  rfl

noncomputable def ginzburgGeneratorPrefixTopEquiv (u v : Q.Vertex) (r c : ℤ) :
    Q.GinzburgGeneratorPrefix k u v r r c ≃ₗ[k]
      (Π a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r},
        Q.ginzburgCutCohomologicalComponent k u (a.val.source Q) 0 (c-a.val.cutDegree Q)) :=
  LinearEquiv.piCongrRight fun _a => LinearEquiv.ofEq _ _ (by rw [sub_self])

noncomputable def ginzburgGeneratorPrefixPreviousEquiv (u v : Q.Vertex) (r c : ℤ) :
    Q.GinzburgGeneratorPrefix k u v r (r-1) c ≃ₗ[k]
      (Π a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r},
        Q.ginzburgCutCohomologicalComponent k u (a.val.source Q) (-1) (c-a.val.cutDegree Q)) :=
  LinearEquiv.piCongrRight fun _a => LinearEquiv.ofEq _ _ (by rw [show r-1-r=(-1:ℤ) by omega])

theorem ginzburgGeneratorPrefixTopEquiv_apply_coe (u v : Q.Vertex) (r c : ℤ)
    (f : Q.GinzburgGeneratorPrefix k u v r r c)
    (a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r}) :
    (Q.ginzburgGeneratorPrefixTopEquiv k u v r c f a).val=(f a).val := by
  simp only [ginzburgGeneratorPrefixTopEquiv,LinearEquiv.piCongrRight_apply,
    LinearEquiv.coe_ofEq_apply]

theorem ginzburgGeneratorPrefixPreviousEquiv_apply_coe (u v : Q.Vertex) (r c : ℤ)
    (f : Q.GinzburgGeneratorPrefix k u v r (r-1) c)
    (a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r}) :
    (Q.ginzburgGeneratorPrefixPreviousEquiv k u v r c f a).val=(f a).val := by
  simp only [ginzburgGeneratorPrefixPreviousEquiv,LinearEquiv.piCongrRight_apply,
    LinearEquiv.coe_ofEq_apply]

end ASGinzburg.CutQuiver
