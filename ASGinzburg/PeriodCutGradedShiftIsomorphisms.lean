import ASGinzburg.PeriodCutGradedShift

/-! Shifts by zero and by successive integers have genuine natural
isomorphisms, given by the identity on the underlying ring module. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

noncomputable def shiftedZeroIso (M : E.CutGradedRightModule Q) : M.shifted 0≅M where
  hom := ⟨LinearMap.id,⟨by intro r x;rfl,by
    intro q x hx
    simpa only [shifted,add_zero] using hx⟩⟩
  inv := ⟨LinearMap.id,⟨by intro r x;rfl,by
    intro q x hx
    simpa only [shifted,add_zero] using hx⟩⟩
  hom_inv_id := by apply Subtype.ext;apply LinearMap.ext;intro x;rfl
  inv_hom_id := by apply Subtype.ext;apply LinearMap.ext;intro x;rfl

noncomputable def shiftedAddIso (M : E.CutGradedRightModule Q) (s t : ℤ) :
    M.shifted (s+t) ≅ (M.shifted s).shifted t where
  hom := ⟨LinearMap.id,⟨by intro r x;rfl,by
    intro q x hx
    change x∈M.grade (q+t+s)
    change x∈M.grade (q+(s+t)) at hx
    simpa only [show q+t+s=q+(s+t) by ring] using hx⟩⟩
  inv := ⟨LinearMap.id,⟨by intro r x;rfl,by
    intro q x hx
    change x∈M.grade (q+(s+t))
    change x∈M.grade (q+t+s) at hx
    simpa only [show q+t+s=q+(s+t) by ring] using hx⟩⟩
  hom_inv_id := by apply Subtype.ext;apply LinearMap.ext;intro x;rfl
  inv_hom_id := by apply Subtype.ext;apply LinearMap.ext;intro x;rfl

noncomputable def shiftedFunctorZeroIso :
    shiftedFunctor (Q:=Q) (E:=E) 0 ≅ 𝟭 (E.CutGradedRightModule Q) :=
  NatIso.ofComponents shiftedZeroIso (by intro M N f;rfl)

noncomputable def shiftedFunctorAddIso (s t : ℤ) :
    shiftedFunctor (Q:=Q) (E:=E) (s+t) ≅
      shiftedFunctor s ⋙ shiftedFunctor t :=
  NatIso.ofComponents (fun M => M.shiftedAddIso s t) (by intro M N f;rfl)

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
