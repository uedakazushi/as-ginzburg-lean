import ASGinzburg.UnrolledPathWords

/-! A genuine ordinary path lifts to any prescribed endpoint sheets
whose difference equals its actual cut degree. -/
namespace ASGinzburg.CutQuiver
variable {Q : CutQuiver}

def Path.unrollBetween (u v : Q.Vertex) (m n : ℤ)
    (p : {p : Q.Path u v // (p.cutDegree:ℤ)=n-m}) : Q.UnrolledPath (u,m) (v,n) :=
  (p.val.unroll m).transport rfl (by
    apply Prod.ext
    · rfl
    · have := p.property
      change m+(p.val.cutDegree:ℤ)=n
      omega)

theorem Path.unrollBetween_erase (u v : Q.Vertex) (m n : ℤ)
    (p : {p : Q.Path u v // (p.cutDegree:ℤ)=n-m}) :
    (Path.unrollBetween u v m n p).erase=p.val := by
  apply Path.toList_injective
  simp [unrollBetween,Path.unroll_erase_toList]

def UnrolledPath.eraseBetween {u v : Q.Vertex} {m n : ℤ}
    (p : Q.UnrolledPath (u,m) (v,n)) : {p : Q.Path u v // (p.cutDegree:ℤ)=n-m} :=
  ⟨p.erase,p.erase_cutDegree⟩

def Path.betweenSheetEquiv (u v : Q.Vertex) (m n : ℤ) :
    {p : Q.Path u v // (p.cutDegree:ℤ)=n-m} ≃ Q.UnrolledPath (u,m) (v,n) where
  toFun := Path.unrollBetween u v m n
  invFun := UnrolledPath.eraseBetween
  left_inv p := Subtype.ext (Path.unrollBetween_erase u v m n p)
  right_inv p := by
    apply UnrolledPath.erase_toList_injective
    change (Path.unrollBetween u v m n p.eraseBetween).erase.toList=p.erase.toList
    rw [Path.unrollBetween_erase]
    rfl

end ASGinzburg.CutQuiver
