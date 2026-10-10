import ASGinzburg.TriangleArrowCoordinates
import ASGinzburg.PathCutUnrollingEquiv

/-! The nine actual cut-zero paths from vertex zero to vertex two are
the canonical composable X/Y arrow pairs. -/
namespace ASGinzburg

@[simp] theorem triangleXPath_cutDegree (i : Fin 3) :
    (triangleXPath i).cutDegree = 0 := by
  simp [triangleXPath, triangleEdgePath, triangleEdgeArrow,
    CutQuiver.Path.cutDegree, CutQuiver.cutDegree, triangle333]
  omega

@[simp] theorem triangleYPath_cutDegree (i : Fin 3) :
    (triangleYPath i).cutDegree = 0 := by
  simp [triangleYPath, triangleEdgePath, triangleEdgeArrow,
    CutQuiver.Path.cutDegree, CutQuiver.cutDegree, triangle333]
  omega

def triangleXYPath (xy : Fin 3 × Fin 3) : triangle333.Path 0 2 :=
  (triangleXPath xy.1).comp (triangleYPath xy.2)

@[simp] theorem triangleXYPath_toList (xy : Fin 3 × Fin 3) :
    (triangleXYPath xy).toList = [triangleX xy.1, triangleY xy.2] := by
  simp [triangleXYPath, CutQuiver.Path.toList_comp]

@[simp] theorem triangleXYPath_cutDegree (xy : Fin 3 × Fin 3) :
    (triangleXYPath xy).cutDegree = 0 := by
  simp [triangleXYPath, CutQuiver.Path.cutDegree_comp]

theorem path_length_two_arrows (Q : CutQuiver) {s t : Q.Vertex}
    (p : Q.Path s t) (hp : p.length = 2) :
    ∃ a b : Q.Arrow, Q.source a = s ∧ Q.target b = t ∧
      Q.source b = Q.target a ∧ p.toList = [a,b] := by
  cases p with
  | nil => simp [CutQuiver.Path.length] at hp
  | snoc p b hb =>
    cases p with
    | nil => simp [CutQuiver.Path.length] at hp
    | snoc p a ha =>
      cases p with
      | nil => exact ⟨a,b,ha,rfl,hb,rfl⟩
      | snoc p c hc => simp [CutQuiver.Path.length] at hp

theorem triangleCutZeroPath02_normal_form (p : triangle333.Path 0 2)
    (hc : p.cutDegree = 0) : ∃ xy : Fin 3 × Fin 3, p = triangleXYPath xy := by
  have hw := p.winding_eq
  rw [triangle_path_winding, hc] at hw
  have hp : p.length = 2 := by
    change (p.length : ℤ) = 2 - 0 + 3 * (0 : ℤ) at hw
    omega
  obtain ⟨a,b,ha,_,hb,hword⟩ := path_length_two_arrows triangle333 p hp
  have ha' : a.val / 3 = 0 := congrArg Fin.val ha
  have hb' : b.val / 3 = (a.val / 3 + 1) % 3 := congrArg Fin.val hb
  let x : Fin 3 := ⟨a.val, by omega⟩
  let y : Fin 3 := ⟨b.val - 3, by omega⟩
  have hax : a = triangleX x := by apply Fin.ext; rfl
  have hby : b = triangleY y := by
    apply Fin.ext
    dsimp [triangleY,y]
    omega
  refine ⟨(x,y), CutQuiver.Path.toList_injective _ _ ?_⟩
  rw [hword, triangleXYPath_toList, hax, hby]

noncomputable def triangleXYPathIndexEquiv :
    Fin 3 × Fin 3 ≃ CutQuiver.Path.CutDegreePath (Q := triangle333) 0 2 0 :=
  Equiv.ofBijective (fun xy => ⟨triangleXYPath xy, triangleXYPath_cutDegree xy⟩) (by
    constructor
    · intro xy xy' h
      have hw := congrArg (fun p => p.val.toList) h
      simp only [triangleXYPath_toList, List.cons.injEq] at hw
      apply Prod.ext
      · have hval := congrArg Fin.val hw.1
        apply Fin.ext
        exact hval
      · have hval := congrArg Fin.val hw.2.1
        apply Fin.ext
        dsimp [triangleY] at hval
        omega
    · intro p
      obtain ⟨xy,hxy⟩ := triangleCutZeroPath02_normal_form p.val p.property
      exact ⟨xy, Subtype.ext hxy.symm⟩)

universe u
variable (k : Type u) [Field k]

noncomputable def triangleXYCutComponentEquiv :
    triangle333.pathCutComponent k 0 2 0 ≃ₗ[k] (Fin 3 × Fin 3 → k) :=
  ((triangle333.pathCutComponentBasisEquiv k 0 2 0).trans
    (Finsupp.domLCongr triangleXYPathIndexEquiv.symm)).trans
      (Finsupp.linearEquivFunOnFinite k k (Fin 3 × Fin 3))

theorem triangleXYCutComponent_finrank :
    Module.finrank k (triangle333.pathCutComponent k 0 2 0) = 9 := by
  rw [(triangleXYCutComponentEquiv k).finrank_eq]
  simp

end ASGinzburg
