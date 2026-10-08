import ASGinzburg.GinzburgPathWords
import ASGinzburg.GinzburgPathFiniteness

/-! Every genuine nonempty Ginzburg path ending at v has a unique last
generator and a genuine prefix. This is the free augmentation-ideal basis. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

@[simp] theorem GinzburgPath.transport_toList {u v u' v' : Q.Vertex}
    (hu : u=u') (hv : v=v') (p : Q.GinzburgPath u v) :
    (p.transport Q hu hv).toList=p.toList := by subst u' v'; rfl

@[simp] theorem GinzburgPath.transport_length {u v u' v' : Q.Vertex}
    (hu : u=u') (hv : v=v') (p : Q.GinzburgPath u v) :
    (p.transport Q hu hv).length=p.length := by subst u' v'; rfl

def GinzburgLastGeneratorData (u v : Q.Vertex) :=
  Σ a : {a : Q.GinzburgArrow // a.target Q=v}, Q.GinzburgPath u (a.val.source Q)

def GinzburgLastGeneratorData.path {u v : Q.Vertex} (d : Q.GinzburgLastGeneratorData u v) :
    Q.GinzburgPath u v :=
  (GinzburgPath.snoc d.2 d.1.val rfl).transport Q rfl d.1.property

theorem GinzburgLastGeneratorData.path_length {u v : Q.Vertex}
    (d : Q.GinzburgLastGeneratorData u v) : (d.path Q).length=d.2.length+1 := by
  simp [path,GinzburgPath.length]

def GinzburgPath.lastGenerator {u v : Q.Vertex} (p : Q.GinzburgPath u v) (hp : 0<p.length) :
    Q.GinzburgLastGeneratorData u v := by
  cases p with
  | nil => simp [length] at hp
  | snoc p a h => exact ⟨⟨a,rfl⟩,p.transport Q rfl h.symm⟩

theorem GinzburgPath.lastGenerator_path {u v : Q.Vertex}
    (p : Q.GinzburgPath u v) (hp : 0<p.length) : (p.lastGenerator Q hp).path Q=p := by
  cases p with
  | nil => simp [length] at hp
  | snoc p a h =>
    cases h
    rfl

theorem GinzburgLastGeneratorData.path_lastGenerator {u v : Q.Vertex}
    (d : Q.GinzburgLastGeneratorData u v) :
    (d.path Q).lastGenerator Q (by rw [d.path_length]; omega)=d := by
  obtain ⟨⟨a,ha⟩,p⟩ := d
  cases ha
  rfl

def ginzburgNonemptyLastEquiv (u v : Q.Vertex) :
    {p : Q.GinzburgPath u v // 0<p.length} ≃ Q.GinzburgLastGeneratorData u v where
  toFun p := p.val.lastGenerator Q p.property
  invFun d := ⟨d.path Q,by rw [d.path_length]; omega⟩
  left_inv p := Subtype.ext (p.val.lastGenerator_path Q p.property)
  right_inv d := d.path_lastGenerator Q

end ASGinzburg.CutQuiver
