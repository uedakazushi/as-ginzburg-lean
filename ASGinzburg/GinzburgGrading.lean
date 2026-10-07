import ASGinzburg.CutQuiver

/-!
# The generators and gradings of the Ginzburg construction

These are the genuine generators a, a*, t_v and their three gradings.
The differential, its square-zero proof, and its cohomology are not
defined in this file. In particular, this is not a proof of regularity.
-/

namespace ASGinzburg.CutQuiver

variable (Q : CutQuiver)

inductive GinzburgArrow
  | original (a : Q.Arrow)
  | dual (a : Q.Arrow)
  | loop (v : Q.Vertex)
  deriving DecidableEq

namespace GinzburgArrow

def source : Q.GinzburgArrow → Q.Vertex
  | .original a => Q.source a
  | .dual a => Q.target a
  | .loop v => v

def target : Q.GinzburgArrow → Q.Vertex
  | .original a => Q.target a
  | .dual a => Q.source a
  | .loop v => v

def cohomologicalDegree : Q.GinzburgArrow → ℤ
  | .original _ => 0
  | .dual _ => -1
  | .loop _ => -2

def cutDegree : Q.GinzburgArrow → ℤ
  | .original a => Q.cutDegree a
  | .dual a => 1 - Q.cutDegree a
  | .loop _ => 1

def winding : Q.GinzburgArrow → ℤ
  | .original a => Q.winding a
  | .dual a => Q.vertices - Q.winding a
  | .loop _ => Q.vertices

theorem winding_pos (a : Q.GinzburgArrow) : 0 < winding Q a := by
  cases a with
  | original a => exact Q.winding_pos a
  | dual a =>
    have := Q.winding_lt_period a
    simp only [winding]
    omega
  | loop v =>
    have := Q.at_least_three
    simp only [winding]
    omega

theorem winding_formula (a : Q.GinzburgArrow) :
    winding Q a = (target Q a).val - (source Q a).val + Q.vertices * cutDegree Q a := by
  cases a with
  | original a => rfl
  | dual a =>
    simp only [winding, target, source, cutDegree, CutQuiver.winding]
    ring
  | loop v => simp [winding, target, source, cutDegree]

theorem original_dual_winding_sum (a : Q.Arrow) :
    winding Q (.original a) + winding Q (.dual a) = Q.vertices := by
  simp [winding]

theorem original_dual_cut_sum (a : Q.Arrow) :
    cutDegree Q (.original a) + cutDegree Q (.dual a) = 1 := by
  simp [cutDegree]

theorem loop_differential_cohomological_degree (a : Q.Arrow) :
    cohomologicalDegree Q (.original a) + cohomologicalDegree Q (.dual a) =
      cohomologicalDegree Q (.loop (Q.source a)) + 1 := by
  rfl

end GinzburgArrow
end ASGinzburg.CutQuiver
