import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace OrderedPartitions.ThreePoleCert

/-- A rational disk on an entire closed interval of epsilon=(6(1-q))^(1/3). -/
structure Cell where
  lo : ℚ
  hi : ℚ
  multiplicity : ℕ
  x : ℚ
  y : ℚ
  radius : ℚ
  cap : ℚ
  negCap : ℚ
deriving Repr

namespace Cell

def qLo (c : Cell) : ℚ := 1-c.hi^3/6
def qHi (c : Cell) : ℚ := 1-c.lo^3/6
def hLower (c : Cell) : ℚ := min 1
    (((173205/100000:ℚ)*c.x-c.y-2*c.radius)*
      ((173205/100000:ℚ)*c.x+c.y-2*c.radius)/c.cap^2)
def derivCap (c : Cell) : ℚ := if c.radius < c.y then
    min 12 ((c.cap^2/2+2*(1-c.qLo))*c.cap/(c.y-c.radius)) else 12
def negDeriv (c : Cell) : ℚ := c.negCap^2/2-2*(1-c.qLo)
def remainderCap (c : Cell) : ℚ :=
  c.derivCap / c.hLower *
    ((c.cap/c.negCap)^241 / (2*c.negDeriv) + 18*(c.cap/2)^241)

def geometry (c : Cell) : Bool := decide
  (0 < c.lo ∧ c.lo < c.hi ∧ 0 < c.radius ∧ c.radius < c.x ∧
   0 ≤ c.y ∧ 1732/1000*c.x-c.y > 2*c.radius ∧
   c.x^2+c.y^2 < (c.cap-c.radius)^2 ∧ c.radius < c.cap ∧
   c.cap < c.negCap ∧ c.negCap < 2 ∧
   (c.multiplicity = 1 ∧ c.radius < c.y ∨ c.multiplicity = 2 ∧ c.y = 0))
def budget (c : Cell) : Bool := decide
  (0 < c.negDeriv ∧ 0 < c.hLower ∧ 0 < c.derivCap ∧ c.remainderCap < 2/5)
def passes (c : Cell) : Bool := c.geometry && c.budget

end Cell
end OrderedPartitions.ThreePoleCert
