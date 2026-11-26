import OrderedPartitions.ThreePoleCell

namespace OrderedPartitions.ThreePoleCert
namespace QComplex

abbrev Point := ℚ × ℚ
def add (z w : Point) : Point := (z.1+w.1,z.2+w.2)
def mult (z w : Point) : Point := (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1)
def scale (z : Point) (s : ℚ) : Point := (s*z.1,s*z.2)
def expTaylor (z : Point) : Point :=
  (List.range 36).reverse.foldl (fun w k ↦ add (1,0) (scale (mult z w) (1/(k+1:ℚ)))) (1,0)
def scale23 : ℕ := 10^23
def lower (z : Point) : ℚ :=
  (Nat.sqrt (⌊(z.1^2+z.2^2)*(scale23:ℚ)^2⌋.toNat) : ℚ) / scale23
def upper (z : Point) : ℚ := lower z + 1/scale23
def expError : ℚ := (8*2^37 : ℕ)/(Nat.factorial 37:ℚ)
def expUpper (x : ℚ) : ℚ := (expTaylor (x,0)).1 + expError

end QComplex
namespace Cell
open QComplex

/-- Two endpoint checks locate the unique negative real zero beyond v. -/
def negativeSigns (c : Cell) : Bool :=
  let v := c.negCap
  let expLo := (expTaylor (-v,0)).1-expError
  let f := fun (q : ℚ) ↦ 1-2*q+v-v^2/2+q*expLo
  decide (0 < f c.qLo ∧ 0 < f c.qHi)

/-- Taylor/Rouché comparison on the entire boundary for a single-root
or a two-root disk, with the same rational arithmetic as the paper checker. -/
def rouche (c : Cell) : Bool :=
  let z : Point := (c.x,c.y)
  let q := (c.qLo+c.qHi)/2
  let dq := (c.qHi-c.qLo)/2
  let e := scale (expTaylor z) q
  let eg := expUpper (c.x+c.radius)
  let g := add (add (add (1-2*q,0) (scale z (-1))) (scale (mult z z) (-(1/2)))) e
  let g1 := add (add e (-1,0)) (scale z (-1))
  let g2 := add e (-1,0)
  let constant := upper g + q*expError + dq*(2+eg)
  let d := c.radius
  if c.multiplicity=1 then
    decide (constant+(upper g2+q*expError+q*eg*d)*d^2/2 < (lower g1-q*expError)*d)
  else
    decide (constant+(upper g1+q*expError)*d+q*eg*d^3/6 < (lower g2-q*expError)*d^2/2)

def taylorPass (c : Cell) : Bool := c.negativeSigns && c.rouche

end Cell
end OrderedPartitions.ThreePoleCert
