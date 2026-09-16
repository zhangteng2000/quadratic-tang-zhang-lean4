import Mathlib.Data.Rat.Floor

import Mathlib.Data.Nat.Sqrt

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Data.Finset.Range



/-! Pure computation, copied exactly from the sound verifier. The bridge proves equality. -/

namespace QuadraticTangZhangKernel

open scoped BigOperators



def roundDown (S : ℕ) (x : ℚ) : ℚ := (⌊x*S⌋₊ : ℚ)/S

def roundUp (S : ℕ) (x : ℚ) : ℚ := (⌈x*S⌉₊ : ℚ)/S

def roundedPowLower (S : ℕ) (x : ℚ) (n : ℕ) : ℚ :=
  if hn : n=0 then 1 else
    let z := roundedPowLower S x (n/2)
    let zz := roundDown S (z*z)
    if n%2=0 then zz else roundDown S (zz*x)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

def roundedPowUpper (S : ℕ) (x : ℚ) (n : ℕ) : ℚ :=
  if hn : n=0 then 1 else
    let z := roundedPowUpper S x (n/2)
    let zz := roundUp S (z*z)
    if n%2=0 then zz else roundUp S (zz*x)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

def roundedSqrtLower (S : ℕ) (x : ℚ) : ℚ := ((Nat.sqrt (⌊x*S⌋₊ * S) : ℕ) : ℚ)/S

def roundedSqrtUpper (S : ℕ) (x : ℚ) : ℚ := ((Nat.sqrt (⌈x*S⌉₊ * S)+1 : ℕ) : ℚ)/S

def halfPowerLower (S : ℕ) (x : ℚ) (n : ℕ) : ℚ :=
  if n%2=0 then roundedPowLower S x (n/2)
  else roundDown S (roundedPowLower S x (n/2)*roundedSqrtLower S x)

def halfPowerUpper (S : ℕ) (x : ℚ) (n : ℕ) : ℚ :=
  if n%2=0 then roundedPowUpper S x (n/2)
  else roundUp S (roundedPowUpper S x (n/2)*roundedSqrtUpper S x)

def chordOne (l r u v : ℚ) : ℚ :=
  (r-l)*(l/2+(r-l)/6)*u+(r-l)*(l/2+(r-l)/3)*v

def chordTwo (l r u v : ℚ) : ℚ :=
  (r-l)*(l^2/2+l*(r-l)/3+(r-l)^2/12)*u+
    (r-l)*(l^2/2+2*l*(r-l)/3+(r-l)^2/4)*v

def quadOne (N : ℕ) (p v : ℕ → ℚ) : ℚ :=
  ∑ i ∈ Finset.range N, chordOne (p i) (p (i+1)) (v i) (v (i+1))

def quadTwo (N : ℕ) (p v : ℕ → ℚ) : ℚ :=
  ∑ i ∈ Finset.range N, chordTwo (p i) (p (i+1)) (v i) (v (i+1))

def certificateScale : ℕ := 2^160

structure CertificateRecord where
  mLower : ℕ
  mUpper : ℕ
  aLower : ℚ
  aUpper : ℚ
  gap : ℚ
  tag : ℕ
  subdivision : ℕ
  deriving Repr, DecidableEq

namespace CertificateRecord

def denominator (b : CertificateRecord) : ℚ := (b.aUpper^2+b.gap)/2
def alphaUpper (b : CertificateRecord) : ℚ := (b.mUpper:ℚ)/2*(1-b.aLower^2)
def envelope (b : CertificateRecord) (t : ℚ) : ℚ := 1-b.gap*t-b.aLower^2*t*(1-t)
def nodeOne (b : CertificateRecord) (t : ℚ) : ℚ :=
  halfPowerUpper certificateScale (b.envelope t) (b.mLower-1)
def nodeTwo (b : CertificateRecord) (t : ℚ) : ℚ :=
  roundUp certificateScale (b.nodeOne t/(1-b.denominator*t))
def upperF (b : CertificateRecord) : ℚ := halfPowerUpper certificateScale (1-b.gap) b.mLower
def upperE (b : CertificateRecord) : ℚ := halfPowerUpper certificateScale (1-b.gap) (b.mLower+1)
def upperT (b : CertificateRecord) : ℚ := (b.mUpper:ℚ)*b.aUpper/(b.mUpper+1)
def upperR (b : CertificateRecord) (N : ℕ) (p : ℕ → ℚ) : ℚ :=
  (5/3:ℚ)*b.aUpper^2*b.mUpper*quadOne N p (fun i => b.nodeOne (p i))
def upperC (b : CertificateRecord) (N : ℕ) (p : ℕ → ℚ) : ℚ :=
  (5/6:ℚ)*b.aUpper^3*((b.mUpper:ℚ)+1)*b.mUpper*quadTwo N p (fun i => b.nodeTwo (p i))
def upperTail (b : CertificateRecord) : ℚ :=
  (b.mUpper:ℚ)/2/b.alphaUpper*
    halfPowerUpper certificateScale (b.alphaUpper/(1+b.alphaUpper)) (b.mLower+1)

def Valid (b : CertificateRecord) : Prop :=
  5 ≤ b.mLower ∧ b.mLower ≤ b.mUpper ∧ 0 ≤ b.aLower ∧ b.aLower < b.aUpper ∧
  b.aUpper ≤ 1 ∧ 0 ≤ b.gap ∧ b.gap < 1 ∧ b.denominator < 1

instance (b : CertificateRecord) : Decidable b.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def GapTest (b : CertificateRecord) : Prop :=
  b.gap ≤ 1/(1+b.alphaUpper) ∨
  halfPowerUpper certificateScale (1+(1-b.aLower^2)*b.gap) (b.mUpper+2) -
    halfPowerLower certificateScale b.aLower (2*(b.mUpper+2)) -
    ((b.mLower:ℚ)+2)/2*(1-b.aUpper^2)*(1+b.gap) < 0

instance (b : CertificateRecord) : Decidable b.GapTest := inferInstanceAs (Decidable (_ ∨ _))

def ExclusionTest (b : CertificateRecord) (N : ℕ) (p : ℕ → ℚ) : Prop :=
  b.upperF+b.upperR N p+b.upperT < 1 ∨
  (2*b.upperC N p ≤ b.aUpper ∧ b.aUpper+b.upperE < 1) ∨
  (0 < b.upperC N p ∧ b.upperE < 1 ∧ 4*(b.aUpper+b.upperC N p)^3 < 27*b.upperC N p*(1-b.upperE)^2) ∨
  (2*b.upperC N p ≤ b.aLower ∧ 0 < b.alphaUpper ∧
    b.alphaUpper ≤ ((b.mLower:ℚ)-1)/2 ∧ b.upperTail < 1/4)

instance (b : CertificateRecord) (N : ℕ) (p : ℕ → ℚ) : Decidable (b.ExclusionTest N p) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def MeshValid (N : ℕ) (p : ℕ → ℚ) : Prop :=
  p 0=0 ∧ p N=1 ∧ (∀ i ∈ Finset.range (N+1), 0 ≤ p i ∧ p i ≤ 1) ∧
    (∀ i ∈ Finset.range N, p i ≤ p (i+1))

instance (N : ℕ) (p : ℕ → ℚ) : Decidable (MeshValid N p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def verifyRecord (b : CertificateRecord) (N : ℕ) (p : ℕ → ℚ) : Bool :=
  decide (b.Valid ∧ b.GapTest ∧ MeshValid N p ∧ b.ExclusionTest N p)

end CertificateRecord

def coordinateScale : ℕ := 2^100

/-- Exact decoding of a certificate row, with no conversion through floating point. -/
def decodeRecord (ml mh al ah h tag sub : ℕ) : CertificateRecord :=
  ⟨ml,mh,(al:ℚ)/coordinateScale,(ah:ℚ)/coordinateScale,(h:ℚ)/coordinateScale,tag,sub⟩

def insertVertex (v : ℕ) : List ℕ → List ℕ
  | [] => [v]
  | w::ws => if v<w then v::w::ws else if v=w then w::ws else w::insertVertex v ws

/-- The original checker uses subdivision two throughout. The mesh is encoded
as integer vertices and its validity is checked, independently of this constructor. -/
def meshVertices (mUpper : ℕ) : Array ℕ := Id.run do
  let scale := coordinateScale
  let kmax := mUpper.log2+4
  let coarse := (0 :: ((List.range kmax).reverse.map (fun k => scale/2^(k+1)))) ++ [scale]
  let mut points : List ℕ := [0,scale]
  for (l,r) in coarse.zip coarse.tail do
    for j in List.range 3 do
      let v := l+(r-l)*j/2
      points := v :: (scale-v) :: points
  return (points.foldr insertVertex []).toArray

def meshCount (mUpper : ℕ) : ℕ := (meshVertices mUpper).size-1
def meshPoint (mUpper i : ℕ) : ℚ := ((meshVertices mUpper)[i]?.getD 0:ℚ)/coordinateScale

def verifyStandardRecord (b : CertificateRecord) : Bool :=
  decide (b.subdivision=2) && CertificateRecord.verifyRecord b (meshCount b.mUpper) (meshPoint b.mUpper)

end QuadraticTangZhangKernel

