import QuadraticTangZhang.CertificateCoverage

namespace QuadraticTangZhang

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

theorem verifyStandardRecord_sound {b : CertificateRecord} (h : verifyStandardRecord b=true)
    {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hmL : b.mLower ≤ m) (hmM : m ≤ b.mUpper)
    (hAa : (b.aLower:ℝ) ≤ a) (haZ : a ≤ (b.aUpper:ℝ)) : False := by
  simp only [verifyStandardRecord,Bool.and_eq_true] at h
  exact CertificateRecord.verifyRecord_sound h.2 hw hmL hmM hAa haZ

end QuadraticTangZhang
