import QuadraticTangZhang.CertificateKernel.Compute
import QuadraticTangZhang.CertificateMesh

namespace QuadraticTangZhang

theorem kernel_powLower_eq (S n : ℕ) (x : ℚ) :
    QuadraticTangZhangKernel.roundedPowLower S x n=roundedPowLower S x n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n; simp [QuadraticTangZhangKernel.roundedPowLower, roundedPowLower]
    · rw [QuadraticTangZhangKernel.roundedPowLower, roundedPowLower]
      simp only [dif_neg hn]
      rw [ih (n/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
      rfl

theorem kernel_powUpper_eq (S n : ℕ) (x : ℚ) :
    QuadraticTangZhangKernel.roundedPowUpper S x n=roundedPowUpper S x n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n; simp [QuadraticTangZhangKernel.roundedPowUpper, roundedPowUpper]
    · rw [QuadraticTangZhangKernel.roundedPowUpper, roundedPowUpper]
      simp only [dif_neg hn]
      rw [ih (n/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
      rfl

theorem kernel_halfLower_eq (S n : ℕ) (x : ℚ) :
    QuadraticTangZhangKernel.halfPowerLower S x n=halfPowerLower S x n := by
  simp only [QuadraticTangZhangKernel.halfPowerLower, halfPowerLower, kernel_powLower_eq]
  rfl

theorem kernel_halfUpper_eq (S n : ℕ) (x : ℚ) :
    QuadraticTangZhangKernel.halfPowerUpper S x n=halfPowerUpper S x n := by
  simp only [QuadraticTangZhangKernel.halfPowerUpper, halfPowerUpper, kernel_powUpper_eq]
  rfl

theorem kernel_insert_eq (v : ℕ) (l : List ℕ) :
    QuadraticTangZhangKernel.insertVertex v l=insertVertex v l := by
  induction l with
  | nil => rfl
  | cons w ws ih => simp only [QuadraticTangZhangKernel.insertVertex, insertVertex, ih]

theorem kernel_mesh_eq (m : ℕ) : QuadraticTangZhangKernel.meshVertices m=meshVertices m := by
  have hi : QuadraticTangZhangKernel.insertVertex=insertVertex := funext fun v => funext fun l => kernel_insert_eq v l
  simp only [QuadraticTangZhangKernel.meshVertices, meshVertices, hi]
  rfl

/-- The isolated computation is equal to the sound verifier for every input. -/
theorem kernel_check_eq (ml mh al ah h tag sub : ℕ) :
    QuadraticTangZhangKernel.verifyStandardRecord
      (QuadraticTangZhangKernel.decodeRecord ml mh al ah h tag sub) =
    verifyStandardRecord (decodeRecord ml mh al ah h tag sub) := by
  simp only [QuadraticTangZhangKernel.verifyStandardRecord, verifyStandardRecord,
    QuadraticTangZhangKernel.decodeRecord, decodeRecord,
    QuadraticTangZhangKernel.meshCount, meshCount,
    QuadraticTangZhangKernel.meshPoint, meshPoint, kernel_mesh_eq,
    QuadraticTangZhangKernel.CertificateRecord.verifyRecord, CertificateRecord.verifyRecord,
    QuadraticTangZhangKernel.CertificateRecord.Valid, CertificateRecord.Valid,
    QuadraticTangZhangKernel.CertificateRecord.GapTest, CertificateRecord.GapTest,
    QuadraticTangZhangKernel.CertificateRecord.MeshValid, CertificateRecord.MeshValid,
    QuadraticTangZhangKernel.CertificateRecord.ExclusionTest, CertificateRecord.ExclusionTest,
    QuadraticTangZhangKernel.CertificateRecord.upperF, CertificateRecord.upperF,
    QuadraticTangZhangKernel.CertificateRecord.upperE, CertificateRecord.upperE,
    QuadraticTangZhangKernel.CertificateRecord.upperT, CertificateRecord.upperT,
    QuadraticTangZhangKernel.CertificateRecord.upperR, CertificateRecord.upperR,
    QuadraticTangZhangKernel.CertificateRecord.upperC, CertificateRecord.upperC,
    QuadraticTangZhangKernel.CertificateRecord.upperTail, CertificateRecord.upperTail,
    QuadraticTangZhangKernel.CertificateRecord.nodeOne, CertificateRecord.nodeOne,
    QuadraticTangZhangKernel.CertificateRecord.nodeTwo, CertificateRecord.nodeTwo,
    QuadraticTangZhangKernel.CertificateRecord.envelope, CertificateRecord.envelope,
    QuadraticTangZhangKernel.CertificateRecord.denominator, CertificateRecord.denominator,
    QuadraticTangZhangKernel.CertificateRecord.alphaUpper, CertificateRecord.alphaUpper,
    QuadraticTangZhangKernel.quadOne, quadOne, QuadraticTangZhangKernel.quadTwo, quadTwo,
    QuadraticTangZhangKernel.chordOne, chordOne, QuadraticTangZhangKernel.chordTwo, chordTwo,
    kernel_halfLower_eq, kernel_halfUpper_eq,
    QuadraticTangZhangKernel.roundUp, roundUp,
    QuadraticTangZhangKernel.coordinateScale, coordinateScale,
    QuadraticTangZhangKernel.certificateScale, certificateScale]
  rfl

theorem kernel_checked_record (ml mh al ah h tag sub : ℕ)
    (hv : QuadraticTangZhangKernel.verifyStandardRecord
      (QuadraticTangZhangKernel.decodeRecord ml mh al ah h tag sub)=true) :
    verifyStandardRecord (decodeRecord ml mh al ah h tag sub)=true :=
  (kernel_check_eq ml mh al ah h tag sub).symm.trans hv

#print axioms kernel_checked_record

end QuadraticTangZhang
