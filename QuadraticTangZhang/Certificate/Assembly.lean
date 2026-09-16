import QuadraticTangZhang.Certificate.DataFacts

namespace QuadraticTangZhang.CertificateData

/-- The Boolean assertion checked by the 43 kernel proof batches. -/
def allBlocksAccepted : Bool := blocks.all (fun B => B.records.all verifyStandardRecord)

theorem accepted_records_of_blocks (h : allBlocksAccepted=true) :
    records.all verifyStandardRecord=true :=
  (List.all_flatMap (l := blocks) (f := DegreeBlock.records) (p := verifyStandardRecord)).trans h

theorem accepted_blocks_sound {bs : List DegreeBlock}
    (h : bs.all (fun B => B.records.all verifyStandardRecord)=true) :
    ∀ B ∈ bs, ∀ b ∈ B.records, ∃ N p, CertificateRecord.verifyRecord b N p=true := by
  intro B hB b hb
  have hBv : B.records.all verifyStandardRecord=true := List.all_eq_true.mp h B hB
  have hv : verifyStandardRecord b=true := List.all_eq_true.mp hBv b hb
  simp only [verifyStandardRecord, Bool.and_eq_true] at hv
  exact ⟨meshCount b.mUpper, meshPoint b.mUpper, hv.2⟩

theorem finite_scalar_exclusion_of_checks (h : allBlocksAccepted=true)
    {m : ℕ} (hm : 5 ≤ m) (hm1 : m < 1000000) {a x s r : ℝ}
    (hw : ScalarConditions m a x s r) : False :=
  certificate_coverage_sound full_certificate_coverage (accepted_blocks_sound (bs := blocks) h)
    hm hm1 hw

end QuadraticTangZhang.CertificateData
