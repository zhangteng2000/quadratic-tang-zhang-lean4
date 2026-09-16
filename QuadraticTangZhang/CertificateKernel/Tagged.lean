import QuadraticTangZhang.CertificateKernel.Compute

namespace QuadraticTangZhangKernel

/-- The record's original tag selects a sufficient exclusion test. -/
def SelectedTest (b : CertificateRecord) (N : ℕ) (p : ℕ → ℚ) : Prop :=
  (b.tag=0 ∧ b.upperF+b.upperR N p+b.upperT < 1) ∨
  (b.tag=1 ∧ 2*b.upperC N p ≤ b.aUpper ∧ b.aUpper+b.upperE < 1) ∨
  (b.tag=2 ∧ 0 < b.upperC N p ∧ b.upperE < 1 ∧
    4*(b.aUpper+b.upperC N p)^3 < 27*b.upperC N p*(1-b.upperE)^2) ∨
  (b.tag=3 ∧ 2*b.upperC N p ≤ b.aLower ∧ 0 < b.alphaUpper ∧
    b.alphaUpper ≤ ((b.mLower:ℚ)-1)/2 ∧ b.upperTail < 1/4)

instance (b : CertificateRecord) (N : ℕ) (p : ℕ → ℚ) : Decidable (SelectedTest b N p) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem selectedTest_sound {b : CertificateRecord} {N : ℕ} {p : ℕ → ℚ}
    (h : SelectedTest b N p) : b.ExclusionTest N p := by
  rcases h with h | h | h | h
  · exact Or.inl h.2
  · exact Or.inr (Or.inl h.2)
  · exact Or.inr (Or.inr (Or.inl h.2))
  · exact Or.inr (Or.inr (Or.inr h.2))

def taggedCheck (b : CertificateRecord) : Bool :=
  decide (b.subdivision=2 ∧ b.Valid ∧ b.GapTest ∧
    CertificateRecord.MeshValid (meshCount b.mUpper) (meshPoint b.mUpper) ∧
    SelectedTest b (meshCount b.mUpper) (meshPoint b.mUpper))

/-- Choosing a test only saves computation; acceptance still proves that the
original complete checker returns true. -/
theorem tagged_checked (b : CertificateRecord) (h : taggedCheck b=true) :
    verifyStandardRecord b=true := by
  have hp := of_decide_eq_true h
  simp only [verifyStandardRecord, CertificateRecord.verifyRecord, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,selectedTest_sound hp.2.2.2.2⟩

#print axioms tagged_checked

end QuadraticTangZhangKernel
