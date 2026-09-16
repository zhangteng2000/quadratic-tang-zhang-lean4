import QuadraticTangZhang.CertificateVerifier

/-! # H. Coverage by adjacent rational parameter intervals and degree blocks -/
namespace QuadraticTangZhang

structure DegreeBlock where
  lower : ℕ
  upper : ℕ
  records : List CertificateRecord
  deriving Repr

def checkParameterChain (lo hi : ℕ) (start : ℚ) : List CertificateRecord → Bool
  | [] => decide (start=1)
  | b::bs => decide (b.mLower=lo ∧ b.mUpper=hi ∧ b.aLower=start ∧ b.aLower ≤ b.aUpper) &&
      checkParameterChain lo hi b.aUpper bs

theorem parameter_chain_sound {bs : List CertificateRecord} {lo hi : ℕ} {start : ℚ}
    (h : checkParameterChain lo hi start bs=true)
    {a : ℝ} (ha : (start:ℝ) ≤ a) (ha1 : a < 1) :
    ∃ b ∈ bs, b.mLower=lo ∧ b.mUpper=hi ∧ (b.aLower:ℝ) ≤ a ∧ a ≤ (b.aUpper:ℝ) := by
  induction bs generalizing start with
  | nil =>
    have hs : start=1 := of_decide_eq_true h
    rw [hs] at ha
    norm_num at ha
    linarith
  | cons b bs ih =>
    simp only [checkParameterChain,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with ⟨⟨hlo,hhi,hl,hlr⟩,hrest⟩
    by_cases hab : a ≤ (b.aUpper:ℝ)
    · exact ⟨b,List.mem_cons_self, hlo,hhi,by simpa only [hl] using ha,hab⟩
    · obtain ⟨c,hc,hcL,hcU,hca,hac⟩ := ih hrest (le_of_lt (lt_of_not_ge hab))
      exact ⟨c,List.mem_cons_of_mem _ hc,hcL,hcU,hca,hac⟩

def checkDegreeChain (start stop : ℕ) : List DegreeBlock → Bool
  | [] => decide (start=stop)
  | b::bs => decide (b.lower=start ∧ b.lower ≤ b.upper) &&
      checkParameterChain b.lower b.upper 0 b.records &&
      checkDegreeChain (b.upper+1) stop bs

theorem degree_chain_sound {bs : List DegreeBlock} {start stop : ℕ}
    (h : checkDegreeChain start stop bs=true) {m : ℕ} (hm : start ≤ m) (hm1 : m < stop)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    ∃ B ∈ bs, ∃ b ∈ B.records, b.mLower ≤ m ∧ m ≤ b.mUpper ∧
      (b.aLower:ℝ) ≤ a ∧ a ≤ (b.aUpper:ℝ) := by
  induction bs generalizing start with
  | nil =>
    have hs : start=stop := of_decide_eq_true h
    omega
  | cons B bs ih =>
    simp only [checkDegreeChain,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨hstart,hLU⟩,hparams⟩,hrest⟩
    by_cases hmB : m ≤ B.upper
    · obtain ⟨b,hb,hbL,hbU,hba,hab⟩ := parameter_chain_sound hparams (by simpa using ha) ha1
      exact ⟨B,List.mem_cons_self,b,hb,by omega,by omega,hba,hab⟩
    · obtain ⟨C,hC,b,hb,hbL,hbU,hba,hab⟩ := ih hrest (by omega)
      exact ⟨C,List.mem_cons_of_mem _ hC,b,hb,hbL,hbU,hba,hab⟩

/-- Coverage plus sound accepted records rules out every scalar configuration
in the full range. The lower/upper bounds on degree and parameter are part of
the conclusion, rather than being supplied separately for a selected point. -/
theorem certificate_coverage_sound {bs : List DegreeBlock} {start stop : ℕ}
    (hcover : checkDegreeChain start stop bs=true)
    (hrecords : ∀ B ∈ bs, ∀ b ∈ B.records, ∃ N p, CertificateRecord.verifyRecord b N p=true)
    {m : ℕ} (hm : start ≤ m) (hm1 : m < stop) {a x s r : ℝ}
    (hw : ScalarConditions m a x s r) : False := by
  obtain ⟨B,hB,b,hb,hmL,hmM,haA,haZ⟩ := degree_chain_sound hcover hm hm1 hw.a_pos.le hw.a_lt_one
  obtain ⟨N,p,hverify⟩ := hrecords B hB b hb
  exact CertificateRecord.verifyRecord_sound hverify hw hmL hmM haA haZ

end QuadraticTangZhang
