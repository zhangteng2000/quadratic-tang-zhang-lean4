import QuadraticTangZhang.UniformBounds
import QuadraticTangZhang.BoundaryTail

/-! # G. Exact one-record verifier

The 100-bit coordinates are represented by exact rationals. Powers and node
quotients are enclosed on the 160-bit grid. Rounding node quotients upward
also keeps quadrature sums dyadic and avoids huge unrelated denominators.
-/
namespace QuadraticTangZhang
open MeasureTheory

def certificateScale : ℕ := 2^160

theorem certificateScale_pos : 0 < certificateScale := by unfold certificateScale; positivity

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

theorem envelope_cast (b : CertificateRecord) (t : ℚ) :
    (b.envelope t:ℝ)=boxEnvelope (b.aLower:ℝ) (b.gap:ℝ) (t:ℝ) := by
  unfold envelope boxEnvelope
  push_cast
  rfl

theorem node_enclosures {b : CertificateRecord} (hb : b.Valid) {t : ℚ} (ht : 0 ≤ t ∧ t ≤ 1) :
    boxEnvelope (b.aLower:ℝ) (b.gap:ℝ) (t:ℝ)^(((b.mLower-1:ℕ):ℝ)/2) ≤ (b.nodeOne t:ℝ) ∧
    boxEnvelope (b.aLower:ℝ) (b.gap:ℝ) (t:ℝ)^(((b.mLower-1:ℕ):ℝ)/2)/
      (1-((b.aUpper:ℝ)^2+(b.gap:ℝ))/2*(t:ℝ)) ≤ (b.nodeTwo t:ℝ) := by
  rcases hb with ⟨hL,hLM,hA,hAZ,hZ,hh,hh1,hd⟩
  have htR : (t:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by exact_mod_cast ht.1,by exact_mod_cast ht.2⟩
  have hA2 : (b.aLower:ℝ)^2 ≤ 1 := by exact_mod_cast (show b.aLower^2 ≤ 1 by nlinarith)
  have henv : 0 ≤ b.envelope t := by
    apply Rat.cast_nonneg (K := ℝ) |>.mp
    rw [envelope_cast]
    exact boxEnvelope_nonneg hA2 (by exact_mod_cast hh1.le) htR
  have hp := (halfPower_sound certificateScale_pos henv (b.mLower-1)).2
  rw [envelope_cast] at hp
  refine ⟨hp,?_⟩
  have hdR : ((b.aUpper:ℝ)^2+(b.gap:ℝ))/2 < 1 := by exact_mod_cast hd
  have hdpos := affine_denominator_pos hdR htR
  have hdiv := div_le_div_of_nonneg_right hp hdpos.le
  have hround := cast_le_roundUp certificateScale_pos (b.nodeOne t/(1-b.denominator*t))
  unfold denominator at hround
  push_cast at hround
  exact hdiv.trans hround

theorem gap_test_sound {b : CertificateRecord} (hb : b.Valid) (hg : b.GapTest)
    {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hmL : b.mLower ≤ m) (hmM : m ≤ b.mUpper)
    (hAa : (b.aLower:ℝ) ≤ a) (haZ : a ≤ (b.aUpper:ℝ)) :
    (b.gap:ℝ) < 1-beta a x 1 := by
  rcases hb with ⟨hL,hLM,hA,hAZ,hZ,hh,hh1,hd⟩
  have hAR : (0:ℝ) ≤ b.aLower := by exact_mod_cast hA
  have hZR : (b.aUpper:ℝ) ≤ 1 := by exact_mod_cast hZ
  rcases hg with hg | hg
  · apply rectangle_rational_gap hw.a_pos hw.a_lt_one hw.x_le_one hw.moment_lower hw.moment_upper
      (by have := hw.degree; omega) hmM hAR hAa _ hw.polar
    unfold alphaUpper at hg
    have hcast := (Rat.cast_le (K := ℝ)).mpr hg
    push_cast at hcast
    exact hcast
  · apply rectangle_chord_gap hw.a_pos.le hw.a_lt_one hw.moment_lower hw.moment_upper
      (by have := hw.degree; omega) hmL hmM hAR hAa haZ hZR (by exact_mod_cast hh) _ hw.polar
    have hbase : 0 ≤ 1+(1-b.aLower^2)*b.gap := by nlinarith [mul_nonneg (show 0 ≤ 1-b.aLower^2 by nlinarith) hh]
    have hu := (halfPower_sound certificateScale_pos hbase (b.mUpper+2)).2
    have hl := (halfPower_sound certificateScale_pos hA (2*(b.mUpper+2))).1
    have he : (((2*(b.mUpper+2):ℕ):ℝ)/2) = ((b.mUpper+2:ℕ):ℝ) := by push_cast; ring
    rw [he,Real.rpow_natCast] at hl
    push_cast at hu
    have hgR : ((halfPowerUpper certificateScale (1+(1-b.aLower^2)*b.gap) (b.mUpper+2) -
        halfPowerLower certificateScale b.aLower (2*(b.mUpper+2)) -
        ((b.mLower:ℚ)+2)/2*(1-b.aUpper^2)*(1+b.gap):ℚ):ℝ) < 0 := by exact_mod_cast hg
    push_cast at hgR
    have heU : ((b.mUpper:ℝ)+2)/2=(b.mUpper:ℝ)/2+1 := by ring
    rw [heU] at hu
    nlinarith

def MeshValid (N : ℕ) (p : ℕ → ℚ) : Prop :=
  p 0=0 ∧ p N=1 ∧ (∀ i ∈ Finset.range (N+1), 0 ≤ p i ∧ p i ≤ 1) ∧
    (∀ i ∈ Finset.range N, p i ≤ p (i+1))

instance (N : ℕ) (p : ℕ → ℚ) : Decidable (MeshValid N p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem quadrature_bounds {b : CertificateRecord} (hb : b.Valid)
    {N : ℕ} {p : ℕ → ℚ} (hp : MeshValid N p) :
    (∫ t in (0:ℝ)..1, t*boxEnvelope (b.aLower:ℝ) (b.gap:ℝ) t^(((b.mLower-1:ℕ):ℝ)/2)) ≤
      (quadOne N p (fun i => b.nodeOne (p i)):ℝ) ∧
    (∫ t in (0:ℝ)..1, t^2*(boxEnvelope (b.aLower:ℝ) (b.gap:ℝ) t^(((b.mLower-1:ℕ):ℝ)/2)/
      (1-((b.aUpper:ℝ)^2+(b.gap:ℝ))/2*t))) ≤ (quadTwo N p (fun i => b.nodeTwo (p i)):ℝ) := by
  have hv (t : ℚ) (ht : 0 ≤ t ∧ t ≤ 1) := node_enclosures hb ht
  rcases hb with ⟨hL,hLM,hA,hAZ,hZ,hh,hh1,hd⟩
  rcases hp with ⟨hp0,hpN,hp,hpm⟩
  have hpoint (i : ℕ) (hi : i ≤ N) := hp i (Finset.mem_range.mpr (by omega))
  have hmono (i : ℕ) (hi : i < N) := hpm i (Finset.mem_range.mpr hi)
  have hA2 : (b.aLower:ℝ)^2 ≤ 1 := by exact_mod_cast (show b.aLower^2 ≤ 1 by nlinarith)
  have hhR : (b.gap:ℝ) ≤ 1 := by exact_mod_cast hh1.le
  have hr : (2:ℝ) ≤ ((b.mLower-1:ℕ):ℝ)/2 := by
    have h : (4:ℝ) ≤ (b.mLower-1:ℕ) := by exact_mod_cast (show 4 ≤ b.mLower-1 by omega)
    linarith
  have hdR : ((b.aUpper:ℝ)^2+(b.gap:ℝ))/2 < 1 := by exact_mod_cast hd
  have hc : Continuous fun t : ℝ => boxEnvelope (b.aLower:ℝ) (b.gap:ℝ) t := by unfold boxEnvelope; fun_prop
  constructor
  · exact finite_quadrature_one_sound hp0 hpN hpoint hmono
      (boxEnvelope_rpow_convex hA2 hhR (by linarith))
      (((Real.continuous_rpow_const (by linarith : (0:ℝ) ≤ ((b.mLower-1:ℕ):ℝ)/2)).comp hc).continuousOn)
      (fun i hi => (hv (p i) (hpoint i hi)).1)
  · exact finite_quadrature_two_sound hp0 hpN hpoint hmono
      (boxEnvelope_rpow_div_convex hA2 hhR hr hdR)
      (envelope_quotient_continuous (by linarith) hdR)
      (fun i hi => (hv (p i) (hpoint i hi)).2)

/-- A record accepted by all three checks excludes every scalar configuration
in its entire degree/parameter rectangle. -/
theorem one_record_verifier_sound {b : CertificateRecord} (hb : b.Valid)
    (hg : b.GapTest) {N : ℕ} {p : ℕ → ℚ} (hp : MeshValid N p) (he : b.ExclusionTest N p)
    {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hmL : b.mLower ≤ m) (hmM : m ≤ b.mUpper)
    (hAa : (b.aLower:ℝ) ≤ a) (haZ : a ≤ (b.aUpper:ℝ)) : False := by
  have hgap := gap_test_sound hb hg hw hmL hmM hAa haZ
  have hquad := quadrature_bounds hb hp
  rcases hb with ⟨hL,hLM,hA,hAZ,hZ,hh,hh1,hd⟩
  have hAR : (0:ℝ) ≤ b.aLower := by exact_mod_cast hA
  have hhR : (0:ℝ) ≤ b.gap := by exact_mod_cast hh
  have hdR : ((b.aUpper:ℝ)^2+(b.gap:ℝ))/2 < 1 := by exact_mod_cast hd
  have hu := uniform_coefficient_bounds hw.degree hL hmL hmM hw.a_pos.le hw.a_lt_one
    hw.x_le_one hAR hAa haZ hhR hgap.le hdR hquad.1 hquad.2
  have hCU : centerCoefficient m a x ≤ (b.upperC N p:ℝ) := by
    simpa only [upperC,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_add,Rat.cast_natCast,Rat.cast_one] using hu.2
  have hRU : (5/3:ℝ)*a^2*m*directIntegral m a x ≤ (b.upperR N p:ℝ) := by
    simpa only [upperR,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast] using hu.1
  have hends := uniform_endpoint_bound hmL hw.a_pos.le hw.a_lt_one hw.x_le_one hAR hAa hhR hgap.le
  have hbase : 0 ≤ 1-b.gap := by linarith
  have hFU : beta a x 1^((m:ℝ)/2) ≤ (b.upperF:ℝ) := by
    apply hends.1.trans
    convert (halfPower_sound certificateScale_pos hbase b.mLower).2 using 1 <;>
      first | rfl | simp only [Rat.cast_sub,Rat.cast_one,upperF]
  have hEU : beta a x 1^(((m+1:ℕ):ℝ)/2) ≤ (b.upperE:ℝ) := by
    apply hends.2.trans
    convert (halfPower_sound certificateScale_pos hbase (b.mLower+1)).2 using 1 <;>
      first | rfl | simp only [Rat.cast_sub,Rat.cast_one,upperE]
  have hTU : (m:ℝ)*a/(m+1) ≤ (b.upperT:ℝ) := by
    simpa only [upperT,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_one]
      using degree_term_mono hmM hw.a_pos.le haZ
  have hC := centerCoefficient_nonneg hw.a_pos.le hw.a_lt_one hw.x_le_one m
  have basic : (b.upperF:ℝ)+(b.upperR N p:ℝ)+(b.upperT:ℝ)<1 ∨
      (2*(b.upperC N p:ℝ)≤(b.aUpper:ℝ) ∧ (b.aUpper:ℝ)+(b.upperE:ℝ)<1) ∨
      (0<(b.upperC N p:ℝ) ∧ (b.upperE:ℝ)<1 ∧
        4*((b.aUpper:ℝ)+(b.upperC N p:ℝ))^3<27*(b.upperC N p:ℝ)*(1-(b.upperE:ℝ))^2) → False := by
    exact abstract_rectangle_exclusion_basic hw.a_pos.le hw.r_nonneg hw.r_le_one hC haZ
      hCU hEU hFU hRU hTU hw.centered hw.direct
  rcases he with he | he | he | he
  · apply basic
    exact Or.inl (by exact_mod_cast he)
  · apply basic
    exact Or.inr (Or.inl (by exact_mod_cast he))
  · apply basic
    exact Or.inr (Or.inr (by exact_mod_cast he))
  · rcases he with ⟨hCa,hα,hαsmall,htail⟩
    have hαR : (0:ℝ) < b.alphaUpper := by exact_mod_cast hα
    have hαsmallR : (b.mUpper:ℝ)/2*(1-(b.aLower:ℝ)^2) ≤ ((b.mLower:ℝ)-1)/2 := by
      have hcast := (Rat.cast_le (K := ℝ)).mpr hαsmall
      unfold alphaUpper at hcast
      push_cast at hcast
      exact hcast
    have ht := rectangle_boundary_tail hw.a_pos hw.a_lt_one hw.x_le_one hw.moment_lower hw.moment_upper
      (by have := hw.degree; omega) hmL hmM hAR hAa hαsmallR hw.polar
    have htailpower := (halfPower_sound certificateScale_pos
      (show 0 ≤ b.alphaUpper/(1+b.alphaUpper) by positivity) (b.mLower+1)).2
    have htailnum := mul_le_mul_of_nonneg_left htailpower
      (show (0:ℝ) ≤ (b.mUpper:ℝ)/2/(b.alphaUpper:ℝ) by positivity)
    have htailU : (b.mUpper:ℝ)/2/((b.mUpper:ℝ)/2*(1-(b.aLower:ℝ)^2))*
        (((b.mUpper:ℝ)/2*(1-(b.aLower:ℝ)^2))/(1+(b.mUpper:ℝ)/2*(1-(b.aLower:ℝ)^2)))^(((b.mLower:ℝ)+1)/2)
        ≤ (b.upperTail:ℝ) := by
      simpa only [upperTail,alphaUpper,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_add,Rat.cast_pow,
        Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat,Nat.cast_add,Nat.cast_one] using htailnum
    have hgain : 0 < 1-a^2 := by nlinarith [hw.a_pos,hw.a_lt_one]
    have ht' := ht.trans (mul_le_mul_of_nonneg_left htailU hgain.le)
    have htailR : (b.upperTail:ℝ) < 1/4 := by
      have hcast := (Rat.cast_lt (K := ℝ)).mpr htail
      norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hcast
      exact hcast
    have hE : beta a x 1^(((m+1:ℕ):ℝ)/2) < (1-a^2)/4 := by
      push_cast
      nlinarith [mul_lt_mul_of_pos_left htailR hgain]
    have hCaR : 2*(b.upperC N p:ℝ) ≤ (b.aLower:ℝ) := by exact_mod_cast hCa
    exact exclude_center_boundary hw.a_pos.le hw.a_lt_one hC (by linarith) hw.r_nonneg hw.r_le_one hE hw.centered

def verifyRecord (b : CertificateRecord) (N : ℕ) (p : ℕ → ℚ) : Bool :=
  decide (b.Valid ∧ b.GapTest ∧ MeshValid N p ∧ b.ExclusionTest N p)

theorem verifyRecord_sound {b : CertificateRecord} {N : ℕ} {p : ℕ → ℚ}
    (h : verifyRecord b N p=true) {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hmL : b.mLower ≤ m) (hmM : m ≤ b.mUpper)
    (hAa : (b.aLower:ℝ) ≤ a) (haZ : a ≤ (b.aUpper:ℝ)) : False := by
  have hc := of_decide_eq_true h
  exact one_record_verifier_sound hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hw hmL hmM hAa haZ

end CertificateRecord
end QuadraticTangZhang
