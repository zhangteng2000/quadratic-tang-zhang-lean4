import QuadraticTangZhang.DyadicSoundness
import QuadraticTangZhang.BetaBounds
import QuadraticTangZhang.RhoBounds

/-! # Analytic enclosures required for G, the one-record soundness theorem -/

namespace QuadraticTangZhang
open MeasureTheory

theorem beta_gap_form (a x t : ℝ) : beta a x t = boxEnvelope a (1-beta a x 1) t := by
  unfold beta boxEnvelope
  ring

theorem denominator_gap_form (a x t : ℝ) :
    1-a*x*t = 1-(a^2+(1-beta a x 1))/2*t := by unfold beta; ring

theorem rpow_div_mono_pair {B b D d r : ℝ}
    (hb : 0 < b) (hB : b ≤ B) (hd : 0 < d) (hD : 0 < D)
    (hr : 1 ≤ r) (hratio : b/d ≤ B/D) : b^r/d ≤ B^r/D := by
  have hB0 : 0 < B := hb.trans_le hB
  have hp := Real.rpow_le_rpow hb.le hB (show 0 ≤ r-1 by linarith)
  have hprod := mul_le_mul hp hratio (div_nonneg hb.le hd.le)
    (Real.rpow_nonneg hB0.le (r-1))
  have hpowb : b^(r-1)*b=b^r := by
    calc
      b^(r-1)*b = b^(r-1)*b^(1:ℝ) := by rw [Real.rpow_one]
      _ = b^((r-1)+1) := (Real.rpow_add hb _ _).symm
      _ = b^r := by congr 1; ring
  have hpowB : B^(r-1)*B=B^r := by
    calc
      B^(r-1)*B = B^(r-1)*B^(1:ℝ) := by rw [Real.rpow_one]
      _ = B^((r-1)+1) := (Real.rpow_add hB0 _ _).symm
      _ = B^r := by congr 1; ring
  simpa only [← mul_div_assoc,hpowb,hpowB] using hprod

/-- Replacing the true beta gap by a smaller gap enlarges the quotient.
This is a finite algebraic argument, avoiding differentiation in the gap. -/
theorem beta_quotient_gap_mono {a x h t r : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hx : x ≤ 1) (hh : h ≤ 1-beta a x 1) (ht : t ∈ Set.Icc (0:ℝ) 1) (hr : 1 ≤ r) :
    beta a x t^r/(1-a*x*t) ≤ boxEnvelope a h t^r/(1-(a^2+h)/2*t) := by
  have hb := beta_pos_on_unit ha ha1 hx ht.1 ht.2
  have hd := origin_gap_pos ha ha1 hx ht.1 ht.2
  have hnum : beta a x t ≤ boxEnvelope a h t := by
    rw [beta_gap_form]
    unfold boxEnvelope
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) ht.1]
  have hden : 1-a*x*t ≤ 1-(a^2+h)/2*t := by
    rw [denominator_gap_form]
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) ht.1]
  have hD := hd.trans_le hden
  apply rpow_div_mono_pair hb hnum hd hD hr
  rw [div_le_div_iff₀ hd hD]
  have hgap := mul_nonneg (sub_nonneg.mpr hh) ht.1
  have ha2t2 : a^2*t^2 ≤ 1 := by
    have ha2 : a^2 ≤ 1 := by nlinarith
    have ht2 : t^2 ≤ 1 := by nlinarith [ht.1,ht.2]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (sq_nonneg t)]
  have hprod := mul_nonneg hgap (sub_nonneg.mpr ha2t2)
  unfold beta boxEnvelope at *
  nlinarith

theorem rectangle_envelope_power_bound {a x A h t r R : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ≤ 1) (hA : 0 ≤ A) (hAa : A ≤ a)
    (hh0 : 0 ≤ h) (hh : h ≤ 1-beta a x 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hR : 0 ≤ R) (hRr : R ≤ r) :
    beta a x t ^ r ≤ boxEnvelope A h t ^ R := by
  have hb := (beta_pos_on_unit ha ha1 hx ht.1 ht.2).le
  have hnum : beta a x t ≤ boxEnvelope A h t := by
    rw [beta_gap_form]
    have hA2 : A^2 ≤ a^2 := by nlinarith
    have hgap := mul_nonneg (sub_nonneg.mpr hh) ht.1
    have hab := mul_nonneg (sub_nonneg.mpr hA2) (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    unfold boxEnvelope
    nlinarith
  have hB0 := hb.trans hnum
  have hB1 := boxEnvelope_le_one (A := A) hh0 ht
  exact (Real.rpow_le_rpow hb hnum (hR.trans hRr)).trans
    (Real.rpow_le_rpow_of_exponent_ge ((beta_pos_on_unit ha ha1 hx ht.1 ht.2).trans_le hnum) hB1 hRr)

theorem rectangle_envelope_quotient_bound {a x A Z h t r R : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ≤ 1)
    (hA : 0 ≤ A) (hAa : A ≤ a) (haZ : a ≤ Z)
    (hh0 : 0 ≤ h) (hh : h ≤ 1-beta a x 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hr : 1 ≤ r) (hR : 0 ≤ R) (hRr : R ≤ r) (hsmall : (Z^2+h)/2 < 1) :
    beta a x t^r/(1-a*x*t) ≤ boxEnvelope A h t^R/(1-(Z^2+h)/2*t) := by
  have hgap := beta_quotient_gap_mono ha ha1 hx hh ht hr
  have ha2Z : a^2 ≤ Z^2 := by nlinarith
  have hAlow : A^2 ≤ a^2 := by nlinarith
  have hnum : boxEnvelope a h t ≤ boxEnvelope A h t := by
    have hmul := mul_nonneg (sub_nonneg.mpr hAlow) (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    unfold boxEnvelope
    nlinarith
  have hBa : 0 ≤ boxEnvelope a h t := boxEnvelope_nonneg (by nlinarith)
    (by have hb := beta_pos_on_unit ha ha1 hx (by norm_num : (0:ℝ)≤1) le_rfl; linarith) ht
  have hB0 := hBa.trans hnum
  have hgapnum : beta a x t ≤ boxEnvelope a h t := by
    rw [beta_gap_form]
    unfold boxEnvelope
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) ht.1]
  have hBpos := (beta_pos_on_unit ha ha1 hx ht.1 ht.2).trans_le (hgapnum.trans hnum)
  have hB1 := boxEnvelope_le_one (A := A) hh0 ht
  have hp := (Real.rpow_le_rpow hBa hnum (by linarith : 0 ≤ r)).trans
    (Real.rpow_le_rpow_of_exponent_ge hBpos hB1 hRr)
  have hd0 : 0 < 1-(Z^2+h)/2*t := by
    have hnonneg : 0 ≤ (Z^2+h)/2 := by positivity
    nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr ht.2)]
  have hd : 1-(Z^2+h)/2*t ≤ 1-(a^2+h)/2*t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha2Z) ht.1]
  exact hgap.trans (div_le_div₀ (Real.rpow_nonneg hB0 R) hp hd0 hd)

end QuadraticTangZhang
