import QuadraticTangZhang.DirectScalar

/-! # D. Abstract rectangle exclusion from sound uniform enclosures

The numerical verifier must supply the upper bounds below. This theorem
then excludes every scalar configuration in the rectangle, rather than
testing a selected sample point. The boundary test additionally uses a
uniform bound for E/(1-a^2).
-/

namespace QuadraticTangZhang

def RectangleTests (aL aU CU EU FU RU TU tailU : ℝ) : Prop :=
  FU+RU+TU < 1 ∨
  (2*CU ≤ aU ∧ aU+EU < 1) ∨
  (0 < CU ∧ EU < 1 ∧ 4*(aU+CU)^3 < 27*CU*(1-EU)^2) ∨
  (2*CU ≤ aL ∧ tailU < 1/4)

theorem degree_term_mono {m M : ℕ} (hmM : m ≤ M) {a A : ℝ}
    (ha : 0 ≤ a) (haA : a ≤ A) :
    (m:ℝ)*a/(m+1) ≤ (M:ℝ)*A/(M+1) := by
  have hmpos : (0:ℝ)<m+1 := by positivity
  have hMpos : (0:ℝ)<M+1 := by positivity
  have hmR : (m:ℝ) ≤ M := by exact_mod_cast hmM
  have hfrac : (m:ℝ)/(m+1) ≤ (M:ℝ)/(M+1) := by
    rw [div_le_div_iff₀ hmpos hMpos]
    nlinarith
  have h := mul_le_mul hfrac haA ha (by positivity : (0:ℝ) ≤ (M:ℝ)/(M+1))
  convert h using 1 <;> first | rfl | ring

/-- Four exclusion tests, with all scalar and enclosure assumptions explicit. -/
theorem abstract_rectangle_exclusion
    {a r C E F R T aL aU CU EU FU RU TU tailU : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (haL : aL ≤ a) (haU : a ≤ aU) (hCU : C ≤ CU) (hEU : E ≤ EU)
    (hFU : F ≤ FU) (hRU : R ≤ RU) (hTU : T ≤ TU)
    (htail : E ≤ (1-a^2)*tailU)
    (hcenter : 1 ≤ a*r+C*r*(1-r^2)+E) (hdirect : 1 ≤ F+T+R)
    (htest : RectangleTests aL aU CU EU FU RU TU tailU) : False := by
  have hCU0 : 0 ≤ CU := hC.trans hCU
  have haU0 : 0 ≤ aU := ha.trans haU
  have hrterm : 0 ≤ r*(1-r^2) := by nlinarith [sq_nonneg r, sq_nonneg (1-r)]
  have hcenterU : 1 ≤ aU*r+CU*r*(1-r^2)+EU := by
    have h1 := mul_le_mul_of_nonneg_right haU hr
    have h2 := mul_le_mul_of_nonneg_right hCU hrterm
    nlinarith
  rcases htest with hd | hm | hc | hb
  · linarith
  · exact exclude_center_monotone hCU0 hm.1 hr hr1 hm.2 hcenterU
  · exact exclude_center_cubic haU0 hc.1 hr hr1 hc.2.1 hc.2.2 hcenterU
  · have hCa : 2*C ≤ a := by linarith [hb.1]
    have hg : 0 < 1-a^2 := by nlinarith
    have hE : E < (1-a^2)/4 := by nlinarith [mul_lt_mul_of_pos_left hb.2 hg]
    exact exclude_center_boundary ha ha1 hC hCa hr hr1 hE hcenter

/-- The first three tests do not require a boundary-tail enclosure. -/
theorem abstract_rectangle_exclusion_basic
    {a r C E F R T aU CU EU FU RU TU : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (haU : a ≤ aU) (hCU : C ≤ CU) (hEU : E ≤ EU)
    (hFU : F ≤ FU) (hRU : R ≤ RU) (hTU : T ≤ TU)
    (hcenter : 1 ≤ a*r+C*r*(1-r^2)+E) (hdirect : 1 ≤ F+T+R)
    (htest : FU+RU+TU < 1 ∨ (2*CU ≤ aU ∧ aU+EU < 1) ∨
      (0 < CU ∧ EU < 1 ∧ 4*(aU+CU)^3 < 27*CU*(1-EU)^2)) : False := by
  have hCU0 : 0 ≤ CU := hC.trans hCU
  have haU0 : 0 ≤ aU := ha.trans haU
  have hrterm : 0 ≤ r*(1-r^2) := by nlinarith [sq_nonneg r, sq_nonneg (1-r)]
  have hcenterU : 1 ≤ aU*r+CU*r*(1-r^2)+EU := by
    have h1 := mul_le_mul_of_nonneg_right haU hr
    have h2 := mul_le_mul_of_nonneg_right hCU hrterm
    nlinarith
  rcases htest with hd | hm | hc
  · linarith
  · exact exclude_center_monotone hCU0 hm.1 hr hr1 hm.2 hcenterU
  · exact exclude_center_cubic haU0 hc.1 hr hr1 hc.2.1 hc.2.2 hcenterU

end QuadraticTangZhang
