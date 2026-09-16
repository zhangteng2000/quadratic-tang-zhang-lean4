import QuadraticTangZhang.Polar

/-! # The endpoint gain: positivity, chord bound, and logarithmic gain -/

namespace QuadraticTangZhang
open MeasureTheory

theorem rho_pos_of_polar {a x s : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hxs : x^2 ≤ s) {m : ℕ} (hm : 0 < m)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, polarQuadratic a x s t ^ ((m:ℝ)/2)) :
    0 < rho a x s := by
  have hs : 0 ≤ s := (sq_nonneg _).trans hxs
  have ha2 : a^2 < 1 := by nlinarith
  have he : (0 : ℝ) < m/2 := by positivity
  have hc : Continuous fun t : ℝ => polarQuadratic a x s t := by unfold polarQuadratic; fun_prop
  have hcp := (Real.continuous_rpow_const he.le).comp hc
  by_contra hneg
  have hr : rho a x s ≤ 0 := le_of_not_gt hneg
  have hle : ∀ t ∈ Set.Ioc (0 : ℝ) 1, polarQuadratic a x s t ^ ((m:ℝ)/2) ≤ 1 := by
    intro t ht
    have hch := polar_le_chord (a := a) (x := x) hs ht.1.le ht.2
    have hrt := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sub_nonneg.mpr ha2.le) ht.1.le) hr
    have hch1 : polarQuadratic a x s t ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha2.le) (sub_nonneg.mpr ht.2)]
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (polarQuadratic_nonneg hxs) hch1 he.le
  have hlt : polarQuadratic a x s 0 ^ ((m:ℝ)/2) < 1 := by
    simpa [polarQuadratic] using (Real.rpow_lt_rpow (sq_nonneg a) ha2 he)
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0:ℝ)<1) hcp.continuousOn continuous_const.continuousOn hle
    ⟨0, by simp, hlt⟩
  have hconst : (∫ _t in (0:ℝ)..1, (1:ℝ)) = 1 := by simp
  rw [hconst] at hi
  exact (not_lt_of_ge hpolar) hi

theorem chord_polar_bound {a x s : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hxs : x^2 ≤ s) {m : ℕ} (hm : 0 < m)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, polarQuadratic a x s t ^ ((m:ℝ)/2)) :
    (1+(1-a^2)*rho a x s)^((m:ℝ)/2+1) -
      a^(m+2) - ((m:ℝ)/2+1)*(1-a^2)*(1+rho a x s) ≥ 0 := by
  have hr := rho_pos_of_polar ha ha1 hxs hm hpolar
  have hs : 0 ≤ s := (sq_nonneg _).trans hxs
  have he : (0:ℝ) < m/2 := by positivity
  have ha2 : 0 < 1-a^2 := by nlinarith
  let d := (1-a^2)*(1+rho a x s)
  have hd : 0 < d := mul_pos ha2 (by linarith)
  have hc : Continuous fun t : ℝ => polarQuadratic a x s t := by unfold polarQuadratic; fun_prop
  have hcPow := (Real.continuous_rpow_const he.le).comp hc
  have hl : Continuous fun t : ℝ => (a^2+d*t)^((m:ℝ)/2) :=
    (Real.continuous_rpow_const he.le).comp (by fun_prop)
  have hi : 1 ≤ ∫ t in (0:ℝ)..1, (a^2+d*t)^((m:ℝ)/2) := by
    apply hpolar.trans
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hcPow.intervalIntegrable _ _) (hl.intervalIntegrable _ _)
    intro t ht
    exact Real.rpow_le_rpow (polarQuadratic_nonneg hxs)
      (polar_le_chord hs ht.1 ht.2) he.le
  have heval := intervalIntegral.mul_integral_comp_add_mul
    (f := fun t : ℝ => t^((m:ℝ)/2)) (a := 0) (b := 1) d (a^2)
  rw [integral_rpow (Or.inl (by linarith : (-1:ℝ)<(m:ℝ)/2))] at heval
  simp only [mul_one, mul_zero, add_zero] at heval
  have hpow : (a^2)^((m:ℝ)/2+1) = a^(m+2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha, ← Real.rpow_natCast a (m+2)]
    congr 1
    push_cast
    ring
  have hend : a^2+d = 1+(1-a^2)*rho a x s := by dsimp [d]; ring
  rw [hpow, hend] at heval
  have hmul := mul_le_mul_of_nonneg_left hi hd.le
  rw [mul_one, heval, le_div_iff₀ (by linarith : (0:ℝ)<(m:ℝ)/2+1)] at hmul
  dsimp [d] at hmul
  nlinarith

theorem rho_log_lower_bound {a x s : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hxs : x^2 ≤ s) {m : ℕ} (hm : 0 < m)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, polarQuadratic a x s t ^ ((m:ℝ)/2))
    (hlarge : 1 < ((m:ℝ)/2+1)*(1-a^2)) :
    Real.log (((m:ℝ)/2+1)*(1-a^2)) / (((m:ℝ)/2+1)*(1-a^2)) ≤ rho a x s := by
  have hr := rho_pos_of_polar ha ha1 hxs hm hpolar
  have hch := chord_polar_bound ha ha1 hxs hm hpolar
  have he : (0:ℝ) < (m:ℝ)/2+1 := by positivity
  have ha2 : 0 < 1-a^2 := by nlinarith
  have hL : 0 < ((m:ℝ)/2+1)*(1-a^2) := by linarith
  have hb : 0 < 1+(1-a^2)*rho a x s := by positivity
  have hlow : ((m:ℝ)/2+1)*(1-a^2) ≤ (1+(1-a^2)*rho a x s)^((m:ℝ)/2+1) := by
    nlinarith [pow_nonneg ha (m+2), mul_nonneg hL.le hr.le]
  have hlog := Real.log_le_log hL hlow
  rw [Real.log_rpow hb] at hlog
  have hu := Real.log_le_sub_one_of_pos hb
  have hmul := mul_le_mul_of_nonneg_left hu he.le
  rw [div_le_iff₀ hL]
  nlinarith

end QuadraticTangZhang
