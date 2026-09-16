import QuadraticTangZhang.ExponentialIntegrals
import Mathlib.Analysis.Convex.Jensen

namespace QuadraticTangZhang
open MeasureTheory

theorem beta_near_initial_bound {a x t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : a/2 ≤ x) (hx1 : x ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1/4) :
    beta a x t ≤ 1-3*a^2*t/4 ∧ 3/4 ≤ 1-a*x*t := by
  have h1 := mul_nonneg (mul_nonneg ha ht) (show 0 ≤ 2*x-a by linarith)
  have h2 := mul_nonneg (mul_nonneg (sq_nonneg a) ht) (show 0 ≤ 1/4-t by linarith)
  have h3 := mul_nonneg (mul_nonneg ha ht) (sub_nonneg.mpr hx1)
  have h4 := mul_nonneg ht (sub_nonneg.mpr ha1)
  unfold beta
  constructor <;> nlinarith

theorem beta_convex (a x : ℝ) : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (beta a x) := by
  apply (boxEnvelope_convex a (1-beta a x 1)).congr
  intro t ht
  exact (beta_gap_form a x t).symm

theorem beta_near_tail_bound {a x t v : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (ha2 : 9/10 ≤ a^2) (hx : a/2 ≤ x) (hx1 : x ≤ 1)
    (ht : t ∈ Set.Icc (1/4:ℝ) 1) (hv : 0 ≤ v) :
    beta a x t^v ≤ ((133:ℝ)/160)^v+beta a x 1^v ∧ beta a x t/(1-a*x*t) ≤ 2 := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hb := beta_pos_on_unit ha ha1 hx1 ht0 ht.2
  have hb1 := beta_pos_on_unit ha ha1 hx1 (by norm_num : (0:ℝ)≤1) le_rfl
  have hquarter := (beta_near_initial_bound ha ha1.le hx hx1 (by norm_num : (0:ℝ)≤1/4) le_rfl).1
  have hquarter' : beta a x (1/4) ≤ 133/160 := by nlinarith
  have hmax := (beta_convex a x).le_max_of_mem_Icc
    (by norm_num : (1/4:ℝ) ∈ Set.Icc 0 1) (by norm_num : (1:ℝ) ∈ Set.Icc 0 1) ht
  have hmax' := hmax.trans (max_le_max hquarter' (le_refl (beta a x 1)))
  constructor
  · rcases le_total ((133:ℝ)/160) (beta a x 1) with h | h
    · rw [max_eq_right h] at hmax'
      have hp := Real.rpow_le_rpow hb.le hmax' hv
      linarith [Real.rpow_nonneg (by norm_num : (0:ℝ)≤133/160) v]
    · rw [max_eq_left h] at hmax'
      have hp := Real.rpow_le_rpow hb.le hmax' hv
      linarith [Real.rpow_nonneg hb1.le v]
  · rw [div_le_iff₀ (origin_gap_pos ha ha1 hx1 ht0 ht.2)]
    have ha2' : a^2 ≤ 1 := by nlinarith
    have ht2 : t^2 ≤ 1 := by nlinarith [ht.2]
    have hh := mul_nonneg (sub_nonneg.mpr ha2') (sq_nonneg t)
    unfold beta
    nlinarith

theorem near_center_integral_bound {m : ℕ} (hm : 5 ≤ m) {a x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (ha2 : 9/10 ≤ a^2) (hx : a/2 ≤ x) (hx1 : x ≤ 1) :
    centerIntegral m a x ≤ (8/3:ℝ)/(3*a^2*((m-1:ℕ):ℝ)/8)^3 +
      2*(((133:ℝ)/160)^(((m:ℝ)-3)/2)+beta a x 1^(((m:ℝ)-3)/2)) := by
  let r := ((m-1:ℕ):ℝ)/2
  let v := ((m:ℝ)-3)/2
  let k := 3*a^2*((m-1:ℕ):ℝ)/8
  let f : ℝ → ℝ := fun t => t^2*beta a x t^r/(1-a*x*t)
  let T := ((133:ℝ)/160)^v+beta a x 1^v
  have hmcast : ((m-1:ℕ):ℝ)=(m:ℝ)-1 := by rw [Nat.cast_sub (show 1 ≤ m by omega),Nat.cast_one]
  have hmR : (5:ℝ) ≤ m := by exact_mod_cast hm
  have hmcpos : (0:ℝ) < (m-1:ℕ) := by rw [hmcast]; linarith
  have hr : 0 < r := by dsimp [r]; rw [hmcast]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have hrv : r=v+1 := by dsimp [r,v]; rw [hmcast]; ring
  have hk : 0 < k := by dsimp [k]; positivity
  have hcb : Continuous fun t : ℝ => beta a x t := by unfold beta; fun_prop
  have hcf : ContinuousOn f (Set.Icc (0:ℝ) 1) :=
    (((continuous_id.pow 2).mul ((Real.continuous_rpow_const hr.le).comp hcb)).continuousOn).div
      (by fun_prop) (fun t ht => (origin_gap_pos ha.le ha1 hx1 ht.1 ht.2).ne')
  have hi (u w : ℝ) (hu : 0 ≤ u) (huw : u ≤ w) (hw : w ≤ 1) : IntervalIntegrable f volume u w := by
    apply (hcf.mono _).intervalIntegrable_of_Icc huw
    intro t ht
    exact ⟨hu.trans ht.1,ht.2.trans hw⟩
  have hfirst : (∫ t in (0:ℝ)..(1/4), f t) ≤ (8/3:ℝ)/k^3 := by
    have him : (∫ t in (0:ℝ)..(1/4), f t) ≤
        ∫ t in (0:ℝ)..(1/4), (4/3:ℝ)*(t^2*Real.exp (-k*t)) := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hi _ _ (by norm_num) (by norm_num) (by norm_num))
        ((by fun_prop : Continuous (fun t : ℝ => (4/3:ℝ)*(t^2*Real.exp (-k*t)))).intervalIntegrable _ _)
      intro t ht
      have ht1 : t ≤ 1 := by linarith [ht.2]
      have hb := beta_pos_on_unit ha.le ha1 hx1 ht.1 ht1
      have hbd := beta_near_initial_bound ha.le ha1.le hx hx1 ht.1 ht.2
      have hp := rpow_le_exp_gap hb.le hbd.1 hr.le
      have heq : -r*(3*a^2*t/4) = -k*t := by dsimp [r,k]; ring
      rw [heq] at hp
      have hden := origin_gap_pos ha.le ha1 hx1 ht.1 ht1
      have hdiv := div_le_div₀ (Real.exp_pos (-k*t)).le hp (by norm_num : (0:ℝ)<3/4) hbd.2
      have hh := mul_le_mul_of_nonneg_left hdiv (sq_nonneg t)
      dsimp [f]
      convert hh using 1 <;> first | rfl | ring
    rw [intervalIntegral.integral_const_mul] at him
    have hInt := mul_le_mul_of_nonneg_left (integral_sq_exp_neg_le hk (by norm_num : (0:ℝ)≤1/4)) (by norm_num : (0:ℝ)≤4/3)
    apply him.trans
    convert hInt using 1 <;> first | rfl | ring
  have hT : 0 ≤ T := add_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (beta_pos_on_unit ha.le ha1 hx1 (by norm_num : (0:ℝ)≤1) le_rfl).le _)
  have hlast : (∫ t in (1/4:ℝ)..1, f t) ≤ 2*T := by
    have him : (∫ t in (1/4:ℝ)..1, f t) ≤ ∫ _t in (1/4:ℝ)..1, 2*T := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hi _ _ (by norm_num) (by norm_num) le_rfl)
        (continuous_const.intervalIntegrable _ _)
      intro t ht
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hb := beta_pos_on_unit ha.le ha1 hx1 ht0 ht.2
      have htail := beta_near_tail_bound ha.le ha1 ha2 hx hx1 ht hv
      have hpow : beta a x t^r=beta a x t^v*beta a x t := by
        rw [hrv,Real.rpow_add hb,Real.rpow_one]
      have hh := mul_le_mul htail.1 htail.2
        (div_nonneg hb.le (origin_gap_pos ha.le ha1 hx1 ht0 ht.2).le) hT
      have ht2 : t^2 ≤ 1 := by nlinarith [ht.2]
      have hh2 := mul_le_mul_of_nonneg_left hh (sq_nonneg t)
      have hfinal := mul_le_mul_of_nonneg_right ht2 (show 0 ≤ T*2 by positivity)
      dsimp [f]
      rw [hpow]
      have htotal : t^2*(beta a x t^v*(beta a x t/(1-a*x*t))) ≤ T*2 :=
        hh2.trans (by simpa only [T,one_mul] using hfinal)
      convert htotal using 1 <;> first | rfl | ring
    simp only [intervalIntegral.integral_const,smul_eq_mul] at him
    nlinarith
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hi 0 (1/4) (by norm_num) (by norm_num) (by norm_num))
    (hi (1/4) 1 (by norm_num) (by norm_num) le_rfl)
  change (∫ t in (0:ℝ)..1, f t) ≤ _
  rw [← hadd]
  exact add_le_add hfirst hlast

end QuadraticTangZhang
