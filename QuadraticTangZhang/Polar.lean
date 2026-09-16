import Sendov.Analytic.PolarBase
import QuadraticTangZhang.Scalar
import QuadraticTangZhang.SmallDegrees
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# The polar channel retaining the exact second moment

The AM--GM proof below adapts Sendov/Analytic/Polar.lean from teorth/sendov
(Apache-2.0; see vendor/PROVENANCE.md). Its pointwise unit-disk premise on q
is replaced by the exact second moment; individual q's need not have norm <= 1.
-/

namespace QuadraticTangZhang
open MeasureTheory

theorem prod_norm_le_exact_moment {q : Multiset ℂ} (hm : 0 < q.card)
    {a x s t : ℝ} (hx : (q.map Complex.re).sum = q.card * x)
    (hs : (q.map fun v => ‖v‖ ^ 2).sum = q.card * s) :
    (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod ≤
      polarQuadratic a x s t ^ ((q.card : ℝ) / 2) := by
  have hmpos : (0 : ℝ) < q.card := by exact_mod_cast hm
  let b := t * (1 - a ^ 2)
  have hcast (v : ℂ) : (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v =
      (a : ℂ) + (b : ℂ) * v := by dsimp [b]; push_cast; ring
  simp only [hcast]
  let M := (q.map (fun v => ‖(a : ℂ) + (b : ℂ) * v‖ ^ 2)).sum / q.card
  have hM : M = polarQuadratic a x s t := by
    dsimp [M]
    rw [Sendov.sum_norm_sq_split, hx, hs]
    dsimp [polarQuadratic, b]
    field_simp
  have hM0 : 0 ≤ M := by
    apply div_nonneg _ hmpos.le
    apply Multiset.sum_nonneg
    intro y hy
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hy
    exact sq_nonneg _
  have hamgm := Sendov.Multiset.prod_le_mean_pow
    (q.map fun v => ‖(a : ℂ) + (b : ℂ) * v‖ ^ 2) (by
      intro y hy
      obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hy
      exact sq_nonneg _)
  rw [Multiset.card_map, Sendov.prod_map_sq] at hamgm
  change _ ≤ M ^ q.card at hamgm
  have hsquare : (M ^ ((q.card : ℝ) / 2)) ^ 2 = M ^ q.card := by
    rw [← Real.rpow_natCast (M ^ ((q.card : ℝ) / 2)) 2, ← Real.rpow_mul hM0,
      ← Real.rpow_natCast M q.card]
    congr 1
    norm_num
  rw [← hsquare] at hamgm
  rw [← hM]
  nlinarith [Sendov.prod_map_norm_nonneg q (fun v => (a : ℂ) + (b : ℂ) * v),
    Real.rpow_nonneg hM0 ((q.card : ℝ) / 2)]

theorem exact_polar_inequality {q : Multiset ℂ} (hm : 0 < q.card)
    {a x s : ℝ} (hx : (q.map Complex.re).sum = q.card * x)
    (hs : (q.map fun v => ‖v‖ ^ 2).sum = q.card * s)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 ≤ ∫ t in (0 : ℝ)..1, polarQuadratic a x s t ^ ((q.card : ℝ) / 2) := by
  have hc : Continuous fun t : ℝ => polarQuadratic a x s t := by unfold polarQuadratic; fun_prop
  have hcPow := (Real.continuous_rpow_const (show (0 : ℝ) ≤ q.card / 2 by positivity)).comp hc
  apply hstar.trans
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((Sendov.continuous_prod_norm a q).intervalIntegrable _ _) (hcPow.intervalIntegrable _ _)
  intro t _
  exact prod_norm_le_exact_moment hm hx hs

theorem polarQuadratic_nonneg {a x s t : ℝ} (hxs : x ^ 2 ≤ s) :
    0 ≤ polarQuadratic a x s t := by
  have h := mul_nonneg (sq_nonneg ((1 - a ^ 2) * t)) (sub_nonneg.mpr hxs)
  dsimp [polarQuadratic]
  nlinarith [sq_nonneg (a + (1 - a ^ 2) * x * t)]

theorem polarQuadratic_le_square {a x s t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : x ≤ 1) (hs : s ≤ 1) (ht : 0 ≤ t) :
    polarQuadratic a x s t ≤ (a + (1 - a ^ 2) * t) ^ 2 := by
  have had : 0 ≤ 1 - a ^ 2 := by nlinarith
  have h1 := mul_nonneg (show 0 ≤ 2 * a * (1 - a ^ 2) * t by positivity) (sub_nonneg.mpr hx)
  have h2 := mul_nonneg (sq_nonneg ((1 - a ^ 2) * t)) (sub_nonneg.mpr hs)
  dsimp [polarQuadratic]
  nlinarith

theorem small_degree_polar_contradiction {a x s : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx : x ≤ 1) (hxs : x ^ 2 ≤ s) (hs : s ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) (hm4 : m ≤ 4)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, polarQuadratic a x s t ^ ((m : ℝ) / 2)) : False := by
  have hc : Continuous fun t : ℝ => polarQuadratic a x s t := by unfold polarQuadratic; fun_prop
  have hcPow := (Real.continuous_rpow_const (show (0 : ℝ) ≤ m / 2 by positivity)).comp hc
  have hlow : Continuous fun t : ℝ => (a + (1 - a ^ 2) * t) ^ m := by fun_prop
  have hle : (∫ t in (0 : ℝ)..1, polarQuadratic a x s t ^ ((m : ℝ) / 2)) ≤ smallIntegral a m := by
    unfold smallIntegral
    apply intervalIntegral.integral_mono_on (by norm_num) (hcPow.intervalIntegrable _ _)
      (hlow.intervalIntegrable _ _)
    intro t ht
    have ht0 := ht.1
    have hbase : 0 ≤ a + (1 - a ^ 2) * t := by
      have : 0 ≤ 1 - a ^ 2 := by nlinarith
      positivity
    have h := Real.rpow_le_rpow (polarQuadratic_nonneg hxs)
      (polarQuadratic_le_square ha.le ha1.le hx hs ht.1) (show (0 : ℝ) ≤ m / 2 by positivity)
    have hid : ((a + (1 - a ^ 2) * t) ^ 2 : ℝ) ^ ((m : ℝ) / 2) = (a + (1 - a ^ 2) * t) ^ m := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbase, ← Real.rpow_natCast _ m]
      congr 1
      norm_num
      ring
    rwa [hid] at h
  exact (not_lt_of_ge (hpolar.trans hle)) (smallIntegral_lt_one ha ha1 hm hm4)

end QuadraticTangZhang
