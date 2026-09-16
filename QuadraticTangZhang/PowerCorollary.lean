import QuadraticTangZhang.LowDegreeEquality
import QuadraticTangZhang.PowerMeans
import Mathlib.Data.List.OfFn

/-! # Real exponents at least two, with infinity at common critical points -/

namespace QuadraticTangZhang
open Polynomial
open scoped BigOperators

noncomputable def criticalPowerEnergy (p : ℂ[X]) (a : ℂ) (ell : ℝ) : ENNReal :=
  (p.derivative.roots.map (fun z => reciprocalEnergy a z ^ (ell/2))).sum

theorem criticalPowerEnergy_two (p : ℂ[X]) (a : ℂ) :
    criticalPowerEnergy p a 2 = criticalEnergy p a := by
  simp [criticalPowerEnergy, criticalEnergy]

theorem reciprocalEnergy_rpow (a z : ℂ) {ell : ℝ} (hell : 0 ≤ ell) :
    reciprocalEnergy a z ^ (ell/2) = (ENNReal.ofReal (‖a-z‖ ^ ell))⁻¹ := by
  rw [reciprocalEnergy, ENNReal.inv_rpow,
    ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by positivity)]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  norm_num
  ring

theorem ennreal_mean_power {m : ℕ} (hm : 0 < m) (u : Fin m → ENNReal)
    {r : ℝ} (hr : 1 ≤ r) :
    ((∑ i, u i) / m) ^ r ≤ (∑ i, u i ^ r) / m := by
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hw : (∑ _i : Fin m, (1 : ENNReal) / m) = 1 := by
    simp [nsmul_eq_mul, ENNReal.mul_inv_cancel hm0 (ENNReal.natCast_ne_top m)]
  have h := ENNReal.rpow_arith_mean_le_arith_mean_rpow Finset.univ
    (fun _ : Fin m => (1 : ENNReal) / m) u hw hr
  simp only [one_div, ← Finset.mul_sum] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem ennreal_power_sum_ge_card {m : ℕ} (hm : 0 < m) (u : Fin m → ENNReal)
    {r : ℝ} (hr : 1 ≤ r) (hs : (m : ENNReal) ≤ ∑ i, u i) :
    (m : ENNReal) ≤ ∑ i, u i ^ r := by
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hmt := ENNReal.natCast_ne_top m
  have havg : (1 : ENNReal) ≤ (∑ i, u i) / m := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmt), one_mul]
    exact hs
  have hpow := ENNReal.rpow_le_rpow havg (show 0 ≤ r by linarith)
  rw [ENNReal.one_rpow] at hpow
  have h := hpow.trans (ennreal_mean_power hm u hr)
  rwa [ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmt), one_mul] at h

theorem ennreal_power_equality {m : ℕ} (hm : 0 < m) (u : Fin m → ENNReal)
    {r : ℝ} (hr : 1 ≤ r) (hs : (m : ENNReal) ≤ ∑ i, u i)
    (heq : (∑ i, u i ^ r) = m) : (∑ i, u i) = m := by
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hmt := ENNReal.natCast_ne_top m
  apply le_antisymm _ hs
  have h := ennreal_mean_power hm u hr
  rw [heq, ENNReal.div_self hm0 hmt] at h
  have hbase : (∑ i, u i) / m ≤ 1 := by
    rw [← ENNReal.one_rpow r] at h
    exact (ENNReal.rpow_le_rpow_iff (show 0 < r by linarith)).mp h
  rwa [ENNReal.div_le_iff hm0 hmt, one_mul] at hbase

theorem multiset_ennreal_power_sum (S : Multiset ENNReal) (hm : 0 < S.card)
    {r : ℝ} (hr : 1 ≤ r) (hs : (S.card : ENNReal) ≤ S.sum) :
    (S.card : ENNReal) ≤ (S.map (fun u => u ^ r)).sum ∧
      ((S.map (fun u => u ^ r)).sum = S.card → S.sum = S.card) := by
  induction S using Quotient.inductionOn with | h L =>
    have hsum (f : ENNReal → ENNReal) :
        (L.map f).sum = ∑ i : Fin L.length, f (L.get i) := by
      have h := congrArg (fun l : List ENNReal => (l.map f).sum) (List.ofFn_get L)
      simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def] using h.symm
    have hid : L.sum = ∑ i : Fin L.length, L.get i := by
      simpa only [List.map_id, id_eq] using hsum id
    change (L.length : ENNReal) ≤ L.sum at hs
    rw [hid] at hs
    change (L.length : ENNReal) ≤ (L.map (fun u => u ^ r)).sum ∧
      ((L.map (fun u => u ^ r)).sum = L.length → L.sum = L.length)
    rw [hsum, hid]
    exact ⟨ennreal_power_sum_ge_card hm L.get hr hs, ennreal_power_equality hm L.get hr hs⟩

theorem power_corollary_of_quadratic (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree) (a : ℂ)
    {ell : ℝ} (hell : 2 ≤ ell) (hs : (p.natDegree - 1 : ℕ) ≤ criticalEnergy p a) :
    (p.natDegree - 1 : ℕ) ≤ criticalPowerEnergy p a ell ∧
      (criticalPowerEnergy p a ell = (p.natDegree - 1 : ℕ) →
        criticalEnergy p a = (p.natDegree - 1 : ℕ)) := by
  have hcard : (p.derivative.roots.map (reciprocalEnergy a)).card = p.natDegree - 1 := by
    rw [Multiset.card_map, ← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_derivative]
  have h := multiset_ennreal_power_sum (p.derivative.roots.map (reciprocalEnergy a))
    (by rw [hcard]; omega) (show 1 ≤ ell/2 by linarith)
    (by simpa only [hcard, criticalEnergy] using hs)
  simpa only [hcard, Multiset.map_map, Function.comp_def, criticalEnergy, criticalPowerEnergy] using h

theorem power_energy_of_extremal (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    {a : ℂ} (hpa : p.eval a = 0) (hext : Extremal p) (ell : ℝ) :
    criticalPowerEnergy p a ell = (p.natDegree - 1 : ℕ) := by
  obtain ⟨c, ω, hc, hω, hform⟩ := hext
  change p = extremalPolynomial c ω p.natDegree at hform
  have hr : (extremalPolynomial c ω p.natDegree).eval a = 0 := by rw [← hform]; exact hpa
  have hnorm := extremal_root_norm hc hω (by omega : 0 < p.natDegree) hr
  have hroots : p.derivative.roots = (p.natDegree - 1) • ({0} : Multiset ℂ) := by
    have h := extremal_critical_roots (ω := ω) hc (by omega : 0 < p.natDegree)
    rw [← hform] at h
    exact h
  have hterm : reciprocalEnergy a 0 = 1 := by simp [reciprocalEnergy, hnorm]
  unfold criticalPowerEnergy
  rw [hroots]
  simp only [Multiset.map_nsmul, Multiset.map_singleton, Multiset.sum_nsmul,
    Multiset.sum_singleton, hterm, ENNReal.one_rpow, nsmul_eq_mul, mul_one]

theorem powers_degrees_two_to_five (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hdeg5 : p.natDegree ≤ 5) (hroots : RootsInClosedDisk p) {a : ℂ}
    (hpa : p.eval a = 0) {ell : ℝ} (hell : 2 ≤ ell) :
    (p.natDegree - 1 : ℕ) ≤ criticalPowerEnergy p a ell ∧
      (criticalPowerEnergy p a ell = (p.natDegree - 1 : ℕ) ↔ Extremal p) := by
  have h := power_corollary_of_quadratic p hdeg a hell (low_degree_inequality p hdeg hdeg5 hroots hpa)
  exact ⟨h.1, ⟨fun he => (low_degree_equality_iff p hdeg hdeg5 hroots hpa).mp (h.2 he),
    fun he => power_energy_of_extremal p hdeg hpa he ell⟩⟩

end QuadraticTangZhang
