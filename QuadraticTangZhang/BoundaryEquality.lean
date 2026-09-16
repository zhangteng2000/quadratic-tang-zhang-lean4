import QuadraticTangZhang.Rotation
import QuadraticTangZhang.Extremal

/-! # Equality at the normalized boundary root -/

namespace QuadraticTangZhang
open Polynomial

theorem multiset_boundary_rigidity (S : Multiset ℂ)
    (hfirst : (S.card : ℝ) ≤ (S.map Complex.re).sum)
    (hsq : (S.map Complex.normSq).sum = S.card) : ∀ q ∈ S, q = 1 := by
  have hnn : ∀ x ∈ S.map (fun q => Complex.normSq (q - 1)), (0 : ℝ) ≤ x := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hx
    exact Complex.normSq_nonneg _
  have hsum : (S.map fun q => Complex.normSq (q - 1)).sum = 0 := by
    have hnonneg := Multiset.sum_nonneg hnn
    rw [multiset_variance_one, hsq] at hnonneg ⊢
    linarith
  intro q hq
  have hz := Multiset.all_zero_of_le_zero_le_of_sum_eq_zero hnn hsum
    (Complex.normSq (q - 1)) (Multiset.mem_map_of_mem _ hq)
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hz)

theorem boundary_equality_critical_zero (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) (hpone : p.eval 1 = 0)
    (henergy : criticalEnergy p 1 = (p.natDegree - 1 : ℕ)) :
    ∀ z ∈ p.derivative.roots, z = 0 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdeg
  have hd0 : p.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hsimple : p.derivative.eval 1 ≠ 0 := by
    intro h
    have ht := main_at_common_zero ((mem_roots hd0).mpr h)
    rw [henergy] at ht
    exact lt_irrefl _ ht
  obtain ⟨P, hP⟩ : (X - C (1 : ℂ)) ∣ p := dvd_iff_isRoot.mpr hpone
  have hP1 : P.eval 1 ≠ 0 := by simpa [hP, derivative_mul] using hsimple
  have hP0 : P ≠ 0 := by intro h; simp [h] at hP1
  have hPr : ∀ z ∈ P.roots, ‖z‖ ≤ 1 := by
    intro z hz
    apply hroots z ((mem_roots hp0).mpr _)
    have hzval : P.eval z = 0 := isRoot_of_mem_roots hz
    simp [hP, hzval]
  have hdegP : P.natDegree = p.natDegree - 1 := by
    rw [hP, natDegree_mul (X_sub_C_ne_zero 1) hP0, natDegree_X_sub_C]
    omega
  let q := criticalReciprocals p 1
  have hcard : q.card = p.natDegree - 1 := criticalReciprocals_card p 1
  have hfirst : (q.card : ℝ) ≤ (q.map Complex.re).sum := by
    rw [hcard, ← hdegP]
    have h := boundary_firstMoment_factored P hP1 hPr
    simpa only [q, criticalReciprocals, hP, Multiset.map_map, Function.comp_def, one_div] using h
  have hnonneg : 0 ≤ (q.map Complex.normSq).sum := by
    apply Multiset.sum_nonneg
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hx
    exact Complex.normSq_nonneg v
  have hsq : (q.map Complex.normSq).sum = q.card := by
    rw [criticalEnergy_eq_ofReal p 1 hsimple] at henergy
    have h := congrArg ENNReal.toReal henergy
    rw [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_natCast] at h
    simpa only [hcard] using h
  have hq := multiset_boundary_rigidity q hfirst hsq
  intro z hz
  have h := hq ((1 - z)⁻¹) (Multiset.mem_map_of_mem _ hz)
  have h' : (1 : ℂ) - z = 1 := inv_eq_one.mp h
  linear_combination -h'

theorem derivative_monomial_of_critical_zero (p : ℂ[X])
    (hz : ∀ z ∈ p.derivative.roots, z = 0) :
    p.derivative = C (p.leadingCoeff * p.natDegree) * X ^ (p.natDegree - 1) := by
  have hfac := (IsAlgClosed.splits p.derivative).eq_prod_roots
  have hmap : (p.derivative.roots.map (fun z => X - C z)) =
      p.derivative.roots.map (fun _ => (X : ℂ[X])) := by
    apply Multiset.map_congr rfl
    intro z hmem
    simp [hz z hmem]
  rw [hmap] at hfac
  change p.derivative = C p.derivative.leadingCoeff *
    (p.derivative.roots.map (Function.const ℂ (X : ℂ[X]))).prod at hfac
  rw [Multiset.map_const, Multiset.prod_replicate, leadingCoeff_derivative,
    ← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_derivative] at hfac
  exact hfac

theorem boundary_polynomial_of_equality (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) (hpone : p.eval 1 = 0)
    (henergy : criticalEnergy p 1 = (p.natDegree - 1 : ℕ)) :
    p = extremalPolynomial p.leadingCoeff 1 p.natDegree := by
  have hm := derivative_monomial_of_critical_zero p
    (boundary_equality_critical_zero p hdeg hroots hpone henergy)
  have hd : (p - extremalPolynomial p.leadingCoeff 1 p.natDegree).derivative = 0 := by
    rw [derivative_sub, hm, extremal_derivative, sub_self]
  have hc := eq_C_of_derivative_eq_zero hd
  have hval : (p - extremalPolynomial p.leadingCoeff 1 p.natDegree).eval 1 = 0 := by
    simp [hpone, extremalPolynomial]
  have hcoef : (p - extremalPolynomial p.leadingCoeff 1 p.natDegree).coeff 0 = 0 := by
    have h := congrArg (fun P : ℂ[X] => P.eval 1) hc
    simpa [hval] using h.symm
  apply sub_eq_zero.mp
  rw [hc, hcoef, map_zero]

/-- A polynomial whose critical points all vanish is determined by any one root. -/
theorem polynomial_of_critical_zero (p : ℂ[X]) {a : ℂ} (hpa : p.eval a = 0)
    (hz : ∀ z ∈ p.derivative.roots, z = 0) :
    p = extremalPolynomial p.leadingCoeff (a ^ p.natDegree) p.natDegree := by
  have hd : (p - extremalPolynomial p.leadingCoeff (a ^ p.natDegree) p.natDegree).derivative = 0 := by
    rw [derivative_sub, derivative_monomial_of_critical_zero p hz, extremal_derivative, sub_self]
  have hc := eq_C_of_derivative_eq_zero hd
  have hval : (p - extremalPolynomial p.leadingCoeff (a ^ p.natDegree) p.natDegree).eval a = 0 := by
    simp [hpa, extremalPolynomial]
  have hcoef : (p - extremalPolynomial p.leadingCoeff (a ^ p.natDegree) p.natDegree).coeff 0 = 0 := by
    have h := congrArg (fun P : ℂ[X] => P.eval a) hc
    simpa [hval] using h.symm
  apply sub_eq_zero.mp
  rw [hc, hcoef, map_zero]

theorem extremal_of_unit_circle_equality (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) {a : ℂ} (hpa : p.eval a = 0) (ha : ‖a‖ = 1)
    (heq : criticalEnergy p a = (p.natDegree - 1 : ℕ)) : Extremal p := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdeg
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hd := natDegree_rotatePolynomial ha0 p
  have hr : (rotatePolynomial a p).eval 1 = 0 := by simpa using hpa
  have he : criticalEnergy (rotatePolynomial a p) 1 =
      ((rotatePolynomial a p).natDegree - 1 : ℕ) := by
    rw [hd, criticalEnergy_rotation ha p 1, mul_one, heq]
  have hz := boundary_equality_critical_zero (rotatePolynomial a p)
    (by simpa [hd] using hdeg) (roots_rotatePolynomial ha hp0 hroots) hr he
  have hcrit : ∀ z ∈ p.derivative.roots, z = 0 := by
    intro z hmem
    rw [← critical_roots_rotation ha0 p] at hmem
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hmem
    rw [hz w hw, mul_zero]
  exact ⟨p.leadingCoeff, a ^ p.natDegree, leadingCoeff_ne_zero.mpr hp0,
    by simp [norm_pow, ha], polynomial_of_critical_zero p hpa hcrit⟩

theorem energy_of_extremal (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    {a : ℂ} (hpa : p.eval a = 0) (hext : Extremal p) :
    criticalEnergy p a = (p.natDegree - 1 : ℕ) := by
  obtain ⟨c, ω, hc, hω, hform⟩ := hext
  have hpform : p = extremalPolynomial c ω p.natDegree := hform
  have hr : (extremalPolynomial c ω p.natDegree).eval a = 0 := by rw [← hpform, hpa]
  have h := extremal_energy hc hω (by omega : 0 < p.natDegree) hr
  rw [← hpform] at h
  exact h

theorem unit_circle_equality_iff (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hroots : RootsInClosedDisk p) {a : ℂ} (hpa : p.eval a = 0) (ha : ‖a‖ = 1) :
    criticalEnergy p a = (p.natDegree - 1 : ℕ) ↔ Extremal p :=
  ⟨extremal_of_unit_circle_equality p hdeg hroots hpa ha, energy_of_extremal p hdeg hpa⟩

end QuadraticTangZhang
