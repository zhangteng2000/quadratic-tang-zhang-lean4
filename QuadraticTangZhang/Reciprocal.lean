import QuadraticTangZhang.Statement
import Sendov.Counterexample.Identities
import Mathlib.Tactic

/-! # Reciprocal critical coordinates without a pointwise bound on their norms -/

namespace QuadraticTangZhang
open Polynomial

noncomputable def criticalReciprocals (p : ℂ[X]) (a : ℂ) : Multiset ℂ :=
  p.derivative.roots.map (fun z => (a - z)⁻¹)

theorem criticalReciprocals_card (p : ℂ[X]) (a : ℂ) :
    (criticalReciprocals p a).card = p.natDegree - 1 := by
  simp only [criticalReciprocals, Multiset.card_map]
  rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_derivative]

theorem criticalReciprocals_ne_zero (p : ℂ[X]) (a : ℂ) (ha : p.derivative.eval a ≠ 0) :
    ∀ v ∈ criticalReciprocals p a, v ≠ 0 := by
  intro v hv
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hv
  apply inv_ne_zero
  intro heq
  have heq' := sub_eq_zero.mp heq
  exact ha (heq' ▸ isRoot_of_mem_roots hz)

theorem criticalReciprocals_factorization (p : ℂ[X]) (a : ℂ) :
    p.derivative = C ((p.natDegree : ℂ) * p.leadingCoeff) *
      (((criticalReciprocals p a).map (fun v => a - v⁻¹)).map (fun z => X - C z)).prod := by
  have hback : (criticalReciprocals p a).map (fun v => a - v⁻¹) = p.derivative.roots := by
    simp only [criticalReciprocals, Multiset.map_map]
    have hfn : (fun x : ℂ => a - ((a - x)⁻¹)⁻¹) = id := by funext x; simp
    change Multiset.map (fun x : ℂ => a - ((a - x)⁻¹)⁻¹) _ = _
    rw [hfn, Multiset.map_id]
  rw [hback]
  convert (IsAlgClosed.splits p.derivative).eq_prod_roots using 1
  rw [leadingCoeff_derivative]
  congr 2
  ring

theorem reciprocalEnergy_of_ne {a z : ℂ} (h : a ≠ z) :
    reciprocalEnergy a z = ENNReal.ofReal (Complex.normSq ((a - z)⁻¹)) := by
  have hpos : 0 < Complex.normSq (a - z) := Complex.normSq_pos.mpr (sub_ne_zero.mpr h)
  rw [reciprocalEnergy, Complex.normSq_inv, ENNReal.ofReal_inv_of_pos hpos,
    Complex.normSq_eq_norm_sq]

theorem ofReal_multiset_sum {S : Multiset ℝ} (hS : ∀ x ∈ S, 0 ≤ x) :
    ENNReal.ofReal S.sum = (S.map ENNReal.ofReal).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons x S ih =>
    have hx := hS x (Multiset.mem_cons_self _ _)
    have ht : ∀ y ∈ S, 0 ≤ y := fun y hy => hS y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.sum_cons, Multiset.map_cons]
    rw [ENNReal.ofReal_add hx (Multiset.sum_nonneg ht), ih ht]

theorem criticalEnergy_eq_ofReal (p : ℂ[X]) (a : ℂ) (ha : p.derivative.eval a ≠ 0) :
    criticalEnergy p a = ENNReal.ofReal ((criticalReciprocals p a).map Complex.normSq).sum := by
  rw [ofReal_multiset_sum (by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hx
    exact Complex.normSq_nonneg v)]
  simp only [criticalEnergy, criticalReciprocals, Multiset.map_map, Function.comp_def]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro z hz
  apply reciprocalEnergy_of_ne
  intro heq
  exact ha (heq ▸ isRoot_of_mem_roots hz)

theorem reciprocal_sum_le_of_energy_le (p : ℂ[X]) (a : ℂ) (ha : p.derivative.eval a ≠ 0)
    (henergy : criticalEnergy p a ≤ (p.natDegree - 1 : ℕ)) :
    ((criticalReciprocals p a).map fun v => ‖v‖ ^ 2).sum ≤ (p.natDegree - 1 : ℕ) := by
  rw [criticalEnergy_eq_ofReal p a ha] at henergy
  have h := ENNReal.toReal_mono (by simp) henergy
  have hn : 0 ≤ ((criticalReciprocals p a).map Complex.normSq).sum := by
    apply Multiset.sum_nonneg
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hx
    exact Complex.normSq_nonneg v
  rw [ENNReal.toReal_ofReal hn] at h
  simpa only [ENNReal.toReal_natCast, Complex.normSq_eq_norm_sq] using h

theorem multiset_variance_real (q : Multiset ℂ) (x : ℝ) :
    (q.map fun v => Complex.normSq (v - (x : ℂ))).sum =
      (q.map fun v => ‖v‖ ^ 2).sum - 2 * x * (q.map Complex.re).sum + q.card * x ^ 2 := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v q ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one, ← Complex.normSq_eq_norm_sq] at ih ⊢
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.normSq_apply]
    nlinarith

theorem multiset_mean_sq_le {q : Multiset ℂ} (hm : 0 < q.card) {x s : ℝ}
    (hx : (q.map Complex.re).sum = q.card * x)
    (hs : (q.map fun v => ‖v‖ ^ 2).sum = q.card * s) : x ^ 2 ≤ s := by
  have hnonneg : 0 ≤ (q.map fun v => Complex.normSq (v - (x : ℂ))).sum := by
    apply Multiset.sum_nonneg
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hy
    exact Complex.normSq_nonneg _
  rw [multiset_variance_real, hx, hs] at hnonneg
  have hmpos : (0 : ℝ) < q.card := by exact_mod_cast hm
  nlinarith

end QuadraticTangZhang
