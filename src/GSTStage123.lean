import GSTStage122

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage122

namespace GSTStage123

theorem affine_pow_weighted_integrable
    (rho a b : ℝ) (f : ℝ → ℝ)
    (hf : ∀ n : ℕ, IntegrableOn
      (fun t => f t * t ^ n * Real.exp (-rho * t)) (Ioi (0 : ℝ)))
    (k n : ℕ) :
    IntegrableOn
      (fun t => (a + b * t) ^ k * f t * t ^ n * Real.exp (-rho * t))
      (Ioi (0 : ℝ)) := by
  induction k generalizing n with
  | zero =>
      simpa only [pow_zero, one_mul] using hf n
  | succ k ih =>
      have h0 := (ih n).const_mul a
      have h1 := (ih (n + 1)).const_mul b
      have he :
          (fun t => a * ((a + b * t) ^ k * f t * t ^ n *
              Real.exp (-rho * t)) +
            b * ((a + b * t) ^ k * f t * t ^ (n + 1) *
              Real.exp (-rho * t))) =
          (fun t => (a + b * t) ^ (k + 1) * f t * t ^ n *
            Real.exp (-rho * t)) := by
        funext t
        simp only [pow_succ]
        ring
      rw [← he]
      exact h0.add h1

theorem mixed_envelope_integrable
    (x : StateData) (D : ℝ) :
    IntegrableOn
      (fun t => Real.exp (-x.rho * t) * (D * (1 + t)) *
        resourceVariationBound x t * x.U)
      (Ioi (0 : ℝ)) := by
  have hbase : ∀ n : ℕ, IntegrableOn
      (fun t : ℝ => (1 : ℝ) * t ^ n * Real.exp (-x.rho * t))
      (Ioi (0 : ℝ)) := by
    intro n
    simpa only [one_mul] using
      GSTStage04.discounted_monomial_integrable x.rho x.hrho n
  have hR : ∀ n : ℕ, IntegrableOn
      (fun t => (x.phiInitial + x.B * t) * t ^ n *
        Real.exp (-x.rho * t)) (Ioi (0 : ℝ)) := by
    intro n
    simpa only [pow_one, mul_one] using
      affine_pow_weighted_integrable x.rho x.phiInitial x.B
        (fun _ => 1) hbase 1 n
  have hP : IntegrableOn
      (fun t => (1 + t) * (x.phiInitial + x.B * t) * t *
        Real.exp (-x.rho * t)) (Ioi (0 : ℝ)) := by
    simpa only [pow_one, one_mul] using
      affine_pow_weighted_integrable x.rho 1 1
        (fun t => x.phiInitial + x.B * t) hR 1 1
  have he :
      (fun t => (D * x.eta * x.U ^ 2) *
        ((1 + t) * (x.phiInitial + x.B * t) * t *
          Real.exp (-x.rho * t))) =
      (fun t => Real.exp (-x.rho * t) * (D * (1 + t)) *
        resourceVariationBound x t * x.U) := by
    funext t
    unfold resourceVariationBound
    ring
  rw [← he]
  exact hP.const_mul (D * x.eta * x.U ^ 2)

theorem gap_envelope_integrable
    (x : StateData) (r : ℝ) :
    IntegrableOn
      (fun t => Real.exp (-x.rho * t) *
        (|x.q| * (stateVariationBound x t) ^ 2 + |r| * x.U ^ 2))
      (Ioi (0 : ℝ)) := by
  have hbase : ∀ n : ℕ, IntegrableOn
      (fun t : ℝ => (1 : ℝ) * t ^ n * Real.exp (-x.rho * t))
      (Ioi (0 : ℝ)) := by
    intro n
    simpa only [one_mul] using
      GSTStage04.discounted_monomial_integrable x.rho x.hrho n
  have hR : ∀ n : ℕ, IntegrableOn
      (fun t => (x.phiInitial + x.B * t) ^ 2 * t ^ n *
        Real.exp (-x.rho * t)) (Ioi (0 : ℝ)) := by
    intro n
    simpa only [mul_one] using
      affine_pow_weighted_integrable x.rho x.phiInitial x.B
        (fun _ => 1) hbase 2 n
  have hP : IntegrableOn
      (fun t => (1 + (x.eta * x.U) * t) ^ 2 *
        (x.phiInitial + x.B * t) ^ 2 * t ^ 2 *
        Real.exp (-x.rho * t)) (Ioi (0 : ℝ)) :=
    affine_pow_weighted_integrable x.rho 1 (x.eta * x.U)
      (fun t => (x.phiInitial + x.B * t) ^ 2) hR 2 2
  have hE : IntegrableOn
      (fun t : ℝ => Real.exp (-x.rho * t)) (Ioi (0 : ℝ)) := by
    simpa only [pow_zero, one_mul] using
      GSTStage04.discounted_monomial_integrable x.rho x.hrho 0
  have he :
      (fun t => (|x.q| * (x.c * x.U) ^ 2) *
        ((1 + (x.eta * x.U) * t) ^ 2 *
          (x.phiInitial + x.B * t) ^ 2 * t ^ 2 *
          Real.exp (-x.rho * t)) +
        (|r| * x.U ^ 2) * Real.exp (-x.rho * t)) =
      (fun t => Real.exp (-x.rho * t) *
        (|x.q| * (stateVariationBound x t) ^ 2 + |r| * x.U ^ 2)) := by
    funext t
    unfold stateVariationBound
    ring
  rw [← he]
  exact (hP.const_mul (|x.q| * (x.c * x.U) ^ 2)).add
    (hE.const_mul (|r| * x.U ^ 2))

end GSTStage123

#print axioms GSTStage123.affine_pow_weighted_integrable
#print axioms GSTStage123.mixed_envelope_integrable
#print axioms GSTStage123.gap_envelope_integrable
