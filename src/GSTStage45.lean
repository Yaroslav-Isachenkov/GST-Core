import GSTStage44
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage45

theorem state_lower_bound
    (x : StateData) (t : ℝ) (ht : 0 ≤ t) :
    x.omegaInitial * Real.exp (-x.a * t) ≤ state x t := by
  have hint : 0 ≤ ∫ s in (0 : ℝ)..t,
      GSTStage29.weightedInput
        (GSTStage29.resourceForcing x.u x.eta x.B x.phiInitial x.c)
        x.a s := by
    apply intervalIntegral.integral_nonneg ht
    intro s hs
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg x.hc
        (mul_nonneg
          (GSTStage30.resource_nonneg x.u x.eta x.B x.phiInitial s
            x.hB x.hphiInitial hs.1)
          (x.hu s hs.1).1))
  have h := mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (a := x.omegaInitial) hint)
    (Real.exp_pos (-x.a * t)).le
  simpa only [state, GSTStage29.omega, GSTStage29.linearState,
    mul_comm] using h

theorem state_positive
    (x : StateData) (ho : 0 < x.omegaInitial)
    (t : ℝ) (ht : 0 ≤ t) :
    0 < state x t := by
  exact lt_of_lt_of_le
    (mul_pos ho (Real.exp_pos _)) (state_lower_bound x t ht)

theorem exponential_tail_integrable
    (k t : ℝ) (hk : 0 < k) :
    IntegrableOn (fun s : ℝ => Real.exp (-k * (s - t))) (Ioi t) := by
  have heq :
      (fun s : ℝ => Real.exp (-k * (s - t))) =
      (fun s : ℝ => Real.exp (k * t) * Real.exp (-k * s)) := by
    funext s
    rw [show -k * (s - t) = k * t + -k * s by ring, Real.exp_add]
  rw [heq]
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hk) t).const_mul
    (Real.exp (k * t))

theorem exponential_tail_integral
    (k t : ℝ) (hk : 0 < k) :
    (∫ s in Ioi t, Real.exp (-k * (s - t))) = 1 / k := by
  have heq :
      (fun s : ℝ => Real.exp (-k * (s - t))) =
      (fun s : ℝ => Real.exp (k * t) * Real.exp (-k * s)) := by
    funext s
    rw [show -k * (s - t) = k * t + -k * s by ring, Real.exp_add]
  rw [heq, integral_const_mul,
    integral_exp_mul_Ioi (neg_neg_of_pos hk) t]
  calc
    Real.exp (k * t) * (-Real.exp (-k * t) / -k) =
        (Real.exp (k * t) * Real.exp (-k * t)) / k := by ring
    _ = 1 / k := by
      rw [← Real.exp_add,
        show k * t + -k * t = 0 by ring, Real.exp_zero]

theorem p_quantitative_upper
    (x : StateData) (hq : 0 ≤ x.q)
    (t : ℝ) (ht : 0 ≤ t) :
    p x t ≤ 2 * x.q *
      (x.target / (x.rho + x.a) -
        (x.omegaInitial * Real.exp (-x.a * t)) /
          (x.rho + x.a + x.a)) := by
  let k : ℝ := x.rho + x.a
  have hk : 0 < k :=
    lt_of_lt_of_le x.hrho (le_add_of_nonneg_right x.ha)
  have hka : 0 < k + x.a :=
    lt_of_lt_of_le hk (le_add_of_nonneg_right x.ha)
  let F : ℝ → ℝ := fun s =>
    Real.exp (-k * (s - t)) * (x.target - state x s)
  let G : ℝ → ℝ := fun s =>
    x.target * Real.exp (-k * (s - t)) -
      (x.omegaInitial * Real.exp (-x.a * t)) *
        Real.exp (-(k + x.a) * (s - t))
  obtain ⟨M, hM, hOmega⟩ := state_linear_growth x
  have hF : IntegrableOn F (Ioi t) :=
    (GSTStage22.p_integrable_and_bound
      (state x) x.rho x.a x.q x.target M t
      hk hM ht (state_continuousOn x) hOmega).1
  have htop : IntegrableOn
      (fun s : ℝ => x.target * Real.exp (-k * (s - t))) (Ioi t) :=
    (exponential_tail_integrable k t hk).const_mul x.target
  have hlow : IntegrableOn
      (fun s : ℝ => (x.omegaInitial * Real.exp (-x.a * t)) *
        Real.exp (-(k + x.a) * (s - t))) (Ioi t) :=
    (exponential_tail_integrable (k + x.a) t hka).const_mul
      (x.omegaInitial * Real.exp (-x.a * t))
  have hG : IntegrableOn G (Ioi t) := htop.sub hlow
  have hle : F ≤ᵐ[volume.restrict (Ioi t)] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hts : t < s := hs
    have hs0 : 0 ≤ s := le_trans ht hts.le
    have hexp :
        Real.exp (-k * (s - t)) * Real.exp (-x.a * s) =
          Real.exp (-x.a * t) *
            Real.exp (-(k + x.a) * (s - t)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      F s ≤ Real.exp (-k * (s - t)) *
          (x.target - x.omegaInitial * Real.exp (-x.a * s)) :=
        mul_le_mul_of_nonneg_left
          (sub_le_sub_left (state_lower_bound x s hs0) x.target)
          (Real.exp_pos _).le
      _ = x.target * Real.exp (-k * (s - t)) -
          x.omegaInitial *
            (Real.exp (-k * (s - t)) * Real.exp (-x.a * s)) := by ring
      _ = G s := by
        rw [hexp]
        dsimp [G]
        ring
  have hIntegral : (∫ s in Ioi t, F s) ≤ ∫ s in Ioi t, G s :=
    integral_mono_ae hF hG hle
  have hGvalue :
      (∫ s in Ioi t, G s) =
        x.target / k -
          (x.omegaInitial * Real.exp (-x.a * t)) / (k + x.a) := by
    change (∫ s in Ioi t,
      x.target * Real.exp (-k * (s - t)) -
        (x.omegaInitial * Real.exp (-x.a * t)) *
          Real.exp (-(k + x.a) * (s - t))) = _
    rw [integral_sub htop hlow, integral_const_mul,
      integral_const_mul, exponential_tail_integral k t hk,
      exponential_tail_integral (k + x.a) t hka]
    ring
  rw [hGvalue] at hIntegral
  have h := mul_le_mul_of_nonneg_left hIntegral
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hq)
  simpa only [p, GSTStage22.pCostate, F, k] using h

theorem p_strict_upper
    (x : StateData) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (t : ℝ) (ht : 0 ≤ t) :
    p x t < 2 * x.q * x.target / (x.rho + x.a) := by
  have hden : 0 < x.rho + x.a + x.a := by
    linarith [x.hrho, x.ha]
  have hcorrection :
      0 < (x.omegaInitial * Real.exp (-x.a * t)) /
        (x.rho + x.a + x.a) :=
    div_pos (mul_pos ho (Real.exp_pos _)) hden
  calc
    p x t ≤ 2 * x.q *
        (x.target / (x.rho + x.a) -
          (x.omegaInitial * Real.exp (-x.a * t)) /
            (x.rho + x.a + x.a)) :=
      p_quantitative_upper x hq.le t ht
    _ < 2 * x.q * (x.target / (x.rho + x.a)) :=
      mul_lt_mul_of_pos_left (sub_lt_self _ hcorrection)
        (mul_pos (by norm_num) hq)
    _ = 2 * x.q * x.target / (x.rho + x.a) := by ring

#print axioms state_lower_bound
#print axioms state_positive
#print axioms exponential_tail_integrable
#print axioms exponential_tail_integral
#print axioms p_quantitative_upper
#print axioms p_strict_upper

end GSTStage45
