import GSTStage99

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11

namespace GSTStage100

theorem resource_eq_of_integral_balance
    (a Phi : ℝ → ℝ) (eta B initial T : ℝ)
    (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T)
    (hPhi : ContinuousOn Phi (Icc (0 : ℝ) T))
    (hbalance : ∀ t ∈ Icc (0 : ℝ) T,
      Phi t = initial + B * t -
        eta * (∫ s in Icc (0 : ℝ) t, Phi s * a s)) :
    EqOn Phi (resource a eta B initial) (Icc (0 : ℝ) T) := by
  have hPhi' : ContinuousOn Phi (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT] using hPhi
  have hp : IntervalIntegrable (fun s => Phi s * a s) volume 0 T :=
    ha.continuousOn_mul hPhi'

  let H : ℝ → ℝ := fun t =>
    initial + B * t - eta * (∫ s in (0 : ℝ)..t, Phi s * a s)

  have hEq : EqOn Phi H (Icc (0 : ℝ) T) := by
    intro t ht
    have hset :
        (∫ s in (0 : ℝ)..t, Phi s * a s) =
          ∫ s in Icc (0 : ℝ) t, Phi s * a s := by
      rw [intervalIntegral.integral_of_le ht.1,
        integral_Icc_eq_integral_Ioc]
    dsimp only [H]
    rw [hset]
    exact hbalance t ht

  have hc : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => initial) 0 T := by
    simp only [AbsolutelyContinuousOnInterval,
      dist_self, Finset.sum_const_zero]
    exact tendsto_const_nhds

  have hlin : AbsolutelyContinuousOnInterval
      (fun t : ℝ => B * t) 0 T := by
    have hl := GSTStage11.cumulative_ac
      (fun _ : ℝ => (1 : ℝ)) B T intervalIntegrable_const
    change AbsolutelyContinuousOnInterval
      (fun t : ℝ => B * ∫ s in (0 : ℝ)..t, (1 : ℝ)) 0 T at hl
    simpa only [intervalIntegral.integral_const, sub_zero,
      smul_eq_mul, mul_one] using hl

  have hi : AbsolutelyContinuousOnInterval
      (fun t => ∫ s in (0 : ℝ)..t, Phi s * a s) 0 T :=
    hp.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc

  have hAC : AbsolutelyContinuousOnInterval H 0 T :=
    (hc.fun_add hlin).fun_sub (hi.const_mul eta)

  have hODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt H (B - eta * a t * H t) t := by
    filter_upwards [hp.ae_hasDerivAt_integral] with t ht
    intro hmem
    have htI : t ∈ Icc (0 : ℝ) T := by
      simpa only [uIcc_of_le hT] using hmem
    have hdI := ht hmem 0 left_mem_uIcc
    have hd : HasDerivAt H (B - eta * (Phi t * a t)) t := by
      simpa only [H, id_eq, mul_one, zero_add] using
        (((hasDerivAt_const t initial).add
          ((hasDerivAt_id t).const_mul B)).sub (hdI.const_mul eta))
    have he : B - eta * (Phi t * a t) =
        B - eta * a t * H t := by
      rw [← hEq htI]
      ring
    rw [he] at hd
    exact hd

  have hinit : H 0 = initial := by
    simp [H]
  have hrepr := GSTStage13.resource_representation
    a H eta B initial T hT ha hAC hODE hinit
  intro t ht
  exact (hEq ht).trans (hrepr ht)

end GSTStage100

#print axioms GSTStage100.resource_eq_of_integral_balance
