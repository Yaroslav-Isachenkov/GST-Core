import GSTStage101

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage34

namespace GSTStage102

theorem competitor_eq_of_integral_balance
    (x : StateData) (a Omega : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T)
    (hOmega : ContinuousOn Omega (Icc (0 : ℝ) T))
    (hbalance : ∀ t ∈ Icc (0 : ℝ) T,
      Omega t = x.omegaInitial -
        x.a * (∫ s in Icc (0 : ℝ) t, Omega s) +
        x.c * (∫ s in Icc (0 : ℝ) t,
          resource a x.eta x.B x.phiInitial s * a s)) :
    EqOn Omega (competitorState x a) (Icc (0 : ℝ) T) := by
  have hOmega' : ContinuousOn Omega (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT] using hOmega
  have ho : IntervalIntegrable Omega volume 0 T :=
    hOmega'.intervalIntegrable
  have hp : IntervalIntegrable
      (fun s => resource a x.eta x.B x.phiInitial s * a s) volume 0 T :=
    ha.continuousOn_mul
      (resource_continuousOn a x.eta x.B x.phiInitial T ha)

  let H : ℝ → ℝ := fun t =>
    x.omegaInitial - x.a * (∫ s in (0 : ℝ)..t, Omega s) +
      x.c * (∫ s in (0 : ℝ)..t,
        resource a x.eta x.B x.phiInitial s * a s)

  have hEq : EqOn Omega H (Icc (0 : ℝ) T) := by
    intro t ht
    have hset (f : ℝ → ℝ) :
        (∫ s in (0 : ℝ)..t, f s) =
          ∫ s in Icc (0 : ℝ) t, f s := by
      rw [intervalIntegral.integral_of_le ht.1,
        integral_Icc_eq_integral_Ioc]
    dsimp only [H]
    simp only [hset]
    exact hbalance t ht

  have hc : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => x.omegaInitial) 0 T := by
    simp only [AbsolutelyContinuousOnInterval,
      dist_self, Finset.sum_const_zero]
    exact tendsto_const_nhds
  have hiO : AbsolutelyContinuousOnInterval
      (fun t => ∫ s in (0 : ℝ)..t, Omega s) 0 T :=
    ho.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hiP : AbsolutelyContinuousOnInterval
      (fun t => ∫ s in (0 : ℝ)..t,
        resource a x.eta x.B x.phiInitial s * a s) 0 T :=
    hp.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hAC : AbsolutelyContinuousOnInterval H 0 T :=
    (hc.fun_sub (hiO.const_mul x.a)).fun_add (hiP.const_mul x.c)

  have hODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt H
        (-x.a * H t +
          x.c * (resource a x.eta x.B x.phiInitial t * a t)) t := by
    filter_upwards [ho.ae_hasDerivAt_integral,
      hp.ae_hasDerivAt_integral] with t hdo hdp
    intro hmem
    have htI : t ∈ Icc (0 : ℝ) T := by
      simpa only [uIcc_of_le hT] using hmem
    have hd : HasDerivAt H
        ((0 - x.a * Omega t) +
          x.c * (resource a x.eta x.B x.phiInitial t * a t)) t :=
      ((hasDerivAt_const t x.omegaInitial).sub
        ((hdo hmem 0 left_mem_uIcc).const_mul x.a)).add
        ((hdp hmem 0 left_mem_uIcc).const_mul x.c)
    have he :
        (0 - x.a * Omega t) +
            x.c * (resource a x.eta x.B x.phiInitial t * a t) =
          -x.a * H t +
            x.c * (resource a x.eta x.B x.phiInitial t * a t) := by
      rw [← hEq htI]
      ring
    rw [he] at hd
    exact hd

  have hinit : H 0 = x.omegaInitial := by
    simp [H]
  have hrepr := GSTStage30.omega_representation
    a H x.eta x.B x.phiInitial x.a x.c x.omegaInitial T
    hT ha hAC hODE hinit
  intro t ht
  exact (hEq ht).trans (hrepr ht)

end GSTStage102

#print axioms GSTStage102.competitor_eq_of_integral_balance
