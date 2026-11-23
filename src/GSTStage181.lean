import GSTStage180

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29 GSTStage180

namespace GSTStage181

theorem source_lift_resource_ac
    (u : ℝ → ℝ) (eta B initial T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    AbsolutelyContinuousOnInterval (liftedResource u eta B initial) 0 T := by
  have hF := GSTStage12.resource_ac u eta 0 initial T hu
  have hlin : AbsolutelyContinuousOnInterval
      (fun t : ℝ => B * t) 0 T := by
    have h := cumulative_ac (fun _ : ℝ => (1 : ℝ)) B T
      intervalIntegrable_const
    change AbsolutelyContinuousOnInterval
      (fun t : ℝ => B * ∫ s in (0 : ℝ)..t, (1 : ℝ)) 0 T at h
    simpa using h
  exact hF.fun_add hlin

theorem source_lift_canonical_trajectories
    (u : ℝ → ℝ) (eta B initial a c omegaInitial U : ℝ)
    (hi : 0 < initial) (hB : 0 ≤ B)
    (hmeas : Measurable u)
    (hbound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U) :
    Measurable (liftedControl u eta B initial) ∧
    (∀ t : ℝ, 0 ≤ t →
      0 ≤ liftedControl u eta B initial t ∧
      liftedControl u eta B initial t ≤ U) ∧
    (∀ t : ℝ, 0 ≤ t →
      resource (liftedControl u eta B initial) eta B initial t =
        liftedResource u eta B initial t ∧
      omega (liftedControl u eta B initial) eta B initial a c omegaInitial t =
        omega u eta 0 initial a c omegaInitial t) := by
  have hvMeas := source_lift_control_measurable u eta B initial hmeas
  have hvBound : ∀ t : ℝ, 0 ≤ t →
      0 ≤ liftedControl u eta B initial t ∧
      liftedControl u eta B initial t ≤ U := by
    intro t ht
    have hb := (source_lift_bounds_and_flow
      u eta B initial t hi hB ht (hbound t ht).1).2.1
    exact ⟨hb.1, hb.2.trans (hbound t ht).2⟩
  have hu : ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable u volume 0 T := by
    intro T hT
    exact GSTStage27.bounded_control_integrable u U T hT hmeas hbound
  have hv : ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable (liftedControl u eta B initial) volume 0 T := by
    intro T hT
    exact GSTStage27.bounded_control_integrable
      (liftedControl u eta B initial) U T hT hvMeas hvBound
  refine ⟨hvMeas, hvBound, ?_⟩
  intro T hT
  have hGODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (liftedResource u eta B initial)
        (B - eta * liftedControl u eta B initial t *
          liftedResource u eta B initial t) t := by
    filter_upwards [GSTStage12.resource_ode_ae
      u eta 0 initial T (hu T hT)] with t hd
    intro ht
    have ht' : t ∈ Icc (0 : ℝ) T := by
      simpa only [uIcc_of_le hT] using ht
    have hflow := (source_lift_bounds_and_flow
      u eta B initial t hi hB ht'.1 (hbound t ht'.1).1).2.2
    have hraw : HasDerivAt (liftedResource u eta B initial)
        ((0 - eta * u t * resource u eta 0 initial t) + B) t := by
      simpa only [liftedResource, Pi.add_apply, id_eq, mul_one] using
        (hd ht).add ((hasDerivAt_id t).const_mul B)
    have hrate :
        B - eta * liftedControl u eta B initial t *
          liftedResource u eta B initial t =
        (0 - eta * u t * resource u eta 0 initial t) + B := by
      calc
        B - eta * liftedControl u eta B initial t *
            liftedResource u eta B initial t =
            B - eta * (liftedResource u eta B initial t *
              liftedControl u eta B initial t) := by ring
        _ = (0 - eta * u t * resource u eta 0 initial t) + B := by
          rw [hflow]
          ring
    rw [hrate]
    exact hraw
  have hGinitial :
      liftedResource u eta B initial 0 = initial :=
    (source_lift_initial u eta B initial hi).1
  have hGrep := GSTStage13.resource_representation
    (liftedControl u eta B initial) (liftedResource u eta B initial)
    eta B initial T hT (hv T hT)
    (source_lift_resource_ac u eta B initial T (hu T hT))
    hGODE hGinitial
  have hsol := GSTStage29.omega_solution
    u eta 0 initial a c omegaInitial T (hu T hT)
  have hOODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (omega u eta 0 initial a c omegaInitial)
        (-a * omega u eta 0 initial a c omegaInitial t +
          c * (resource (liftedControl u eta B initial) eta B initial t *
            liftedControl u eta B initial t)) t := by
    filter_upwards [hsol.2] with t hd
    intro ht
    have ht' : t ∈ Icc (0 : ℝ) T := by
      simpa only [uIcc_of_le hT] using ht
    have hflow := (source_lift_bounds_and_flow
      u eta B initial t hi hB ht'.1 (hbound t ht'.1).1).2.2
    rw [← hGrep ht', hflow]
    exact hd ht
  have hOrep := GSTStage30.omega_representation
    (liftedControl u eta B initial)
    (omega u eta 0 initial a c omegaInitial)
    eta B initial a c omegaInitial T hT (hv T hT)
    hsol.1 hOODE (omega_initial u eta 0 initial a c omegaInitial)
  exact ⟨(hGrep ⟨hT, le_rfl⟩).symm, (hOrep ⟨hT, le_rfl⟩).symm⟩

end GSTStage181

#print axioms GSTStage181.source_lift_resource_ac
#print axioms GSTStage181.source_lift_canonical_trajectories
