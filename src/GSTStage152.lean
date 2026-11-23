import GSTStage151

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage147 GSTStage150 GSTStage151

namespace GSTStage152

theorem candidate_z_hasDerivAt
    (x : StateData) (r : ℝ)
    (hclip : GSTStage44.Clipping x r)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (z x) (x.rho * z x t - x.u t * d x t) t := by
  apply GSTStage47.hasDerivAt_of_local_ac_ae
    (z x) (fun s => x.rho * z x s - x.u s * d x s)
    ?_ ?_ ?_ t ht
  · intro T hT
    exact (GSTStage43.z_solution_rewritten x T hT).1
  · intro T hT
    exact (GSTStage43.z_solution_rewritten x T hT).2
  · intro T hT
    have hz := (GSTStage43.z_solution_rewritten x T hT).1.continuousOn
    have hd := ((state_costates_verified x).1 T hT).continuousOn
    have hu := GSTStage44.candidate_control_continuousOn x r T hT hclip
    exact (continuousOn_const.mul hz).sub (hu.mul hd)

theorem candidate_saturated_systemOn
    (x : StateData) (a T : ℝ)
    (ha : x.a = 1 / 10) (hc : x.c = 1)
    (heta : x.eta = 1 / 20) (hrho : x.rho = 1 / 20)
    (hq : x.q = 1) (htarget : x.target = 1)
    (hclip : GSTStage44.Clipping x (1 / 10))
    (haPos : 0 < a)
    (hsat : ∀ t ∈ Ioo a T, x.u t = 1) :
    SaturatedSystemOn
      (resource x.u x.eta x.B x.phiInitial)
      (state x) (p x) (z x) x.B a T := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t ht
    exact (GSTStage60.resource_ode_at x (1 / 10) hclip t
      (lt_of_lt_of_le haPos ht.1)).continuousAt.continuousWithinAt
  · intro t ht
    exact (GSTStage47.state_ode_at x (1 / 10) hclip t
      (lt_of_lt_of_le haPos ht.1)).continuousAt.continuousWithinAt
  · intro t ht
    exact (GSTStage47.p_ode_at x t
      (lt_of_lt_of_le haPos ht.1)).continuousAt.continuousWithinAt
  · intro t ht
    exact (candidate_z_hasDerivAt x (1 / 10) hclip t
      (lt_of_lt_of_le haPos ht.1)).continuousAt.continuousWithinAt
  · intro t ht
    have htPos : 0 < t := lt_trans haPos ht.1
    have hu := hsat t ht
    have hR := GSTStage60.resource_ode_at x (1 / 10) hclip t htPos
    have hO := GSTStage47.state_ode_at x (1 / 10) hclip t htPos
    have hP := GSTStage47.p_ode_at x t htPos
    have hZ := candidate_z_hasDerivAt x (1 / 10) hclip t htPos
    have hd : d x t = p x t - z x t / 20 := by
      change x.c * p x t - x.eta * z x t = p x t - z x t / 20
      rw [hc, heta]
      ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · convert hR using 1
      all_goals rw [hu, heta]
      all_goals ring
    · convert hO using 1
      all_goals rw [hu, ha, hc]
      all_goals ring
    · convert hP using 1
      all_goals rw [hrho, ha, hq, htarget]
      all_goals ring
    · convert hZ using 1
      all_goals rw [hrho, hu, hd]
      all_goals ring

theorem candidate_saturated_eq_profiles
    (x : StateData) (a T : ℝ)
    (ha : x.a = 1 / 10) (hc : x.c = 1)
    (heta : x.eta = 1 / 20) (hrho : x.rho = 1 / 20)
    (hq : x.q = 1) (htarget : x.target = 1)
    (hclip : GSTStage44.Clipping x (1 / 10))
    (haPos : 0 < a)
    (hsat : ∀ t ∈ Ioo a T, x.u t = 1)
    (hF : resource x.u x.eta x.B x.phiInitial a =
      1 / 10 - 3 * p x a / 400) :
    let F := resource x.u x.eta x.B x.phiInitial a
    EqOn (resource x.u x.eta x.B x.phiInitial)
      (fun t => satResource F x.B (satClock a t)) (Icc a T) ∧
    EqOn (state x)
      (fun t => satState (p x a) (S x a) F x.B (satClock a t)) (Icc a T) ∧
    EqOn (p x)
      (fun t => satP (p x a) (S x a) F x.B (satClock a t)) (Icc a T) ∧
    EqOn (z x)
      (fun t => satZ (p x a) (S x a) F (z x a) x.B (satClock a t))
      (Icc a T) := by
  have hsystem := candidate_saturated_systemOn
    x a T ha hc heta hrho hq htarget hclip haPos hsat
  have hO : state x a = 1 + S x a / 2 - p x a / 20 := by
    have he : S x a =
        x.a * p x a + 2 * x.q * (state x a - x.target) := rfl
    rw [ha, hq, htarget] at he
    linarith
  exact saturated_solution_eq_profiles
    (resource x.u x.eta x.B x.phiInitial) (state x) (p x) (z x)
    (p x a) (S x a) (resource x.u x.eta x.B x.phiInitial a)
    (z x a) x.B a T hsystem hF ⟨rfl, hO, rfl, rfl⟩

end GSTStage152

#print axioms GSTStage152.candidate_z_hasDerivAt
#print axioms GSTStage152.candidate_saturated_systemOn
#print axioms GSTStage152.candidate_saturated_eq_profiles
