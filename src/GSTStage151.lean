import GSTStage150

open Set GSTStage147 GSTStage150

namespace GSTStage151

noncomputable def satClock (a t : ℝ) : ℝ :=
  Real.exp ((t - a) / 20)

theorem satClock_hasDerivAt (a t : ℝ) :
    HasDerivAt (satClock a) (satClock a t / 20) t := by
  convert (((hasDerivAt_id t).sub_const a).div_const (20 : ℝ)).exp using 1
  all_goals dsimp [satClock]
  all_goals ring

theorem saturated_profiles_systemOn (P M F Z B a T : ℝ) :
    SaturatedSystemOn
      (fun t => satResource F B (satClock a t))
      (fun t => satState P M F B (satClock a t))
      (fun t => satP P M F B (satClock a t))
      (fun t => satZ P M F Z B (satClock a t))
      B a T := by
  have hd (t : ℝ) :=
    GSTStage148.saturated_profiles_solve_odes
      P M F Z B (satClock a) t (satClock_hasDerivAt a t)
      (Real.exp_pos ((t - a) / 20))
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t _ht
    exact (hd t).1.continuousAt.continuousWithinAt
  · intro t _ht
    exact (hd t).2.1.continuousAt.continuousWithinAt
  · intro t _ht
    exact (hd t).2.2.1.continuousAt.continuousWithinAt
  · intro t _ht
    exact (hd t).2.2.2.continuousAt.continuousWithinAt
  · intro t _ht
    exact hd t

theorem saturated_solution_eq_profiles
    (f o p z : ℝ → ℝ) (P M F Z B a T : ℝ)
    (hsystem : SaturatedSystemOn f o p z B a T)
    (hF : F = 1 / 10 - 3 * P / 400)
    (hinit : f a = F ∧ o a = 1 + M / 2 - P / 20 ∧
      p a = P ∧ z a = Z) :
    EqOn f (fun t => satResource F B (satClock a t)) (Icc a T) ∧
    EqOn o (fun t => satState P M F B (satClock a t)) (Icc a T) ∧
    EqOn p (fun t => satP P M F B (satClock a t)) (Icc a T) ∧
    EqOn z (fun t => satZ P M F Z B (satClock a t)) (Icc a T) := by
  have hclock : satClock a a = 1 := by simp [satClock]
  have hv := saturated_profiles_initial_values P M F Z B hF
  apply saturated_system_unique_on_interval
    f o p z
    (fun t => satResource F B (satClock a t))
    (fun t => satState P M F B (satClock a t))
    (fun t => satP P M F B (satClock a t))
    (fun t => satZ P M F Z B (satClock a t))
    B a T hsystem (saturated_profiles_systemOn P M F Z B a T)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hclock] using hinit.1.trans hv.1.symm
  · simpa only [hclock] using hinit.2.1.trans hv.2.1.symm
  · simpa only [hclock] using hinit.2.2.1.trans hv.2.2.1.symm
  · simpa only [hclock] using hinit.2.2.2.trans hv.2.2.2.symm

end GSTStage151

#print axioms GSTStage151.satClock_hasDerivAt
#print axioms GSTStage151.saturated_profiles_systemOn
#print axioms GSTStage151.saturated_solution_eq_profiles
