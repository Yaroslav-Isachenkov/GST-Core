import GSTStage174

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29 GSTStage173 GSTStage174

namespace GSTStage175

theorem preserving_resource_ac
    (B eta a h c initial T : ℝ) :
    AbsolutelyContinuousOnInterval
      (preservingResource B eta a h c initial) 0 T := by
  have hlin := cumulative_ac (fun _ : ℝ => (1 : ℝ))
    (B - eta * a * h / c) T intervalIntegrable_const
  have hlin' : AbsolutelyContinuousOnInterval
      (fun t : ℝ => (B - eta * a * h / c) * t) 0 T := by
    change AbsolutelyContinuousOnInterval
      (fun t : ℝ =>
        (B - eta * a * h / c) * ∫ s in (0 : ℝ)..t, (1 : ℝ)) 0 T at hlin
    simpa using hlin
  exact (GSTStage09.constant_ac 0 T initial).fun_add hlin'

theorem preserving_state_ac
    (a h initial T : ℝ) :
    AbsolutelyContinuousOnInterval (preservingState a h initial) 0 T := by
  have he := GSTStage30.linear_exponential_ac (-a) T
  exact (GSTStage09.constant_ac 0 T h).fun_add
    (he.const_mul (initial - h))

theorem preserving_canonical_trajectories_eq
    (B eta a h c s U phiInitial omegaInitial : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hh : 0 < h) (hs : 0 < s)
    (hphi : s ≤ phiInitial) (homega : h ≤ omegaInitial)
    (hsource : eta * a * h / c ≤ B)
    (heffort : a * h / (c * s) ≤ U) :
    ∀ t : ℝ, 0 ≤ t →
      resource (preservingControl B eta a h c phiInitial)
        eta B phiInitial t =
        preservingResource B eta a h c phiInitial t ∧
      omega (preservingControl B eta a h c phiInitial)
        eta B phiInitial a c omegaInitial t =
        preservingState a h omegaInitial t := by
  let v := preservingControl B eta a h c phiInitial
  let F := preservingResource B eta a h c phiInitial
  let O := preservingState a h omegaInitial
  have hvCont : ContinuousOn v (Ici (0 : ℝ)) :=
    preserving_control_continuousOn B eta a h c phiInitial
      hc (lt_of_lt_of_le hs hphi) hsource
  intro T hT
  have hvInt : IntervalIntegrable v volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    exact hvCont.mono Icc_subset_Ici_self
  have hFode : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt F (B - eta * v t * F t) t := by
    apply Filter.Eventually.of_forall
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact (preserving_profiles_solve_odes
      B eta a h c s U phiInitial omegaInitial t
      ha hc hh hs hphi homega hsource heffort ht.1).1
  have hFinit : F 0 = phiInitial :=
    (preserving_profiles_initial B eta a h c phiInitial omegaInitial).1
  have hFrep : EqOn F (resource v eta B phiInitial)
      (Icc (0 : ℝ) T) :=
    GSTStage13.resource_representation
      v F eta B phiInitial T hT hvInt
      (preserving_resource_ac B eta a h c phiInitial T)
      hFode hFinit
  have hOode : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt O
        (-a * O t + c * (resource v eta B phiInitial t * v t)) t := by
    apply Filter.Eventually.of_forall
    intro t ht
    rw [uIcc_of_le hT] at ht
    rw [← hFrep ht]
    exact (preserving_profiles_solve_odes
      B eta a h c s U phiInitial omegaInitial t
      ha hc hh hs hphi homega hsource heffort ht.1).2
  have hOinit : O 0 = omegaInitial :=
    (preserving_profiles_initial B eta a h c phiInitial omegaInitial).2
  have hOrep : EqOn O (omega v eta B phiInitial a c omegaInitial)
      (Icc (0 : ℝ) T) :=
    GSTStage30.omega_representation
      v O eta B phiInitial a c omegaInitial T hT hvInt
      (preserving_state_ac a h omegaInitial T) hOode hOinit
  exact ⟨(hFrep ⟨hT, le_rfl⟩).symm, (hOrep ⟨hT, le_rfl⟩).symm⟩

end GSTStage175

#print axioms GSTStage175.preserving_resource_ac
#print axioms GSTStage175.preserving_state_ac
#print axioms GSTStage175.preserving_canonical_trajectories_eq
