import GSTStage173
import Mathlib.Tactic.FunProp

open MeasureTheory Set Filter
open scoped Topology
open GSTStage173

namespace GSTStage174

theorem preserving_resource_hasDerivAt
    (B eta a h c initial t : ℝ) :
    HasDerivAt (preservingResource B eta a h c initial)
      (B - eta * a * h / c) t := by
  simpa only [preservingResource, id_eq, mul_one] using
    ((hasDerivAt_id t).const_mul (B - eta * a * h / c)).const_add initial

theorem preserving_state_hasDerivAt
    (a h initial t : ℝ) :
    HasDerivAt (preservingState a h initial)
      (-a * preservingState a h initial t + a * h) t := by
  have hd : HasDerivAt (preservingState a h initial)
      ((initial - h) * (Real.exp (-a * t) * (-a))) t := by
    simpa only [preservingState, id_eq, mul_one] using
      ((((hasDerivAt_id t).const_mul (-a)).exp).const_mul
        (initial - h)).const_add h
  convert hd using 1
  dsimp [preservingState]
  ring

theorem preserving_control_measurable
    (B eta a h c initial : ℝ) :
    Measurable (preservingControl B eta a h c initial) := by
  unfold preservingControl preservingResource
  fun_prop

theorem preserving_control_continuousOn
    (B eta a h c initial : ℝ)
    (hc : 0 < c) (hi : 0 < initial)
    (hsource : eta * a * h / c ≤ B) :
    ContinuousOn (preservingControl B eta a h c initial)
      (Ici (0 : ℝ)) := by
  have hF : Continuous (preservingResource B eta a h c initial) := by
    unfold preservingResource
    fun_prop
  change ContinuousOn
    (fun t => a * h / (c * preservingResource B eta a h c initial t))
    (Ici (0 : ℝ))
  apply continuousOn_const.div (continuous_const.mul hF).continuousOn
  intro t ht
  have hinc : 0 ≤ (B - eta * a * h / c) * t :=
    mul_nonneg (sub_nonneg.mpr hsource) ht
  have hpos : 0 < preservingResource B eta a h c initial t := by
    dsimp [preservingResource]
    linarith only [hi, hinc]
  exact ne_of_gt (mul_pos hc hpos)

theorem preserving_profiles_solve_odes
    (B eta a h c s U phiInitial omegaInitial t : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hh : 0 < h) (hs : 0 < s)
    (hphi : s ≤ phiInitial) (homega : h ≤ omegaInitial)
    (hsource : eta * a * h / c ≤ B)
    (heffort : a * h / (c * s) ≤ U)
    (ht : 0 ≤ t) :
    HasDerivAt (preservingResource B eta a h c phiInitial)
      (B - eta * preservingControl B eta a h c phiInitial t *
        preservingResource B eta a h c phiInitial t) t ∧
    HasDerivAt (preservingState a h omegaInitial)
      (-a * preservingState a h omegaInitial t +
        c * (preservingResource B eta a h c phiInitial t *
          preservingControl B eta a h c phiInitial t)) t := by
  have hflow := (preserving_profiles_bounds
    B eta a h c s U phiInitial omegaInitial t
    ha hc hh hs hphi homega hsource heffort ht).2.2.2
  have hcancel : c * (a * h / c) = a * h := by
    field_simp
  have hR :
      B - eta * preservingControl B eta a h c phiInitial t *
          preservingResource B eta a h c phiInitial t =
        B - eta * a * h / c := by
    calc
      B - eta * preservingControl B eta a h c phiInitial t *
          preservingResource B eta a h c phiInitial t =
          B - eta * (preservingResource B eta a h c phiInitial t *
            preservingControl B eta a h c phiInitial t) := by ring
      _ = B - eta * (a * h / c) := by rw [hflow]
      _ = B - eta * a * h / c := by ring
  have hO :
      -a * preservingState a h omegaInitial t +
        c * (preservingResource B eta a h c phiInitial t *
          preservingControl B eta a h c phiInitial t) =
      -a * preservingState a h omegaInitial t + a * h := by
    rw [hflow, hcancel]
  constructor
  · rw [hR]
    exact preserving_resource_hasDerivAt B eta a h c phiInitial t
  · rw [hO]
    exact preserving_state_hasDerivAt a h omegaInitial t

end GSTStage174

#print axioms GSTStage174.preserving_resource_hasDerivAt
#print axioms GSTStage174.preserving_state_hasDerivAt
#print axioms GSTStage174.preserving_control_measurable
#print axioms GSTStage174.preserving_control_continuousOn
#print axioms GSTStage174.preserving_profiles_solve_odes
