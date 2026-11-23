import GSTStage172

namespace GSTStage173

noncomputable def preservingResource
    (B eta a h c initial t : ℝ) : ℝ :=
  initial + (B - eta * a * h / c) * t

noncomputable def preservingState
    (a h initial t : ℝ) : ℝ :=
  h + (initial - h) * Real.exp (-a * t)

noncomputable def preservingControl
    (B eta a h c initial t : ℝ) : ℝ :=
  a * h / (c * preservingResource B eta a h c initial t)

theorem preserving_profiles_initial
    (B eta a h c phiInitial omegaInitial : ℝ) :
    preservingResource B eta a h c phiInitial 0 = phiInitial ∧
      preservingState a h omegaInitial 0 = omegaInitial := by
  simp [preservingResource, preservingState]

theorem preserving_profiles_bounds
    (B eta a h c s U phiInitial omegaInitial t : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hh : 0 < h) (hs : 0 < s)
    (hphi : s ≤ phiInitial) (homega : h ≤ omegaInitial)
    (hsource : eta * a * h / c ≤ B)
    (heffort : a * h / (c * s) ≤ U)
    (ht : 0 ≤ t) :
    s ≤ preservingResource B eta a h c phiInitial t ∧
    h ≤ preservingState a h omegaInitial t ∧
    (0 ≤ preservingControl B eta a h c phiInitial t ∧
      preservingControl B eta a h c phiInitial t ≤ U) ∧
    preservingResource B eta a h c phiInitial t *
      preservingControl B eta a h c phiInitial t = a * h / c := by
  let F := preservingResource B eta a h c phiInitial t
  let v := preservingControl B eta a h c phiInitial t
  have hF : s ≤ F := by
    have hn := mul_nonneg (sub_nonneg.mpr hsource) ht
    dsimp [F, preservingResource]
    linarith only [hphi, hn]
  have hFpos : 0 < F := lt_of_lt_of_le hs hF
  have hden : 0 < c * F := mul_pos hc hFpos
  have hcs : 0 < c * s := mul_pos hc hs
  have hnum : 0 < a * h := mul_pos ha hh
  have hvEq : v = a * h / (c * F) := rfl
  have hv0 : 0 ≤ v := by
    rw [hvEq]
    exact (div_pos hnum hden).le
  have hU0 : 0 ≤ U :=
    (div_pos hnum hcs).le.trans heffort
  have hbase : a * h ≤ U * (c * s) :=
    (div_le_iff₀ hcs).mp heffort
  have hdenLe : c * s ≤ c * F :=
    mul_le_mul_of_nonneg_left hF hc.le
  have hupper : U * (c * s) ≤ U * (c * F) :=
    mul_le_mul_of_nonneg_left hdenLe hU0
  have hvU : v ≤ U := by
    rw [hvEq]
    exact (div_le_iff₀ hden).2 (hbase.trans hupper)
  have hbalance : v * (c * F) = a * h :=
    (eq_div_iff (ne_of_gt hden)).mp hvEq
  have hflow : F * v = a * h / c := by
    apply (eq_div_iff (ne_of_gt hc)).2
    nlinarith only [hbalance]
  have hO : h ≤ preservingState a h omegaInitial t := by
    have hn := mul_nonneg (sub_nonneg.mpr homega)
      (Real.exp_pos (-a * t)).le
    dsimp [preservingState]
    linarith only [hn]
  exact ⟨hF, hO, ⟨hv0, hvU⟩, hflow⟩

end GSTStage173

#print axioms GSTStage173.preserving_profiles_initial
#print axioms GSTStage173.preserving_profiles_bounds
