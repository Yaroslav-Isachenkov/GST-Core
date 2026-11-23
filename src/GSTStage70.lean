import GSTStage69

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11

namespace GSTStage70

theorem ac_difference_bound
    (f D : ℝ → ℝ) (L T : ℝ) (hT : 0 ≤ T)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hode : ∀ᵐ v : ℝ, v ∈ uIcc (0 : ℝ) T →
      HasDerivAt f (D v) v)
    (hbound : ∀ v ∈ Icc (0 : ℝ) T, |D v| ≤ L) :
    ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      |f t - f s| ≤ L * |t - s| := by
  intro s hs t ht
  have hsub : uIcc s t ⊆ uIcc (0 : ℝ) T := by
    intro v hv
    change min s t ≤ v ∧ v ≤ max s t at hv
    rw [uIcc_of_le hT]
    exact ⟨le_trans (le_min hs.1 ht.1) hv.1,
      le_trans hv.2 (max_le hs.2 ht.2)⟩
  have hlocal : AbsolutelyContinuousOnInterval f s t :=
    hf.mono hsub
  have hlocalODE : ∀ᵐ v : ℝ, v ∈ uIcc s t →
      HasDerivAt f (D v) v := by
    filter_upwards [hode] with v hv hmem
    exact hv (hsub hmem)
  have hid := GSTStage08.ac_integral_identity
    f D s t hlocal hlocalODE
  have hnorm : ‖∫ v in s..t, D v‖ ≤ L * |t - s| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro v hv
    have hmem := hsub (uIoc_subset_uIcc hv)
    rw [uIcc_of_le hT] at hmem
    simpa only [Real.norm_eq_abs] using hbound v hmem
  rw [hid, Real.norm_eq_abs] at hnorm
  exact hnorm

theorem uniform_trajectory_lipschitz_estimates
    (x : StateData) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Lphi Lomega : ℝ, 0 ≤ Lphi ∧ 0 ≤ Lomega ∧
      ∀ u : ℝ → ℝ, Measurable u →
        (∀ v : ℝ, 0 ≤ v → 0 ≤ u v ∧ u v ≤ x.U) →
        ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
          |resource u x.eta x.B x.phiInitial t -
            resource u x.eta x.B x.phiInitial s|
              ≤ Lphi * |t - s| ∧
          |competitorState x u t - competitorState x u s|
              ≤ Lomega * |t - s| := by
  obtain ⟨Lphi, Lomega, hLphi, hLomega, hb⟩ :=
    GSTStage69.uniform_rate_bounds x T hT
  refine ⟨Lphi, Lomega, hLphi, hLomega, ?_⟩
  intro u huMeas huBound
  have hui := GSTStage27.bounded_control_integrable
    u x.U T hT huMeas huBound
  have hphiAC := GSTStage12.resource_ac
    u x.eta x.B x.phiInitial T hui
  have hphiODE := GSTStage12.resource_ode_ae
    u x.eta x.B x.phiInitial T hui
  have homega := GSTStage29.omega_solution
    u x.eta x.B x.phiInitial x.a x.c x.omegaInitial T hui
  have hphiDiff := ac_difference_bound
    (resource u x.eta x.B x.phiInitial)
    (fun v => x.B - x.eta * u v *
      resource u x.eta x.B x.phiInitial v)
    Lphi T hT hphiAC hphiODE
    (fun v hv => (hb u huMeas huBound v hv).1)
  have homegaAC :
      AbsolutelyContinuousOnInterval (competitorState x u) 0 T :=
    homega.1
  have homegaODE : ∀ᵐ v : ℝ, v ∈ uIcc (0 : ℝ) T →
      HasDerivAt (competitorState x u)
        (-x.a * competitorState x u v +
          x.c * (resource u x.eta x.B x.phiInitial v * u v)) v :=
    homega.2
  have homegaDiff := ac_difference_bound
    (competitorState x u)
    (fun v => -x.a * competitorState x u v +
      x.c * (resource u x.eta x.B x.phiInitial v * u v))
    Lomega T hT homegaAC homegaODE
    (fun v hv => (hb u huMeas huBound v hv).2)
  intro s hs t ht
  exact ⟨hphiDiff s hs t ht, homegaDiff s hs t ht⟩

#print axioms GSTStage70.ac_difference_bound
#print axioms GSTStage70.uniform_trajectory_lipschitz_estimates

end GSTStage70
