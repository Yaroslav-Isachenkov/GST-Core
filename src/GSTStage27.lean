import GSTStage12
import GSTStage24
import GSTStage25
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
open scoped Topology
open GSTStage22 GSTStage23 GSTStage24 GSTStage25

namespace GSTStage27

noncomputable def zPhase
    (u : ℝ → ℝ) (eta rho t : ℝ) : ℝ :=
  rho * t + GSTStage11.cumulative u eta t

noncomputable def zInput
    (u p : ℝ → ℝ) (eta rho s : ℝ) : ℝ :=
  Real.exp (-zPhase u eta rho s) * (u s * p s)

theorem bounded_control_integrable
    (u : ℝ → ℝ) (U T : ℝ) (hT : 0 ≤ T)
    (huMeas : Measurable u)
    (hu : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U) :
    IntervalIntegrable u volume 0 T := by
  have henv : IntegrableOn (fun _ : ℝ => U) (Ioc (0 : ℝ) T) :=
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => U) volume 0 T).1
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T),
      ‖u t‖ ≤ U := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hu t (le_of_lt ht.1)).1]
      exact (hu t (le_of_lt ht.1)).2)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
  exact henv.mono' huMeas.stronglyMeasurable.aestronglyMeasurable hbound

theorem z_phase_ac
    (u : ℝ → ℝ) (eta rho T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    AbsolutelyContinuousOnInterval (zPhase u eta rho) 0 T := by
  have hi : IntervalIntegrable (fun _ : ℝ => rho) volume 0 T :=
    intervalIntegrable_const
  have hlinear :
      AbsolutelyContinuousOnInterval (fun t : ℝ => rho * t) 0 T := by
    have h := hi.absolutelyContinuousOnInterval_intervalIntegral
      (show (0 : ℝ) ∈ uIcc (0 : ℝ) T by simp)
    simpa only [
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm
    ] using h
  exact hlinear.fun_add (GSTStage11.cumulative_ac u eta T hu)

theorem z_phase_derivative_ae
    (u : ℝ → ℝ) (eta rho T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (zPhase u eta rho) (rho + eta * u t) t := by
  have hzero : (0 : ℝ) ∈ uIcc (0 : ℝ) T := by simp
  filter_upwards [hu.ae_hasDerivAt_integral] with t hd
  intro ht
  have hl : HasDerivAt (fun x : ℝ => rho * x) rho t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul rho
  exact hl.add ((hd ht 0 hzero).const_mul eta)

theorem z_kernel_factor
    (u : ℝ → ℝ) (eta rho t s : ℝ)
    (hut : IntervalIntegrable u volume 0 t)
    (hus : IntervalIntegrable u volume 0 s) :
    zKernel u eta rho t s =
      Real.exp (zPhase u eta rho t) *
        Real.exp (-zPhase u eta rho s) := by
  have hsplit := intervalIntegral.integral_interval_sub_left hus hut
  have hexponent :
      -rho * (s - t) - eta * (∫ r in t..s, u r) =
        zPhase u eta rho t + (-zPhase u eta rho s) := by
    unfold zPhase GSTStage11.cumulative
    rw [← hsplit]
    ring
  unfold zKernel
  rw [hexponent, Real.exp_add]

theorem z_weighted_tail
    (u p : ℝ → ℝ) (eta rho c t : ℝ) (ht : 0 ≤ t)
    (hu : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable u volume 0 T) :
    zCostate u p eta rho c t =
      c * (Real.exp (zPhase u eta rho t) *
        tail (zInput u p eta rho) t) := by
  have heq :
      (∫ s in Ioi t, zKernel u eta rho t s * (u s * p s)) =
      ∫ s in Ioi t, Real.exp (zPhase u eta rho t) *
        zInput u p eta rho s := by
    apply integral_congr_ae
    change ∀ᵐ s ∂volume.restrict (Ioi t),
      zKernel u eta rho t s * (u s * p s) =
        Real.exp (zPhase u eta rho t) * zInput u p eta rho s
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun s hs => by
      rw [z_kernel_factor u eta rho t s
        (hu t ht) (hu s (le_trans ht (le_of_lt hs)))]
      unfold zInput
      ring)
  unfold zCostate tail
  rw [heq, integral_const_mul]

theorem z_input_integrable
    (u p : ℝ → ℝ) (eta rho c U P : ℝ)
    (heta : 0 ≤ eta) (hrho : 0 < rho)
    (hU : 0 ≤ U) (hP : 0 ≤ P)
    (huMeas : Measurable u) (hpMeas : Measurable p)
    (hu : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U)
    (hp : ∀ t : ℝ, 0 ≤ t → |p t| ≤ P * (1 + t)) :
    IntegrableOn (zInput u p eta rho) (Ioi (0 : ℝ)) := by
  have hi := (z_integrable_and_bound u p eta rho c U P 0
    heta hrho hU hP (le_refl 0) hu hp
    (z_integrand_aestronglyMeasurable u p eta rho 0 huMeas hpMeas)).1
  apply hi.congr_fun ?_ measurableSet_Ioi
  intro s _hs
  unfold zKernel zInput zPhase GSTStage11.cumulative
  change
    Real.exp (-rho * (s - 0) - eta * (∫ r in (0 : ℝ)..s, u r)) *
      (u s * p s) =
    Real.exp (-(rho * s + eta * (∫ r in (0 : ℝ)..s, u r))) *
      (u s * p s)
  rw [show -rho * (s - 0) - eta * (∫ r in (0 : ℝ)..s, u r) =
    -(rho * s + eta * (∫ r in (0 : ℝ)..s, u r)) by ring]

theorem z_ac_of_input_integrable
    (u p : ℝ → ℝ) (eta rho c T : ℝ) (hT : 0 ≤ T)
    (hu : ∀ R : ℝ, 0 ≤ R → IntervalIntegrable u volume 0 R)
    (hg : IntegrableOn (zInput u p eta rho) (Ioi (0 : ℝ))) :
    AbsolutelyContinuousOnInterval (zCostate u p eta rho c) 0 T := by
  have hexp :
      AbsolutelyContinuousOnInterval
        (fun t => Real.exp (zPhase u eta rho t)) 0 T := by
    apply GSTStage12.exp_ac
    exact z_phase_ac u eta rho T (hu T hT)
  have htail := tail_ac (zInput u p eta rho) T hg hT
  have hmodel := (hexp.fun_mul htail).const_mul c
  apply ac_congr_on
    (fun t => c * (Real.exp (zPhase u eta rho t) *
      tail (zInput u p eta rho) t))
    (zCostate u p eta rho c) 0 T hmodel
  intro t ht
  have hmem : t ∈ Icc (0 : ℝ) T := by
    simpa only [uIcc_of_le hT] using ht
  exact (z_weighted_tail u p eta rho c t hmem.1 hu).symm

theorem z_ode_ae_of_input_integrable
    (u p : ℝ → ℝ) (eta rho c T : ℝ) (hT : 0 ≤ T)
    (hu : ∀ R : ℝ, 0 ≤ R → IntervalIntegrable u volume 0 R)
    (hg : IntegrableOn (zInput u p eta rho) (Ioi (0 : ℝ))) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (zCostate u p eta rho c)
        ((rho + eta * u t) * zCostate u p eta rho c t -
          c * u t * p t) t := by
  have hne : ∀ᵐ t : ℝ, t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [
    z_phase_derivative_ae u eta rho T (hu T hT),
    tail_derivative_ae (zInput u p eta rho) T hg hT,
    hne
  ] with t hphase htail htne
  intro ht
  have hmem : t ∈ Icc (0 : ℝ) T := by
    simpa only [uIcc_of_le hT] using ht
  have htpos : 0 < t :=
    lt_of_le_of_ne hmem.1 (Ne.symm htne)
  have he := (hphase ht).exp
  have hproduct := (he.mul (htail ht)).const_mul c
  have hcancel :
      Real.exp (zPhase u eta rho t) * zInput u p eta rho t =
        u t * p t := by
    unfold zInput
    rw [← mul_assoc, ← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero, one_mul]
  have hvalue := z_weighted_tail u p eta rho c t hmem.1 hu
  have hmodel :
      HasDerivAt
        (fun x => c * (Real.exp (zPhase u eta rho x) *
          tail (zInput u p eta rho) x))
        ((rho + eta * u t) * zCostate u p eta rho c t -
          c * u t * p t) t := by
    convert hproduct using 1
    dsimp only [Pi.mul_apply]
    rw [hvalue, mul_neg, hcancel]
    ring
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds htpos] with x hx
  exact z_weighted_tail u p eta rho c x (le_of_lt hx) hu

theorem z_is_costate_solution
    (u p : ℝ → ℝ) (eta rho c U P T : ℝ)
    (heta : 0 ≤ eta) (hrho : 0 < rho)
    (hU : 0 ≤ U) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (huMeas : Measurable u) (hpMeas : Measurable p)
    (hu : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U)
    (hp : ∀ t : ℝ, 0 ≤ t → |p t| ≤ P * (1 + t)) :
    AbsolutelyContinuousOnInterval (zCostate u p eta rho c) 0 T ∧
    (∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (zCostate u p eta rho c)
        ((rho + eta * u t) * zCostate u p eta rho c t -
          c * u t * p t) t) := by
  have hui : ∀ R : ℝ, 0 ≤ R → IntervalIntegrable u volume 0 R :=
    fun R hR => bounded_control_integrable u U R hR huMeas hu
  have hg := z_input_integrable u p eta rho c U P
    heta hrho hU hP huMeas hpMeas hu hp
  exact ⟨
    z_ac_of_input_integrable u p eta rho c T hT hui hg,
    z_ode_ae_of_input_integrable u p eta rho c T hT hui hg
  ⟩

-- Application to the integral-defined p from the core.
-- Growth and measurability of p are derived from earlier stages.
theorem canonical_z_is_costate_solution
    (u omega : ℝ → ℝ) (eta rho a c q target U M T : ℝ)
    (heta : 0 ≤ eta) (hrho : 0 < rho) (hdecay : 0 < rho + a)
    (hU : 0 ≤ U) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (huMeas : Measurable u) (hOmegaMeas : Measurable omega)
    (hu : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U)
    (hcont : ContinuousOn omega (Ici (0 : ℝ)))
    (hOmega : ∀ t : ℝ, 0 ≤ t → |omega t| ≤ M * (1 + t)) :
    AbsolutelyContinuousOnInterval
      (zCostate u (pCostate omega rho a q target) eta rho c) 0 T ∧
    (∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt
        (zCostate u (pCostate omega rho a q target) eta rho c)
        ((rho + eta * u t) *
          zCostate u (pCostate omega rho a q target) eta rho c t -
          c * u t * pCostate omega rho a q target t) t) := by
  obtain ⟨P, hP, hp⟩ :=
    p_linear_growth omega rho a q target M hdecay hM hcont hOmega
  exact z_is_costate_solution
    u (pCostate omega rho a q target) eta rho c U P T
    heta hrho hU hP hT huMeas
    (p_measurable omega rho a q target hOmegaMeas) hu hp

#print axioms bounded_control_integrable
#print axioms z_phase_ac
#print axioms z_phase_derivative_ae
#print axioms z_kernel_factor
#print axioms z_weighted_tail
#print axioms z_input_integrable
#print axioms z_ac_of_input_integrable
#print axioms z_ode_ae_of_input_integrable
#print axioms z_is_costate_solution
#print axioms canonical_z_is_costate_solution

end GSTStage27
