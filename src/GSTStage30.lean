import GSTStage29
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29

namespace GSTStage30

theorem linear_exponential_ac
    (a T : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t : ℝ => Real.exp (a * t)) 0 T := by
  have h := cumulative_ac (fun _ : ℝ => (1 : ℝ)) a T
    intervalIntegrable_const
  change AbsolutelyContinuousOnInterval
    (fun t : ℝ => a * ∫ s in (0 : ℝ)..t, (1 : ℝ)) 0 T at h
  have hlin : AbsolutelyContinuousOnInterval
      (fun t : ℝ => a * t) 0 T := by
    simpa using h
  exact GSTStage12.exp_ac (fun t : ℝ => a * t) 0 T hlin

theorem linear_ode_unique
    (f g forcing : ℝ → ℝ) (a T : ℝ)
    (hT : 0 ≤ T)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hg : AbsolutelyContinuousOnInterval g 0 T)
    (hfODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt f (-a * f t + forcing t) t)
    (hgODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt g (-a * g t + forcing t) t)
    (hinitial : f 0 = g 0) :
    EqOn f g (Icc (0 : ℝ) T) := by
  let W : ℝ → ℝ := fun t => Real.exp (a * t) * (f t - g t)
  have hW : AbsolutelyContinuousOnInterval W 0 T :=
    (linear_exponential_ac a T).mul (hf.fun_sub hg)
  have hWODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt W 0 t := by
    filter_upwards [hfODE, hgODE] with t hft hgt
    intro ht
    have he := ((hasDerivAt_id t).const_mul a).exp
    have hd := he.mul ((hft ht).sub (hgt ht))
    convert hd using 1
    dsimp only [W, Pi.mul_apply, Pi.sub_apply, id_eq]
    ring
  obtain ⟨C, hC⟩ := hW.const_of_ae_hasDerivAt_zero hWODE
  have hzero : W 0 = 0 := by
    simp [W, hinitial]
  intro t ht
  have ht' : t ∈ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hT]
    exact ht
  have heq : W t = W 0 :=
    (hC t ht').trans (hC 0 left_mem_uIcc).symm
  have hz : Real.exp (a * t) * (f t - g t) = 0 :=
    heq.trans hzero
  have hdiff : f t - g t = 0 :=
    (mul_eq_zero.mp hz).resolve_left (ne_of_gt (Real.exp_pos _))
  exact sub_eq_zero.mp hdiff

theorem omega_representation
    (u g : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial T : ℝ)
    (hT : 0 ≤ T)
    (hu : IntervalIntegrable u volume 0 T)
    (hg : AbsolutelyContinuousOnInterval g 0 T)
    (hgODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt g
        (-a * g t + c * (resource u eta B phiInitial t * u t)) t)
    (hg0 : g 0 = omegaInitial) :
    EqOn g (omega u eta B phiInitial a c omegaInitial)
      (Icc (0 : ℝ) T) := by
  have hs := omega_solution u eta B phiInitial a c omegaInitial T hu
  apply linear_ode_unique
    g (omega u eta B phiInitial a c omegaInitial)
    (resourceForcing u eta B phiInitial c)
    a T hT hg hs.1 hgODE hs.2
  rw [omega_initial]
  exact hg0

theorem resource_nonneg
    (u : ℝ → ℝ) (eta B phiInitial t : ℝ)
    (hB : 0 ≤ B) (hi : 0 ≤ phiInitial) (ht : 0 ≤ t) :
    0 ≤ resource u eta B phiInitial t := by
  exact le_trans
    (mul_nonneg hi (le_of_lt (Real.exp_pos _)))
    (resource_lower_bound u eta B phiInitial t hB ht)

theorem omega_nonneg
    (u : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial t : ℝ)
    (hB : 0 ≤ B) (hi : 0 ≤ phiInitial)
    (hc : 0 ≤ c) (ho : 0 ≤ omegaInitial) (ht : 0 ≤ t)
    (hu0 : ∀ s : ℝ, 0 ≤ s → 0 ≤ u s) :
    0 ≤ omega u eta B phiInitial a c omegaInitial t := by
  have hint : 0 ≤ ∫ s in (0 : ℝ)..t,
      weightedInput (resourceForcing u eta B phiInitial c) a s := by
    apply intervalIntegral.integral_nonneg ht
    intro s hs
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (mul_nonneg hc
        (mul_nonneg
          (resource_nonneg u eta B phiInitial s hB hi hs.1)
          (hu0 s hs.1)))
  exact mul_nonneg (le_of_lt (Real.exp_pos _)) (add_nonneg ho hint)

theorem ac_endpoint_upper
    (f : ℝ → ℝ) (L T : ℝ)
    (hT : 0 ≤ T)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      deriv f t ≤ L) :
    f T ≤ f 0 + L * T := by
  have hle : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      deriv f t ≤ L := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hderiv] with t ht hmem
    apply ht
    rw [uIcc_of_le hT]
    exact hmem
  have hcomp := intervalIntegral.integral_mono_ae_restrict
    hT hf.intervalIntegrable_deriv
    (intervalIntegrable_const (c := L)) hle
  rw [hf.integral_deriv_eq_sub] at hcomp
  have hfinal : f T - f 0 ≤ T * L := by
    simpa using hcomp
  nlinarith

-- The control terms cancel exactly in eta*Omega + c*phi.
theorem state_resource_balance_upper
    (phi om u : ℝ → ℝ) (eta a c B T : ℝ)
    (hT : 0 ≤ T) (heta : 0 ≤ eta) (ha : 0 ≤ a)
    (hphi : AbsolutelyContinuousOnInterval phi 0 T)
    (hom : AbsolutelyContinuousOnInterval om 0 T)
    (hphiODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt phi (B - eta * u t * phi t) t)
    (homODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt om (-a * om t + c * (phi t * u t)) t)
    (hom0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ om t) :
    eta * om T + c * phi T ≤
      eta * om 0 + c * phi 0 + c * B * T := by
  let H : ℝ → ℝ := fun t => eta * om t + c * phi t
  have hH : AbsolutelyContinuousOnInterval H 0 T :=
    (hom.const_mul eta).fun_add (hphi.const_mul c)
  have hHD : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      deriv H t ≤ c * B := by
    filter_upwards [homODE, hphiODE] with t hot hpt
    intro ht
    have hd := ((hot ht).const_mul eta).add ((hpt ht).const_mul c)
    have hd' : HasDerivAt H (-eta * a * om t + c * B) t := by
      convert hd using 1
      ring
    have ht' : t ∈ Icc (0 : ℝ) T := by
      rw [uIcc_of_le hT] at ht
      exact ht
    rw [hd'.deriv]
    have hn := mul_nonneg (mul_nonneg heta ha) (hom0 t ht')
    nlinarith
  exact ac_endpoint_upper H (c * B) T hT hH hHD

theorem omega_upper
    (u : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial T : ℝ)
    (hT : 0 ≤ T) (heta : 0 < eta)
    (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hi : 0 ≤ phiInitial) (hc : 0 ≤ c) (ho : 0 ≤ omegaInitial)
    (hu : IntervalIntegrable u volume 0 T)
    (hu0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t) :
    omega u eta B phiInitial a c omegaInitial T ≤
      (eta * omegaInitial + c * phiInitial + c * B * T) / eta := by
  have hs := omega_solution u eta B phiInitial a c omegaInitial T hu
  have hb := state_resource_balance_upper
    (resource u eta B phiInitial)
    (omega u eta B phiInitial a c omegaInitial)
    u eta a c B T hT (le_of_lt heta) ha
    (GSTStage12.resource_ac u eta B phiInitial T hu)
    hs.1
    (GSTStage12.resource_ode_ae u eta B phiInitial T hu)
    hs.2
    (fun t ht => omega_nonneg
      u eta B phiInitial a c omegaInitial t hB hi hc ho ht.1 hu0)
  simp only [omega_initial, resource_initial] at hb
  have hn := mul_nonneg hc
    (resource_nonneg u eta B phiInitial T hB hi hT)
  apply (le_div_iff₀ heta).2
  nlinarith

theorem omega_linear_growth
    (u : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial : ℝ)
    (heta : 0 < eta) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hi : 0 ≤ phiInitial) (hc : 0 ≤ c) (ho : 0 ≤ omegaInitial)
    (hu : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable u volume 0 T)
    (hu0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t : ℝ, 0 ≤ t →
        |omega u eta B phiInitial a c omegaInitial t| ≤ M * (1 + t) := by
  have hA : 0 ≤ eta * omegaInitial + c * phiInitial :=
    add_nonneg (mul_nonneg (le_of_lt heta) ho) (mul_nonneg hc hi)
  have hD : 0 ≤ c * B := mul_nonneg hc hB
  refine ⟨(eta * omegaInitial + c * phiInitial + c * B) / eta,
    div_nonneg (add_nonneg hA hD) (le_of_lt heta), ?_⟩
  intro t ht
  rw [abs_of_nonneg
    (omega_nonneg u eta B phiInitial a c omegaInitial t
      hB hi hc ho ht hu0)]
  calc
    omega u eta B phiInitial a c omegaInitial t
        ≤ (eta * omegaInitial + c * phiInitial + c * B * t) / eta :=
      omega_upper u eta B phiInitial a c omegaInitial t
        ht heta ha hB hi hc ho (hu t ht) hu0
    _ ≤ ((eta * omegaInitial + c * phiInitial + c * B) * (1 + t)) / eta := by
      apply div_le_div_of_nonneg_right _ (le_of_lt heta)
      nlinarith [mul_nonneg hA ht]
    _ = ((eta * omegaInitial + c * phiInitial + c * B) / eta) * (1 + t) := by
      ring

-- Pointwise bounds match the representative used in stage28.
theorem admissible_omega_linear_growth
    (u : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial U : ℝ)
    (heta : 0 < eta) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hi : 0 ≤ phiInitial) (hc : 0 ≤ c) (ho : 0 ≤ omegaInitial)
    (hmeas : Measurable u)
    (hbound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t : ℝ, 0 ≤ t →
        |omega u eta B phiInitial a c omegaInitial t| ≤ M * (1 + t) := by
  have hu : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable u volume 0 T := by
    intro T hT
    apply GSTStage14.admissible_control_integrable u U T hT hmeas
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun t ht => hbound t ht.1)
  exact omega_linear_growth u eta B phiInitial a c omegaInitial
    heta ha hB hi hc ho hu (fun t ht => (hbound t ht).1)

#print axioms linear_exponential_ac
#print axioms linear_ode_unique
#print axioms omega_representation
#print axioms resource_nonneg
#print axioms omega_nonneg
#print axioms ac_endpoint_upper
#print axioms state_resource_balance_upper
#print axioms omega_upper
#print axioms omega_linear_growth
#print axioms admissible_omega_linear_growth

end GSTStage30
