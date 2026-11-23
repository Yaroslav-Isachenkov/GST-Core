import GSTStage08
import GSTStage15
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage12 GSTStage15

namespace GSTStage16

noncomputable def remainder
    (phi psi d S : ℝ → ℝ) (rho c B t : ℝ) : ℝ :=
  Real.exp (-rho * t) *
    (c * psi t * S t *
       (phi t / psi t - 1 - Real.log (phi t / psi t))
     - B * d t *
       (Real.log (phi t / psi t) + (phi t / psi t)⁻¹ - 1))

noncomputable def mixed
    (phi psi d u v : ℝ → ℝ) (rho t : ℝ) : ℝ :=
  Real.exp (-rho * t) * d t * (phi t - psi t) * (u t - v t)

theorem remainder_nonpos_at
    (phi psi d S : ℝ → ℝ) (rho c B t : ℝ)
    (hp : 0 < phi t) (hq : 0 < psi t)
    (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hd : 0 ≤ d t) (hS : S t ≤ 0) :
    remainder phi psi d S rho c B t ≤ 0 := by
  have hx : 0 < phi t / psi t := div_pos hp hq
  have hF := GSTStage01.F_nonneg (phi t / psi t) hx
  have hG := GSTStage01.G_nonneg (phi t / psi t) hx
  have hfirst :
      c * psi t * S t *
        (phi t / psi t - 1 - Real.log (phi t / psi t)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hc (le_of_lt hq)) hS) hF
  have hsecond :
      0 ≤ B * d t *
        (Real.log (phi t / psi t) + (phi t / psi t)⁻¹ - 1) :=
    mul_nonneg (mul_nonneg hB hd) hG
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _))
    (sub_nonpos.mpr (le_trans hfirst hsecond))

theorem entropy_weight_nonneg_at
    (phi psi d : ℝ → ℝ) (rho t : ℝ)
    (hp : 0 < phi t) (hq : 0 < psi t)
    (hd : 0 ≤ d t) :
    0 ≤ entropyWeight phi psi d rho t := by
  have hF := GSTStage01.F_nonneg (phi t / psi t) (div_pos hp hq)
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt hq)) hd) hF

theorem resource_mixed_integral_nonpos
    (u v d S : ℝ → ℝ) (eta B initial rho c T : ℝ)
    (hT : 0 ≤ T) (heta : 0 < eta)
    (hB : 0 ≤ B) (hi : 0 < initial) (hc : 0 ≤ c)
    (hu : IntervalIntegrable u volume 0 T)
    (hv : IntervalIntegrable v volume 0 T)
    (hdAC : AbsolutelyContinuousOnInterval d 0 T)
    (hdODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt d ((rho + eta * v t) * d t + c * S t) t)
    (hdpos : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ d t)
    (hS : ∀ t ∈ Icc (0 : ℝ) T, S t ≤ 0)
    (hRint : IntervalIntegrable
      (remainder (resource u eta B initial)
        (resource v eta B initial) d S rho c B) volume 0 T)
    (hmint : IntervalIntegrable
      (mixed (resource u eta B initial)
        (resource v eta B initial) d u v rho) volume 0 T) :
    (∫ t in (0 : ℝ)..T,
      mixed (resource u eta B initial)
        (resource v eta B initial) d u v rho t) ≤ 0 := by
  let phi := resource u eta B initial
  let psi := resource v eta B initial
  have hp : ∀ t ∈ uIcc (0 : ℝ) T, 0 < phi t := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact resource_positive u eta B initial t hB hi ht.1
  have hq : ∀ t ∈ uIcc (0 : ℝ) T, 0 < psi t := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact resource_positive v eta B initial t hB hi ht.1
  have hpODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt phi (B - eta * phi t * u t) t := by
    simpa only [phi, mul_assoc, mul_left_comm, mul_comm] using
      resource_ode_ae u eta B initial T hu
  have hqODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt psi (B - eta * psi t * v t) t := by
    simpa only [psi, mul_assoc, mul_left_comm, mul_comm] using
      resource_ode_ae v eta B initial T hv
  have hAC : AbsolutelyContinuousOnInterval
      (entropyWeight phi psi d rho) 0 T :=
    resource_pair_entropy_ac
      u v d eta B initial rho T hT hB hi hu hv hdAC
  have hbalance := entropy_balance_ae
    phi psi d u v S B eta rho c T heta hp hq hpODE hqODE hdODE
  have hderiv : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (entropyWeight phi psi d rho)
        (remainder phi psi d S rho c B t
          - eta * mixed phi psi d u v rho t) t := by
    filter_upwards [hbalance] with t ht
    intro hmem
    have h := ht hmem
    convert h using 1
    dsimp [remainder, mixed]
    ring
  have hsign : ∀ t ∈ Icc (0 : ℝ) T,
      remainder phi psi d S rho c B t ≤ 0 := by
    intro t ht
    have hmem : t ∈ uIcc (0 : ℝ) T := by
      rwa [uIcc_of_le hT]
    exact remainder_nonpos_at phi psi d S rho c B t
      (hp t hmem) (hq t hmem) hc hB (hdpos t ht) (hS t ht)
  have hzero : entropyWeight phi psi d rho 0 = 0 := by
    simp [entropyWeight, phi, psi, resource_initial, ne_of_gt hi]
  have hterminal : 0 ≤ entropyWeight phi psi d rho T :=
    entropy_weight_nonneg_at phi psi d rho T
      (hp T (right_mem_uIcc)) (hq T (right_mem_uIcc))
      (hdpos T ⟨hT, le_rfl⟩)
  have hboundary :
      entropyWeight phi psi d rho 0 ≤ entropyWeight phi psi d rho T := by
    rw [hzero]
    exact hterminal
  exact GSTStage08.ac_finite_interval_nonpos
    (entropyWeight phi psi d rho)
    (remainder phi psi d S rho c B)
    (mixed phi psi d u v rho)
    eta T heta hT hAC hderiv hRint hmint hsign hboundary

#print axioms remainder_nonpos_at
#print axioms entropy_weight_nonneg_at
#print axioms resource_mixed_integral_nonpos

end GSTStage16
