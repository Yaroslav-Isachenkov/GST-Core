import GSTStage22
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology
open GSTStage21 GSTStage22

namespace GSTStage23

noncomputable def zKernel
    (u : ℝ → ℝ) (eta rho t s : ℝ) : ℝ :=
  Real.exp (-rho * (s - t) - eta * ∫ r in t..s, u r)

noncomputable def zCostate
    (u p : ℝ → ℝ) (eta rho c t : ℝ) : ℝ :=
  c * ∫ s in Ioi t, zKernel u eta rho t s * (u s * p s)

noncomputable def zBound (rho c U P : ℝ) : ℝ :=
  |c| * ((U * P) * moment rho)

-- Nonnegative effort can only decrease the exponential kernel.
theorem z_kernel_bound
    (u : ℝ → ℝ) (eta rho t s : ℝ)
    (heta : 0 ≤ eta) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hu : ∀ r : ℝ, 0 ≤ r → 0 ≤ u r) :
    0 ≤ zKernel u eta rho t (t + s) ∧
      zKernel u eta rho t (t + s) ≤ Real.exp (-rho * s) := by
  have hts : t ≤ t + s := by linarith
  have hae : ∀ᵐ r ∂volume.restrict (Icc t (t + s)), 0 ≤ u r := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall
      (fun r hr => hu r (le_trans ht hr.1))
  have hint : 0 ≤ ∫ r in t..(t + s), u r :=
    intervalIntegral.integral_nonneg_of_ae_restrict hts hae
  unfold zKernel
  simp only [add_sub_cancel_left]
  constructor
  · exact le_of_lt (Real.exp_pos _)
  · apply Real.exp_le_exp.mpr
    exact sub_le_self _ (mul_nonneg heta hint)

theorem z_shifted
    (u p : ℝ → ℝ) (eta rho c t : ℝ) :
    zCostate u p eta rho c t =
      c * ∫ s in Ioi (0 : ℝ),
        zKernel u eta rho t (t + s) * (u (t + s) * p (t + s)) := by
  unfold zCostate
  exact congrArg (fun x : ℝ => c * x)
    (tail_integral_shift
      (fun s => zKernel u eta rho t s * (u s * p s)) t).symm

-- Measurability is explicit here; no growth assumption on z is used.
theorem z_integrable_and_bound
    (u p : ℝ → ℝ) (eta rho c U P t : ℝ)
    (heta : 0 ≤ eta) (hrho : 0 < rho)
    (hU : 0 ≤ U) (hP : 0 ≤ P) (ht : 0 ≤ t)
    (hu : ∀ r : ℝ, 0 ≤ r → 0 ≤ u r ∧ u r ≤ U)
    (hp : ∀ r : ℝ, 0 ≤ r → |p r| ≤ P * (1 + r))
    (hmeas : AEStronglyMeasurable
      (fun s => zKernel u eta rho t (t + s) *
        (u (t + s) * p (t + s)))
      (volume.restrict (Ioi (0 : ℝ)))) :
    IntegrableOn
      (fun s => zKernel u eta rho t s * (u s * p s)) (Ioi t) ∧
      |zCostate u p eta rho c t| ≤ zBound rho c U P * (1 + t) := by
  have hinput : ∀ s : ℝ, 0 < s →
      |u (t + s) * p (t + s)| ≤ (U * P) * (1 + t + s) := by
    intro s hs
    have hx : 0 ≤ t + s := by linarith
    rw [abs_mul, abs_of_nonneg (hu (t + s) hx).1]
    calc
      u (t + s) * |p (t + s)| ≤ U * |p (t + s)| :=
        mul_le_mul_of_nonneg_right (hu (t + s) hx).2 (abs_nonneg _)
      _ ≤ U * (P * (1 + (t + s))) :=
        mul_le_mul_of_nonneg_left (hp (t + s) hx) hU
      _ = (U * P) * (1 + t + s) := by ring
  have hkernel : ∀ s : ℝ, 0 < s →
      0 ≤ zKernel u eta rho t (t + s) ∧
        zKernel u eta rho t (t + s) ≤ Real.exp (-rho * s) := by
    intro s hs
    exact z_kernel_bound u eta rho t s heta ht (le_of_lt hs)
      (fun r hr => (hu r hr).1)
  obtain ⟨hi, hb⟩ := kernel_affine_integrable_and_bound
    (fun s => zKernel u eta rho t (t + s))
    (fun s => u (t + s) * p (t + s))
    rho (U * P) t hrho (mul_nonneg hU hP) ht hmeas
    (fun s hs => (hkernel s hs).1)
    (fun s hs => (hkernel s hs).2)
    hinput
  refine ⟨tail_integrable_of_shift
    (fun s => zKernel u eta rho t s * (u s * p s)) t hi, ?_⟩
  rw [z_shifted, abs_mul]
  calc
    |c| * |∫ s in Ioi (0 : ℝ),
        zKernel u eta rho t (t + s) * (u (t + s) * p (t + s))|
        ≤ |c| * (((U * P) * (1 + t)) * moment rho) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = zBound rho c U P * (1 + t) := by
      unfold zBound
      ring

theorem z_linear_growth
    (u p : ℝ → ℝ) (eta rho c U P : ℝ)
    (heta : 0 ≤ eta) (hrho : 0 < rho)
    (hU : 0 ≤ U) (hP : 0 ≤ P)
    (hu : ∀ r : ℝ, 0 ≤ r → 0 ≤ u r ∧ u r ≤ U)
    (hp : ∀ r : ℝ, 0 ≤ r → |p r| ≤ P * (1 + r))
    (hmeas : ∀ t : ℝ, 0 ≤ t →
      AEStronglyMeasurable
        (fun s => zKernel u eta rho t (t + s) *
          (u (t + s) * p (t + s)))
        (volume.restrict (Ioi (0 : ℝ)))) :
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ t : ℝ, 0 ≤ t →
      |zCostate u p eta rho c t| ≤ Z * (1 + t) := by
  have hzero := (z_integrable_and_bound u p eta rho c U P 0
    heta hrho hU hP (le_refl 0) hu hp (hmeas 0 (le_refl 0))).2
  have hZ : 0 ≤ zBound rho c U P := by
    have h := le_trans (abs_nonneg (zCostate u p eta rho c 0)) hzero
    simpa only [add_zero, mul_one] using h
  refine ⟨zBound rho c U P, hZ, ?_⟩
  intro t ht
  exact (z_integrable_and_bound u p eta rho c U P t
    heta hrho hU hP ht hu hp (hmeas t ht)).2

theorem d_bound_from_bounds
    (p z c eta P Z t : ℝ)
    (hp : |p| ≤ P * (1 + t))
    (hz : |z| ≤ Z * (1 + t)) :
    |c * p - eta * z| ≤ (|c| * P + |eta| * Z) * (1 + t) := by
  have htriangle : |c * p - eta * z| ≤ |c * p| + |eta * z| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (c * p), le_abs_self (eta * z)]
    · linarith [le_abs_self (c * p), neg_abs_le (eta * z)]
  rw [abs_mul, abs_mul] at htriangle
  calc
    |c * p - eta * z| ≤ |c| * |p| + |eta| * |z| := htriangle
    _ ≤ |c| * (P * (1 + t)) + |eta| * (Z * (1 + t)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hp (abs_nonneg c))
        (mul_le_mul_of_nonneg_left hz (abs_nonneg eta))
    _ = (|c| * P + |eta| * Z) * (1 + t) := by ring

-- Combined result for the integral-defined p and z.
-- Growth of neither costate nor d is assumed.
theorem integral_costates_d_linear_growth
    (u omega : ℝ → ℝ) (eta rho a c q target U M : ℝ)
    (heta : 0 ≤ eta) (hrho : 0 < rho)
    (hdecay : 0 < rho + a)
    (hU : 0 ≤ U) (hM : 0 ≤ M)
    (hu : ∀ r : ℝ, 0 ≤ r → 0 ≤ u r ∧ u r ≤ U)
    (hcont : ContinuousOn omega (Ici (0 : ℝ)))
    (hOmega : ∀ r : ℝ, 0 ≤ r → |omega r| ≤ M * (1 + r))
    (hmeas : ∀ t : ℝ, 0 ≤ t →
      AEStronglyMeasurable
        (fun s => zKernel u eta rho t (t + s) *
          (u (t + s) * pCostate omega rho a q target (t + s)))
        (volume.restrict (Ioi (0 : ℝ)))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 ≤ t →
      |c * pCostate omega rho a q target t -
        eta * zCostate u (pCostate omega rho a q target) eta rho c t|
        ≤ D * (1 + t) := by
  obtain ⟨P, hP, hp⟩ :=
    p_linear_growth omega rho a q target M hdecay hM hcont hOmega
  obtain ⟨Z, hZ, hz⟩ :=
    z_linear_growth u (pCostate omega rho a q target)
      eta rho c U P heta hrho hU hP hu hp hmeas
  refine ⟨|c| * P + |eta| * Z,
    add_nonneg (mul_nonneg (abs_nonneg c) hP)
      (mul_nonneg (abs_nonneg eta) hZ), ?_⟩
  intro t ht
  exact d_bound_from_bounds
    (pCostate omega rho a q target t)
    (zCostate u (pCostate omega rho a q target) eta rho c t)
    c eta P Z t (hp t ht) (hz t ht)

#print axioms z_kernel_bound
#print axioms z_shifted
#print axioms z_integrable_and_bound
#print axioms z_linear_growth
#print axioms d_bound_from_bounds
#print axioms integral_costates_d_linear_growth

end GSTStage23
