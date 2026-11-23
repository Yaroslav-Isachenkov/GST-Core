import GSTStage08
import GSTStage12
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage12

namespace GSTStage13

theorem resource_uniqueness
    (u f g : ℝ → ℝ) (eta B T : ℝ)
    (hT : 0 ≤ T)
    (hu : IntervalIntegrable u volume 0 T)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hg : AbsolutelyContinuousOnInterval g 0 T)
    (hfode : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt f (B - eta * u t * f t) t)
    (hgode : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt g (B - eta * u t * g t) t)
    (hinitial : f 0 = g 0) :
    EqOn f g (Icc (0 : ℝ) T) := by
  let W : ℝ → ℝ := fun t =>
    Real.exp (cumulative u eta t) * (f t - g t)
  have hA := cumulative_ac u eta T hu
  have hW : AbsolutelyContinuousOnInterval W 0 T :=
    (exp_ac (cumulative u eta) 0 T hA).fun_mul (hf.fun_sub hg)
  have hWderiv : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt W 0 t := by
    filter_upwards [hu.ae_hasDerivAt_integral, hfode, hgode]
      with t hdu hdf hdg
    intro ht
    have hdA : HasDerivAt (cumulative u eta) (eta * u t) t := by
      simpa only [cumulative] using
        (hdu ht 0 (left_mem_uIcc)).const_mul eta
    have hproduct := hdA.exp.mul ((hdf ht).sub (hdg ht))
    convert hproduct using 1
    simp only [Pi.sub_apply]
    ring
  have hW0 : W 0 = 0 := by
    simp [W, hinitial]
  intro t ht
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl ht.2
  have hdlocal : ∀ᵐ x : ℝ, x ∈ uIcc (0 : ℝ) t →
      HasDerivAt W 0 x := by
    filter_upwards [hWderiv] with x hx hxt
    exact hx (hsub hxt)
  have hFTC := GSTStage08.ac_integral_identity
    W (fun _ : ℝ => 0) 0 t (hW.mono hsub) hdlocal
  have hWt : W t = 0 := by
    simpa [hW0] using hFTC.symm
  have hmul :
      Real.exp (cumulative u eta t) * (f t - g t) = 0 := hWt
  have hdiff : f t - g t = 0 :=
    (mul_eq_zero.mp hmul).resolve_left
      (ne_of_gt (Real.exp_pos _))
  exact sub_eq_zero.mp hdiff

theorem resource_representation
    (u f : ℝ → ℝ) (eta B initial T : ℝ)
    (hT : 0 ≤ T)
    (hu : IntervalIntegrable u volume 0 T)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hfode : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt f (B - eta * u t * f t) t)
    (hinitial : f 0 = initial) :
    EqOn f (resource u eta B initial) (Icc (0 : ℝ) T) := by
  apply resource_uniqueness
    u f (resource u eta B initial) eta B T hT hu hf
    (resource_ac u eta B initial T hu) hfode
    (resource_ode_ae u eta B initial T hu)
  simpa only [resource_initial] using hinitial

theorem any_resource_solution_positive
    (u f : ℝ → ℝ) (eta B initial T : ℝ)
    (hT : 0 ≤ T) (hB : 0 ≤ B) (hi : 0 < initial)
    (hu : IntervalIntegrable u volume 0 T)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hfode : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt f (B - eta * u t * f t) t)
    (hinitial : f 0 = initial) :
    ∀ t ∈ Icc (0 : ℝ) T, 0 < f t := by
  have hrepr := resource_representation
    u f eta B initial T hT hu hf hfode hinitial
  intro t ht
  rw [hrepr ht]
  exact resource_positive u eta B initial t hB hi ht.1

theorem any_resource_solution_lower_bound
    (u f : ℝ → ℝ) (eta B initial U T : ℝ)
    (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (hB : 0 ≤ B) (hi : 0 ≤ initial)
    (hu : IntervalIntegrable u volume 0 T)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hfode : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt f (B - eta * u t * f t) t)
    (hinitial : f 0 = initial)
    (hupper : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) T),
      u s ≤ U) :
    initial * Real.exp (-(eta * U * T)) ≤ f T := by
  have hrepr := resource_representation
    u f eta B initial T hT hu hf hfode hinitial
  rw [hrepr ⟨hT, le_rfl⟩]
  exact resource_quantitative_lower_bound
    u eta B initial U T heta hB hi hT hu hupper

#print axioms resource_uniqueness
#print axioms resource_representation
#print axioms any_resource_solution_positive
#print axioms any_resource_solution_lower_bound

end GSTStage13
