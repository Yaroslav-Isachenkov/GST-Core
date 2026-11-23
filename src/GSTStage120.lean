import GSTStage119

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage118 GSTStage119

namespace GSTStage120

theorem cumulative_increment_eq
    (u : ℝ → ℝ) (eta s t : ℝ)
    (hut : IntervalIntegrable u volume 0 t)
    (hus : IntervalIntegrable u volume 0 s) :
    cumulative u eta t - cumulative u eta s =
      eta * ∫ z in s..t, u z := by
  unfold cumulative
  rw [← mul_sub, intervalIntegral.integral_interval_sub_left hut hus]

theorem resource_kernel_convex_difference_bound
    (x : StateData) (v : ℝ → ℝ) (ε s t : ℝ)
    (hvMeas : Measurable v)
    (hvBound : ∀ z : ℝ, 0 ≤ z → 0 ≤ v z ∧ v z ≤ x.U)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    |Real.exp
        (cumulative (convexControl x.u v ε) x.eta s -
          cumulative (convexControl x.u v ε) x.eta t) -
      Real.exp (cumulative x.u x.eta s - cumulative x.u x.eta t)| ≤
        ε * x.eta * x.U * (t - s) := by
  let p := convexControl x.u v ε
  have ht : 0 ≤ t := hs.trans hst
  have hadm := convex_control_admissible
    x.u v x.U ε x.huMeas hvMeas x.hu hvBound hε0 hε1
  have hpT : IntervalIntegrable p volume 0 t :=
    GSTStage27.bounded_control_integrable p x.U t ht hadm.1 hadm.2
  have hpS : IntervalIntegrable p volume 0 s :=
    GSTStage27.bounded_control_integrable p x.U s hs hadm.1 hadm.2
  have huT := GSTStage27.bounded_control_integrable
    x.u x.U t ht x.huMeas x.hu
  have huS := GSTStage27.bounded_control_integrable
    x.u x.U s hs x.huMeas x.hu
  have hpST : IntervalIntegrable p volume s t := hpS.symm.trans hpT
  have huST : IntervalIntegrable x.u volume s t := huS.symm.trans huT
  have hep := cumulative_increment_eq p x.eta s t hpT hpS
  have heu := cumulative_increment_eq x.u x.eta s t huT huS

  have hAp : 0 ≤ cumulative p x.eta t - cumulative p x.eta s := by
    rw [hep]
    apply mul_nonneg x.heta.le
    apply intervalIntegral.integral_nonneg hst
    intro z hz
    exact (hadm.2 z (hs.trans hz.1)).1
  have hAu : 0 ≤ cumulative x.u x.eta t - cumulative x.u x.eta s := by
    rw [heu]
    apply mul_nonneg x.heta.le
    apply intervalIntegral.integral_nonneg hst
    intro z hz
    exact (x.hu z (hs.trans hz.1)).1

  have hd (z : ℝ) (hz : 0 ≤ z) : |p z - x.u z| ≤ ε * x.U := by
    have hb := GSTStage33.abs_sub_le_common_upper
      (v z) (x.u z) x.U
      (hvBound z hz).1 (hvBound z hz).2
      (x.hu z hz).1 (x.hu z hz).2
    have he : p z - x.u z = ε * (v z - x.u z) := by
      dsimp [p, convexControl]
      ring
    rw [he, abs_mul, abs_of_nonneg hε0]
    exact mul_le_mul_of_nonneg_left hb hε0

  have hi :
      |∫ z in s..t, p z - x.u z| ≤ (ε * x.U) * (t - s) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s) (b := t) (C := ε * x.U)
      (f := fun z => p z - x.u z)
      (by
        intro z hz
        rw [uIoc_of_le hst] at hz
        simpa only [Real.norm_eq_abs] using hd z (hs.trans hz.1.le))
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst)] using h

  have hdelta :
      |(cumulative p x.eta t - cumulative p x.eta s) -
        (cumulative x.u x.eta t - cumulative x.u x.eta s)| ≤
          ε * x.eta * x.U * (t - s) := by
    rw [hep, heu, ← mul_sub,
      ← intervalIntegral.integral_sub hpST huST,
      abs_mul, abs_of_nonneg x.heta.le]
    calc
      x.eta * |∫ z in s..t, p z - x.u z|
          ≤ x.eta * ((ε * x.U) * (t - s)) :=
        mul_le_mul_of_nonneg_left hi x.heta.le
      _ = ε * x.eta * x.U * (t - s) := by ring

  have h := exp_neg_lipschitz
    (cumulative p x.eta t - cumulative p x.eta s)
    (cumulative x.u x.eta t - cumulative x.u x.eta s) hAp hAu
  have h' :
      |Real.exp (cumulative p x.eta s - cumulative p x.eta t) -
        Real.exp (cumulative x.u x.eta s - cumulative x.u x.eta t)| ≤
      |(cumulative p x.eta t - cumulative p x.eta s) -
        (cumulative x.u x.eta t - cumulative x.u x.eta s)| := by
    simpa only [neg_sub] using h
  exact h'.trans hdelta

theorem resource_convex_difference_bound
    (x : StateData) (v : ℝ → ℝ) (ε t : ℝ)
    (hvMeas : Measurable v)
    (hvBound : ∀ z : ℝ, 0 ≤ z → 0 ≤ v z ∧ v z ≤ x.U)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    |resource (convexControl x.u v ε) x.eta x.B x.phiInitial t -
      resource x.u x.eta x.B x.phiInitial t| ≤
        ε * x.eta * x.U * t * (x.phiInitial + x.B * t) := by
  let p := convexControl x.u v ε
  let C : ℝ := ε * x.eta * x.U
  let kp : ℝ → ℝ := fun s =>
    Real.exp (cumulative p x.eta s - cumulative p x.eta t)
  let ku : ℝ → ℝ := fun s =>
    Real.exp (cumulative x.u x.eta s - cumulative x.u x.eta t)
  have hU : 0 ≤ x.U := (x.hu 0 le_rfl).1.trans (x.hu 0 le_rfl).2
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hε0 x.heta.le) hU
  have hadm := convex_control_admissible
    x.u v x.U ε x.huMeas hvMeas x.hu hvBound hε0 hε1
  have hpT : IntervalIntegrable p volume 0 t :=
    GSTStage27.bounded_control_integrable p x.U t ht hadm.1 hadm.2
  have huT := GSTStage27.bounded_control_integrable
    x.u x.U t ht x.huMeas x.hu
  have hkp : IntervalIntegrable kp volume 0 t :=
    (((cumulative_ac p x.eta t hpT).continuousOn.sub
      continuousOn_const).rexp).intervalIntegrable
  have hku : IntervalIntegrable ku volume 0 t :=
    (((cumulative_ac x.u x.eta t huT).continuousOn.sub
      continuousOn_const).rexp).intervalIntegrable

  have hk (s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
      |kp s - ku s| ≤ C * (t - s) :=
    resource_kernel_convex_difference_bound
      x v ε s t hvMeas hvBound hε0 hε1 hs hst

  have hzero :
      |Real.exp (-cumulative p x.eta t) -
        Real.exp (-cumulative x.u x.eta t)| ≤ C * t := by
    have h := hk 0 le_rfl ht
    simpa only [kp, ku, cumulative, intervalIntegral.integral_same,
      mul_zero, zero_sub, sub_zero] using h

  have hi :
      |(∫ s in (0 : ℝ)..t, kp s) -
        (∫ s in (0 : ℝ)..t, ku s)| ≤ (C * t) * t := by
    rw [← intervalIntegral.integral_sub hkp hku]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (C := C * t)
      (f := fun s => kp s - ku s)
      (by
        intro s hs
        rw [uIoc_of_le ht] at hs
        have hb := hk s hs.1.le hs.2
        have hle : C * (t - s) ≤ C * t :=
          mul_le_mul_of_nonneg_left (by linarith [hs.1]) hC
        simpa only [Real.norm_eq_abs] using hb.trans hle)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] using h

  have he :
      resource p x.eta x.B x.phiInitial t -
        resource x.u x.eta x.B x.phiInitial t =
      x.phiInitial *
        (Real.exp (-cumulative p x.eta t) -
          Real.exp (-cumulative x.u x.eta t)) +
      x.B * ((∫ s in (0 : ℝ)..t, kp s) -
        (∫ s in (0 : ℝ)..t, ku s)) := by
    rw [resource_kernel_representation, resource_kernel_representation]
    dsimp only [kp, ku]
    ring

  change |resource p x.eta x.B x.phiInitial t -
    resource x.u x.eta x.B x.phiInitial t| ≤ _
  rw [he]
  calc
    |x.phiInitial *
        (Real.exp (-cumulative p x.eta t) -
          Real.exp (-cumulative x.u x.eta t)) +
      x.B * ((∫ s in (0 : ℝ)..t, kp s) -
        (∫ s in (0 : ℝ)..t, ku s))|
      ≤ |x.phiInitial *
          (Real.exp (-cumulative p x.eta t) -
            Real.exp (-cumulative x.u x.eta t))| +
        |x.B * ((∫ s in (0 : ℝ)..t, kp s) -
          (∫ s in (0 : ℝ)..t, ku s))| :=
      abs_add_le _ _
    _ = x.phiInitial *
          |Real.exp (-cumulative p x.eta t) -
            Real.exp (-cumulative x.u x.eta t)| +
        x.B * |(∫ s in (0 : ℝ)..t, kp s) -
          (∫ s in (0 : ℝ)..t, ku s)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg x.hphiInitial,
        abs_of_nonneg x.hB]
    _ ≤ x.phiInitial * (C * t) + x.B * ((C * t) * t) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hzero x.hphiInitial)
        (mul_le_mul_of_nonneg_left hi x.hB)
    _ = ε * x.eta * x.U * t * (x.phiInitial + x.B * t) := by
      dsimp only [C]
      ring

end GSTStage120

#print axioms GSTStage120.cumulative_increment_eq
#print axioms GSTStage120.resource_kernel_convex_difference_bound
#print axioms GSTStage120.resource_convex_difference_bound
