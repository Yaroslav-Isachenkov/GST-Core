import GSTStage120

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29 GSTStage31 GSTStage34 GSTStage118

namespace GSTStage121

theorem linear_state_difference_bound
    (f g : ℝ → ℝ) (a initial T L : ℝ)
    (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T)
    (hg : IntervalIntegrable g volume 0 T)
    (hbound : ∀ s ∈ Icc (0 : ℝ) T, |f s - g s| ≤ L) :
    |linearState f a initial T - linearState g a initial T| ≤ L * T := by
  have he :
      (fun s => Real.exp (-a * (T - s)) * (f s - g s)) =
      (fun s => Real.exp (-a * T) *
        (weightedInput f a s - weightedInput g a s)) := by
    funext s
    have hexp : Real.exp (-a * (T - s)) =
        Real.exp (-a * T) * Real.exp (a * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    unfold weightedInput
    ring
  have hrepr :
      linearState f a initial T - linearState g a initial T =
        ∫ s in (0 : ℝ)..T,
          Real.exp (-a * (T - s)) * (f s - g s) := by
    rw [he, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub
        (weighted_input_integrable f a T hf)
        (weighted_input_integrable g a T hg)]
    unfold linearState
    ring
  rw [hrepr]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := T) (C := L)
    (f := fun s => Real.exp (-a * (T - s)) * (f s - g s))
    (by
      intro s hs
      rw [uIoc_of_le hT] at hs
      have he0 : 0 ≤ Real.exp (-a * (T - s)) := (Real.exp_pos _).le
      have he1 : Real.exp (-a * (T - s)) ≤ 1 := by
        have hn : -a * (T - s) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr ha) (sub_nonneg.mpr hs.2)
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hn
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg he0]
      calc
        Real.exp (-a * (T - s)) * |f s - g s|
            ≤ 1 * |f s - g s| :=
          mul_le_mul_of_nonneg_right he1 (abs_nonneg _)
        _ = |f s - g s| := one_mul _
        _ ≤ L := hbound s ⟨hs.1.le, hs.2⟩)
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] using h

theorem resource_control_convex_difference_bound
    (x : StateData) (v : ℝ → ℝ) (ε T s : ℝ)
    (hvMeas : Measurable v)
    (hvBound : ∀ z : ℝ, 0 ≤ z → 0 ≤ v z ∧ v z ≤ x.U)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs : s ∈ Icc (0 : ℝ) T) :
    |resource (convexControl x.u v ε) x.eta x.B x.phiInitial s *
        convexControl x.u v ε s -
      resource x.u x.eta x.B x.phiInitial s * x.u s| ≤
      ε * x.U * (x.phiInitial + x.B * T) * (1 + x.eta * x.U * T) := by
  let p := convexControl x.u v ε
  let R : ℝ := x.phiInitial + x.B * T
  let K : ℝ := ε * x.eta * x.U
  have hT : 0 ≤ T := hs.1.trans hs.2
  have hU : 0 ≤ x.U := (x.hu 0 le_rfl).1.trans (x.hu 0 le_rfl).2
  have hR : 0 ≤ R := add_nonneg x.hphiInitial (mul_nonneg x.hB hT)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hε0 x.heta.le) hU
  have hRs : 0 ≤ x.phiInitial + x.B * s :=
    add_nonneg x.hphiInitial (mul_nonneg x.hB hs.1)
  have hRsT : x.phiInitial + x.B * s ≤ R := by
    dsimp only [R]
    exact add_le_add
      le_rfl (mul_le_mul_of_nonneg_left hs.2 x.hB)
  have hadm := convex_control_admissible
    x.u v x.U ε x.huMeas hvMeas x.hu hvBound hε0 hε1
  have hp : |p s| ≤ x.U := by
    rw [abs_of_nonneg (hadm.2 s hs.1).1]
    exact (hadm.2 s hs.1).2

  have hd : |p s - x.u s| ≤ ε * x.U := by
    have hb := GSTStage33.abs_sub_le_common_upper
      (v s) (x.u s) x.U
      (hvBound s hs.1).1 (hvBound s hs.1).2
      (x.hu s hs.1).1 (x.hu s hs.1).2
    have he : p s - x.u s = ε * (v s - x.u s) := by
      dsimp [p, convexControl]
      ring
    rw [he, abs_mul, abs_of_nonneg hε0]
    exact mul_le_mul_of_nonneg_left hb hε0

  have hr :
      |resource x.u x.eta x.B x.phiInitial s| ≤ R := by
    rw [abs_of_nonneg
      (GSTStage30.resource_nonneg x.u x.eta x.B x.phiInitial s
        x.hB x.hphiInitial hs.1)]
    exact (GSTStage33.resource_upper
      x.u x.eta x.B x.phiInitial x.U s hs.1
      x.heta.le x.hB x.hphiInitial x.huMeas x.hu).trans hRsT

  have hres :
      |resource p x.eta x.B x.phiInitial s -
        resource x.u x.eta x.B x.phiInitial s| ≤ K * T * R := by
    have hb := GSTStage120.resource_convex_difference_bound
      x v ε s hvMeas hvBound hε0 hε1 hs.1
    calc
      |resource p x.eta x.B x.phiInitial s -
          resource x.u x.eta x.B x.phiInitial s|
          ≤ K * s * (x.phiInitial + x.B * s) := hb
      _ ≤ K * T * R :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hs.2 hK)
          hRsT hRs (mul_nonneg hK hT)

  have he :
      resource p x.eta x.B x.phiInitial s * p s -
        resource x.u x.eta x.B x.phiInitial s * x.u s =
      (resource p x.eta x.B x.phiInitial s -
        resource x.u x.eta x.B x.phiInitial s) * p s +
      resource x.u x.eta x.B x.phiInitial s * (p s - x.u s) := by
    ring
  change |resource p x.eta x.B x.phiInitial s * p s -
    resource x.u x.eta x.B x.phiInitial s * x.u s| ≤ _
  rw [he]
  calc
    |(resource p x.eta x.B x.phiInitial s -
        resource x.u x.eta x.B x.phiInitial s) * p s +
      resource x.u x.eta x.B x.phiInitial s * (p s - x.u s)|
      ≤ |(resource p x.eta x.B x.phiInitial s -
          resource x.u x.eta x.B x.phiInitial s) * p s| +
        |resource x.u x.eta x.B x.phiInitial s * (p s - x.u s)| :=
      abs_add_le _ _
    _ = |resource p x.eta x.B x.phiInitial s -
          resource x.u x.eta x.B x.phiInitial s| * |p s| +
        |resource x.u x.eta x.B x.phiInitial s| * |p s - x.u s| := by
      rw [abs_mul, abs_mul]
    _ ≤ (K * T * R) * x.U + R * (ε * x.U) :=
      add_le_add
        (mul_le_mul hres hp (abs_nonneg _)
          (mul_nonneg (mul_nonneg hK hT) hR))
        (mul_le_mul hr hd (abs_nonneg _) hR)
    _ = ε * x.U * (x.phiInitial + x.B * T) *
        (1 + x.eta * x.U * T) := by
      dsimp only [K, R]
      ring

theorem competitor_convex_difference_bound
    (x : StateData) (v : ℝ → ℝ) (ε t : ℝ)
    (hvMeas : Measurable v)
    (hvBound : ∀ z : ℝ, 0 ≤ z → 0 ≤ v z ∧ v z ≤ x.U)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    |competitorState x (convexControl x.u v ε) t -
      competitorState x x.u t| ≤
      ε * x.c * x.U * t * (x.phiInitial + x.B * t) *
        (1 + x.eta * x.U * t) := by
  let p := convexControl x.u v ε
  let f := resourceForcing p x.eta x.B x.phiInitial x.c
  let g := resourceForcing x.u x.eta x.B x.phiInitial x.c
  let L : ℝ := x.c *
    (ε * x.U * (x.phiInitial + x.B * t) * (1 + x.eta * x.U * t))
  have hadm := convex_control_admissible
    x.u v x.U ε x.huMeas hvMeas x.hu hvBound hε0 hε1
  have hpInt : IntervalIntegrable p volume 0 t :=
    GSTStage27.bounded_control_integrable p x.U t ht hadm.1 hadm.2
  have huInt := GSTStage27.bounded_control_integrable
    x.u x.U t ht x.huMeas x.hu
  have hf : IntervalIntegrable f volume 0 t :=
    resource_forcing_integrable p x.eta x.B x.phiInitial x.c t hpInt
  have hg : IntervalIntegrable g volume 0 t :=
    resource_forcing_integrable x.u x.eta x.B x.phiInitial x.c t huInt
  have hb : ∀ s ∈ Icc (0 : ℝ) t, |f s - g s| ≤ L := by
    intro s hs
    have h := resource_control_convex_difference_bound
      x v ε t s hvMeas hvBound hε0 hε1 hs
    change |x.c * (resource p x.eta x.B x.phiInitial s * p s) -
      x.c * (resource x.u x.eta x.B x.phiInitial s * x.u s)| ≤ L
    rw [← mul_sub, abs_mul, abs_of_nonneg x.hc]
    exact mul_le_mul_of_nonneg_left h x.hc
  have h := linear_state_difference_bound
    f g x.a x.omegaInitial t L x.ha ht hf hg hb
  change |linearState f x.a x.omegaInitial t -
    linearState g x.a x.omegaInitial t| ≤ _
  calc
    |linearState f x.a x.omegaInitial t -
        linearState g x.a x.omegaInitial t| ≤ L * t := h
    _ = ε * x.c * x.U * t * (x.phiInitial + x.B * t) *
        (1 + x.eta * x.U * t) := by
      dsimp only [L]
      ring

end GSTStage121

#print axioms GSTStage121.linear_state_difference_bound
#print axioms GSTStage121.resource_control_convex_difference_bound
#print axioms GSTStage121.competitor_convex_difference_bound
