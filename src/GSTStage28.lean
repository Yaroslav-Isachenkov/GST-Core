import GSTStage18
import GSTStage20
import GSTStage26
import GSTStage27

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage28

-- Packaging of the assumptions already used in stages 24, 26 and 27.
-- The sign of S is NOT included here.
structure CostateData where
  u : ℝ → ℝ
  omega : ℝ → ℝ
  eta : ℝ
  rho : ℝ
  a : ℝ
  c : ℝ
  q : ℝ
  target : ℝ
  U : ℝ
  M : ℝ
  heta : 0 ≤ eta
  hrho : 0 < rho
  hdecay : 0 < rho + a
  hc : 0 ≤ c
  hU : 0 ≤ U
  hM : 0 ≤ M
  huMeas : Measurable u
  hOmegaMeas : Measurable omega
  hu : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U
  hcont : ContinuousOn omega (Ici (0 : ℝ))
  hOmega : ∀ t : ℝ, 0 ≤ t → |omega t| ≤ M * (1 + t)

noncomputable def pOf (x : CostateData) : ℝ → ℝ :=
  GSTStage22.pCostate x.omega x.rho x.a x.q x.target

noncomputable def zOf (x : CostateData) : ℝ → ℝ :=
  GSTStage23.zCostate x.u (pOf x) x.eta x.rho x.c

noncomputable def dOf (x : CostateData) : ℝ → ℝ :=
  GSTStage18.canonicalD (pOf x) (zOf x) x.c x.eta

noncomputable def sOf (x : CostateData) : ℝ → ℝ :=
  GSTStage18.canonicalS (pOf x) x.omega x.a x.q x.target

-- A countable cover is needed: an uncountable intersection of
-- almost-everywhere statements is not used.
theorem ae_nonnegative_of_ae_on_intervals
    (Q : ℝ → Prop)
    (h : ∀ T : ℝ, 0 ≤ T →
      ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T → Q t) :
    ∀ᵐ t : ℝ, 0 ≤ t → Q t := by
  have hn : ∀ n : ℕ, ∀ᵐ t : ℝ,
      t ∈ uIcc (0 : ℝ) (n : ℝ) → Q t :=
    fun n => h (n : ℝ) (Nat.cast_nonneg n)
  have hall : ∀ᵐ t : ℝ, ∀ n : ℕ,
      t ∈ uIcc (0 : ℝ) (n : ℝ) → Q t :=
    ae_all_iff.2 hn
  filter_upwards [hall] with t ht
  intro ht0
  obtain ⟨n, hn⟩ := exists_nat_gt t
  apply ht n
  rw [uIcc_of_le (Nat.cast_nonneg n)]
  exact ⟨ht0, le_of_lt hn⟩

theorem p_solution
    (x : CostateData) (T : ℝ) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (pOf x) 0 T ∧
      (∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
        HasDerivAt (pOf x)
          ((x.rho + x.a) * pOf x t
            + 2 * x.q * (x.omega t - x.target)) t) := by
  exact GSTStage26.p_is_costate_solution
    x.omega x.rho x.a x.q x.target x.M T
    x.hdecay x.hM hT x.hcont x.hOmega

theorem z_solution
    (x : CostateData) (T : ℝ) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (zOf x) 0 T ∧
      (∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
        HasDerivAt (zOf x)
          ((x.rho + x.eta * x.u t) * zOf x t
            - x.c * x.u t * pOf x t) t) := by
  exact GSTStage27.canonical_z_is_costate_solution
    x.u x.omega x.eta x.rho x.a x.c x.q x.target x.U x.M T
    x.heta x.hrho x.hdecay x.hU x.hM hT
    x.huMeas x.hOmegaMeas x.hu x.hcont x.hOmega

theorem d_ac
    (x : CostateData) (T : ℝ) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (dOf x) 0 T := by
  exact GSTStage18.canonicalD_ac
    (pOf x) (zOf x) x.c x.eta T
    (p_solution x T hT).1 (z_solution x T hT).1

theorem s_continuous
    (x : CostateData) (T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (sOf x) (uIcc (0 : ℝ) T) := by
  have ho : ContinuousOn x.omega (uIcc (0 : ℝ) T) := by
    apply x.hcont.mono
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact ht.1
  exact GSTStage18.canonicalS_continuous
    (pOf x) x.omega x.a x.q x.target T
    (p_solution x T hT).1.continuousOn ho

theorem d_ode_ae_on
    (x : CostateData) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (dOf x)
        ((x.rho + x.eta * x.u t) * dOf x t
          + x.c * sOf x t) t := by
  exact GSTStage18.canonicalD_ode_ae
    (pOf x) (zOf x) x.omega x.u
    x.a x.c x.eta x.rho x.q x.target T
    (p_solution x T hT).2 (z_solution x T hT).2

theorem d_ode_ae
    (x : CostateData) :
    ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt (dOf x)
        ((x.rho + x.eta * x.u t) * dOf x t
          + x.c * sOf x t) t := by
  exact ae_nonnegative_of_ae_on_intervals
    (fun t => HasDerivAt (dOf x)
      ((x.rho + x.eta * x.u t) * dOf x t
        + x.c * sOf x t) t)
    (fun T hT => d_ode_ae_on x T hT)

theorem d_linear_growth
    (x : CostateData) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → |dOf x t| ≤ C * (1 + t) := by
  simpa only [dOf, pOf, zOf, GSTStage18.canonicalD] using
    GSTStage24.d_linear_growth_of_measurable_data
      x.u x.omega x.eta x.rho x.a x.c x.q x.target x.U x.M
      x.heta x.hrho x.hdecay x.hU x.hM
      x.huMeas x.hOmegaMeas x.hu x.hcont x.hOmega

theorem weighted_limit
    (x : CostateData) :
    Tendsto
      (fun t => GSTStage19.weight x.u x.eta x.rho t * dOf x t)
      atTop (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ := d_linear_growth x
  have hu : ∀ᵐ t : ℝ, 0 ≤ t → 0 ≤ x.u t :=
    Filter.Eventually.of_forall (fun t ht => (x.hu t ht).1)
  have hpoly : ∀ t : ℝ, 0 ≤ t →
      |dOf x t| ≤ C * (1 + t ^ (1 : ℕ)) := by
    intro t ht
    simpa only [pow_one] using hbound t ht
  exact GSTStage20.weighted_tail_from_polynomial_bound
    x.u (dOf x) x.eta x.rho C 1 x.heta x.hrho hu hpoly

-- S <= 0 remains an explicit condition.
-- The sign of d and its terminal limit are conclusions, not assumptions.
theorem d_nonneg
    (x : CostateData)
    (hS : ∀ t : ℝ, 0 ≤ t → sOf x t ≤ 0) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ dOf x t := by
  obtain ⟨C, _hC, hbound⟩ := d_linear_growth x
  have hu : ∀ᵐ t : ℝ, 0 ≤ t → 0 ≤ x.u t :=
    Filter.Eventually.of_forall (fun t ht => (x.hu t ht).1)
  have huInt : ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable x.u volume 0 T := by
    intro T hT
    exact GSTStage27.bounded_control_integrable
      x.u x.U T hT x.huMeas x.hu
  have hpoly : ∀ t : ℝ, 0 ≤ t →
      |dOf x t| ≤ C * (1 + t ^ (1 : ℕ)) := by
    intro t ht
    simpa only [pow_one] using hbound t ht
  exact GSTStage20.d_nonneg_from_polynomial_bound
    x.u (dOf x) (sOf x) x.eta x.rho x.c C 1
    x.heta x.hrho x.hc hu huInt
    (fun T hT => d_ac x T hT)
    (fun T hT => s_continuous x T hT)
    (d_ode_ae x) hS hpoly

#print axioms ae_nonnegative_of_ae_on_intervals
#print axioms p_solution
#print axioms z_solution
#print axioms d_ac
#print axioms s_continuous
#print axioms d_ode_ae_on
#print axioms d_ode_ae
#print axioms d_linear_growth
#print axioms weighted_limit
#print axioms d_nonneg

end GSTStage28
