import GSTStage97

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage34

namespace GSTStage98

theorem continuous_subinterval_integral_limit
    (T t : ℝ) (htT : t ≤ T)
    (phi : ℕ → ℝ → ℝ) (Phi : ℝ → ℝ)
    (F : ℕ → BoundedContinuousFunction (Icc (0 : ℝ) T) ℝ)
    (Flim : BoundedContinuousFunction (Icc (0 : ℝ) T) ℝ)
    (hphi : ∀ n, ContinuousOn (phi n) (Icc (0 : ℝ) T))
    (hPhi : ContinuousOn Phi (Icc (0 : ℝ) T))
    (hF : ∀ n s (hs : s ∈ Icc (0 : ℝ) T), F n ⟨s, hs⟩ = phi n s)
    (hFlim : ∀ s (hs : s ∈ Icc (0 : ℝ) T), Flim ⟨s, hs⟩ = Phi s)
    (hconv : Tendsto F atTop (𝓝 Flim)) :
    Tendsto (fun n => ∫ s in Icc (0 : ℝ) t, phi n s)
      atTop (𝓝 (∫ s in Icc (0 : ℝ) t, Phi s)) := by
  let hp : MemLp (fun _ : ℝ => (1 : ℝ)) 2
      (volume.restrict (Icc (0 : ℝ) T)) := memLp_const 1
  let oneLp : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)) :=
    hp.toLp (fun _ => 1)
  have hl := GSTStage94.continuous_subinterval_product_limit
    T t htT (fun _ _ => 1) phi (fun _ => 1) Phi
    (fun _ => oneLp) oneLp F Flim ‖oneLp‖
    (fun _ => hp.coeFn_toLp) hp.coeFn_toLp
    (fun _ => le_rfl) (fun _ => tendsto_const_nhds)
    hphi hPhi hF hFlim hconv
  simpa only [mul_one] using hl

theorem competitor_integral_balance
    (x : StateData) (u : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hu : IntervalIntegrable u volume 0 T) :
    competitorState x u T =
      x.omegaInitial - x.a * (∫ s in Icc (0 : ℝ) T, competitorState x u s) +
        x.c * (∫ s in Icc (0 : ℝ) T,
          resource u x.eta x.B x.phiInitial s * u s) := by
  have hs := GSTStage29.omega_solution
    u x.eta x.B x.phiInitial x.a x.c x.omegaInitial T hu
  have ho : IntervalIntegrable (competitorState x u) volume 0 T :=
    hs.1.continuousOn.intervalIntegrable
  have hp : IntervalIntegrable
      (fun s => resource u x.eta x.B x.phiInitial s * u s) volume 0 T :=
    hu.continuousOn_mul
      (resource_continuousOn u x.eta x.B x.phiInitial T hu)
  have hinit : competitorState x u 0 = x.omegaInitial :=
    GSTStage29.omega_initial
      u x.eta x.B x.phiInitial x.a x.c x.omegaInitial
  have hFTC := GSTStage08.ac_integral_identity
    (competitorState x u)
    (fun s => -x.a * competitorState x u s +
      x.c * (resource u x.eta x.B x.phiInitial s * u s))
    0 T hs.1 hs.2
  rw [intervalIntegral.integral_add
        (ho.const_mul (-x.a)) (hp.const_mul x.c),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      hinit] at hFTC
  have hset (f : ℝ → ℝ) :
      (∫ s in (0 : ℝ)..T, f s) = ∫ s in Icc (0 : ℝ) T, f s := by
    rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]
  simp only [hset] at hFTC
  linarith

theorem competitor_limit_integral_balance
    (x : StateData) (u : ℕ → ℝ → ℝ) (a Phi Omega : ℝ → ℝ)
    (hu : ∀ n T, 0 ≤ T → IntervalIntegrable (u n) volume 0 T)
    (hstate : ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun n => competitorState x (u n) t) atTop (𝓝 (Omega t)))
    (hintegral : ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun n => ∫ s in Icc (0 : ℝ) t, competitorState x (u n) s)
        atTop (𝓝 (∫ s in Icc (0 : ℝ) t, Omega s)))
    (hproduct : ∀ t : ℝ, 0 ≤ t →
      Tendsto
        (fun n => ∫ s in Icc (0 : ℝ) t,
          resource (u n) x.eta x.B x.phiInitial s * u n s)
        atTop (𝓝 (∫ s in Icc (0 : ℝ) t, Phi s * a s))) :
    ∀ t : ℝ, 0 ≤ t →
      Omega t = x.omegaInitial -
        x.a * (∫ s in Icc (0 : ℝ) t, Omega s) +
        x.c * (∫ s in Icc (0 : ℝ) t, Phi s * a s) := by
  intro t ht
  have hc (c : ℝ) : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) :=
    tendsto_const_nhds
  have hr := ((hc x.omegaInitial).sub
    ((hc x.a).mul (hintegral t ht))).add
    ((hc x.c).mul (hproduct t ht))
  have he (n : ℕ) :
      competitorState x (u n) t =
        x.omegaInitial -
          x.a * (∫ s in Icc (0 : ℝ) t, competitorState x (u n) s) +
          x.c * (∫ s in Icc (0 : ℝ) t,
            resource (u n) x.eta x.B x.phiInitial s * u n s) :=
    competitor_integral_balance x (u n) t ht (hu n t ht)
  exact tendsto_nhds_unique
    ((hstate t ht).congr' (Filter.Eventually.of_forall he)) hr

end GSTStage98

#print axioms GSTStage98.continuous_subinterval_integral_limit
#print axioms GSTStage98.competitor_integral_balance
#print axioms GSTStage98.competitor_limit_integral_balance
