import GSTStage05
import GSTStage10
import GSTStage12

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage12

namespace GSTStage15

noncomputable def entropyWeight
    (phi psi d : ℝ → ℝ) (rho t : ℝ) : ℝ :=
  Real.exp (-rho * t) * psi t * d t *
    (phi t / psi t - 1 - Real.log (phi t / psi t))

theorem discount_ac (rho T : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t => Real.exp (-rho * t)) 0 T := by
  have hi : AbsolutelyContinuousOnInterval
      (fun t : ℝ => t) 0 T := by
    have hconst : IntervalIntegrable
        (fun _ : ℝ => (1 : ℝ)) volume 0 T :=
      intervalIntegrable_const
    simpa using
      hconst.absolutelyContinuousOnInterval_intervalIntegral
        (c := 0) (left_mem_uIcc)
  exact exp_ac (fun t => -rho * t) 0 T (hi.const_mul (-rho))

theorem entropy_weight_ac
    (phi psi d : ℝ → ℝ) (rho T : ℝ)
    (hphi : AbsolutelyContinuousOnInterval phi 0 T)
    (hpsi : AbsolutelyContinuousOnInterval psi 0 T)
    (hd : AbsolutelyContinuousOnInterval d 0 T)
    (hphi_pos : ∀ t ∈ uIcc (0 : ℝ) T, 0 < phi t)
    (hpsi_pos : ∀ t ∈ uIcc (0 : ℝ) T, 0 < psi t) :
    AbsolutelyContinuousOnInterval
      (entropyWeight phi psi d rho) 0 T := by
  have hF := GSTStage10.positive_entropy_ac
    phi psi 0 T hphi hpsi hphi_pos hpsi_pos
  simpa only [entropyWeight] using
    (((discount_ac rho T).fun_mul hpsi).fun_mul hd).fun_mul hF

theorem entropy_balance_ae
    (phi psi d u v S : ℝ → ℝ)
    (B eta rho c T : ℝ)
    (_heta : 0 < eta)
    (hphi_pos : ∀ t ∈ uIcc (0 : ℝ) T, 0 < phi t)
    (hpsi_pos : ∀ t ∈ uIcc (0 : ℝ) T, 0 < psi t)
    (hphi : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt phi (B - eta * phi t * u t) t)
    (hpsi : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt psi (B - eta * psi t * v t) t)
    (hd : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt d ((rho + eta * v t) * d t + c * S t) t) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (entropyWeight phi psi d rho)
        (Real.exp (-rho * t) *
          (c * psi t * S t *
              (phi t / psi t - 1 - Real.log (phi t / psi t))
           - B * d t *
              (Real.log (phi t / psi t) + (phi t / psi t)⁻¹ - 1)
           - eta * d t * (phi t - psi t) * (u t - v t))) t := by
  filter_upwards [hphi, hpsi, hd] with t hp hq hdt
  intro ht
  unfold entropyWeight
  simpa only [mul_assoc] using
    (GSTStage05.weighted_entropy_balance
      phi psi d t B eta rho c (S t) (u t) (v t)
      (hphi_pos t ht) (hpsi_pos t ht)
      (hp ht) (hq ht) (hdt ht))

theorem resource_pair_entropy_ac
    (u v d : ℝ → ℝ) (eta B initial rho T : ℝ)
    (hT : 0 ≤ T) (hB : 0 ≤ B) (hi : 0 < initial)
    (hu : IntervalIntegrable u volume 0 T)
    (hv : IntervalIntegrable v volume 0 T)
    (hd : AbsolutelyContinuousOnInterval d 0 T) :
    AbsolutelyContinuousOnInterval
      (entropyWeight
        (resource u eta B initial)
        (resource v eta B initial) d rho) 0 T := by
  apply entropy_weight_ac
    (resource u eta B initial)
    (resource v eta B initial) d rho T
    (resource_ac u eta B initial T hu)
    (resource_ac v eta B initial T hv) hd
  · intro t ht
    rw [uIcc_of_le hT] at ht
    exact resource_positive u eta B initial t hB hi ht.1
  · intro t ht
    rw [uIcc_of_le hT] at ht
    exact resource_positive v eta B initial t hB hi ht.1

#print axioms discount_ac
#print axioms entropy_weight_ac
#print axioms entropy_balance_ae
#print axioms resource_pair_entropy_ac

end GSTStage15
