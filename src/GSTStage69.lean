import GSTStage68

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11

namespace GSTStage69

theorem uniform_trajectory_bounds
    (x : StateData) (T : ℝ) (hT : 0 ≤ T) :
    ∃ R W : ℝ, 0 ≤ R ∧ 0 ≤ W ∧
      ∀ u : ℝ → ℝ, Measurable u →
        (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
        ∀ t ∈ Icc (0 : ℝ) T,
          (0 ≤ resource u x.eta x.B x.phiInitial t ∧
            resource u x.eta x.B x.phiInitial t ≤ R) ∧
          (0 ≤ competitorState x u t ∧
            competitorState x u t ≤ W) := by
  obtain ⟨M, hM, hm⟩ := GSTStage67.uniform_state_growth x
  refine ⟨x.phiInitial + x.B * T, M * (1 + T),
    add_nonneg x.hphiInitial (mul_nonneg x.hB hT),
    mul_nonneg hM (by linarith), ?_⟩
  intro u huMeas huBound t ht
  have hphi0 := GSTStage30.resource_nonneg
    u x.eta x.B x.phiInitial t x.hB x.hphiInitial ht.1
  have hphi := GSTStage33.resource_upper
    u x.eta x.B x.phiInitial x.U t ht.1 x.heta.le
    x.hB x.hphiInitial huMeas huBound
  have hBt := mul_le_mul_of_nonneg_left ht.2 x.hB
  have homega0 : 0 ≤ competitorState x u t :=
    GSTStage30.omega_nonneg
      u x.eta x.B x.phiInitial x.a x.c x.omegaInitial t
      x.hB x.hphiInitial x.hc x.homegaInitial ht.1
      (fun s hs => (huBound s hs).1)
  have homega := hm u huMeas huBound t ht.1
  have hMt : M * (1 + t) ≤ M * (1 + T) :=
    mul_le_mul_of_nonneg_left (by linarith [ht.2]) hM
  have homegaT : competitorState x u t ≤ M * (1 + T) :=
    le_trans (le_abs_self _) (le_trans homega hMt)
  exact ⟨⟨hphi0, by linarith⟩, ⟨homega0, homegaT⟩⟩

theorem uniform_rate_bounds
    (x : StateData) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Lphi Lomega : ℝ, 0 ≤ Lphi ∧ 0 ≤ Lomega ∧
      ∀ u : ℝ → ℝ, Measurable u →
        (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
        ∀ t ∈ Icc (0 : ℝ) T,
          |x.B - x.eta * u t *
            resource u x.eta x.B x.phiInitial t| ≤ Lphi ∧
          |-x.a * competitorState x u t +
            x.c * (resource u x.eta x.B x.phiInitial t * u t)|
              ≤ Lomega := by
  obtain ⟨R, W, hR, hW, hb⟩ :=
    uniform_trajectory_bounds x T hT
  have hU : 0 ≤ x.U :=
    le_trans (x.hu 0 le_rfl).1 (x.hu 0 le_rfl).2
  refine ⟨x.B + x.eta * x.U * R,
    x.a * W + x.c * (R * x.U),
    add_nonneg x.hB (mul_nonneg (mul_nonneg x.heta.le hU) hR),
    add_nonneg (mul_nonneg x.ha hW)
      (mul_nonneg x.hc (mul_nonneg hR hU)), ?_⟩
  intro u huMeas huBound t ht
  obtain ⟨⟨hphi0, hphiR⟩, ⟨homega0, homegaW⟩⟩ :=
    hb u huMeas huBound t ht
  have hu := huBound t ht.1
  have hetaU : x.eta * u t ≤ x.eta * x.U :=
    mul_le_mul_of_nonneg_left hu.2 x.heta.le
  have hproduct :
      x.eta * u t * resource u x.eta x.B x.phiInitial t ≤
        x.eta * x.U * R :=
    mul_le_mul hetaU hphiR hphi0 (mul_nonneg x.heta.le hU)
  have hproduct0 :
      0 ≤ x.eta * u t * resource u x.eta x.B x.phiInitial t :=
    mul_nonneg (mul_nonneg x.heta.le hu.1) hphi0
  have hforcingProduct :
      resource u x.eta x.B x.phiInitial t * u t ≤ R * x.U :=
    mul_le_mul hphiR hu.2 hu.1 hR
  have hforcing :
      x.c * (resource u x.eta x.B x.phiInitial t * u t) ≤
        x.c * (R * x.U) :=
    mul_le_mul_of_nonneg_left hforcingProduct x.hc
  have hforcing0 :
      0 ≤ x.c * (resource u x.eta x.B x.phiInitial t * u t) :=
    mul_nonneg x.hc (mul_nonneg hphi0 hu.1)
  have hdecay : x.a * competitorState x u t ≤ x.a * W :=
    mul_le_mul_of_nonneg_left homegaW x.ha
  have hdecay0 : 0 ≤ x.a * competitorState x u t :=
    mul_nonneg x.ha homega0
  constructor
  · apply abs_le.mpr
    constructor <;> linarith [x.hB]
  · apply abs_le.mpr
    constructor <;> nlinarith

#print axioms GSTStage69.uniform_trajectory_bounds
#print axioms GSTStage69.uniform_rate_bounds

end GSTStage69
