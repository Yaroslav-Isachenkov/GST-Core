import GSTStage156
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic

open Set

namespace GSTStage157

theorem first_bad_point_after_strict_prefix
    (w : ℝ → ℝ) (a b T c : ℝ)
    (hab : a < b) (hbT : b ≤ T)
    (hcont : ContinuousOn w (Icc b T))
    (hprefix : ∀ s ∈ Ioc a b, c < w s)
    (hbad : w T ≤ c) :
    ∃ t ∈ Ioc a T, w t ≤ c ∧
      ∀ s ∈ Ioo a t, c < w s := by
  obtain ⟨v, hv, he⟩ :=
    (lowerSemicontinuousOn_iff_preimage_Iic.mp
      hcont.lowerSemicontinuousOn) c
  let K : Set ℝ := Icc b T ∩ w ⁻¹' Iic c
  have hK : IsCompact K := by
    change IsCompact (Icc b T ∩ w ⁻¹' Iic c)
    rw [he]
    exact isCompact_Icc.inter_right hv
  have hKT : T ∈ K := ⟨⟨hbT, le_rfl⟩, hbad⟩
  obtain ⟨t, ht, hmin⟩ :=
    hK.exists_isMinOn ⟨T, hKT⟩
      (show ContinuousOn (fun s : ℝ => s) K from continuous_id.continuousOn)
  have htBounds : b ≤ t ∧ t ≤ T := ht.1
  have htBad : w t ≤ c := ht.2
  refine ⟨t, ⟨lt_of_lt_of_le hab htBounds.1, htBounds.2⟩, htBad, ?_⟩
  intro s hs
  by_cases hsb : s ≤ b
  · exact hprefix s ⟨hs.1, hsb⟩
  · have hbs : b < s := lt_of_not_ge hsb
    by_contra hn
    have hsBad : w s ≤ c := le_of_not_gt hn
    have hsK : s ∈ K :=
      ⟨⟨hbs.le, le_trans hs.2.le htBounds.2⟩, hsBad⟩
    have hts : t ≤ s := hmin hsK
    exact (not_le_of_gt hs.2) hts

theorem strict_threshold_persistence
    (w : ℝ → ℝ) (a b T c : ℝ)
    (hab : a < b) (_hbT : b ≤ T)
    (hcont : ContinuousOn w (Icc b T))
    (hprefix : ∀ s ∈ Ioc a b, c < w s)
    (hstep : ∀ t ∈ Ioc a T,
      (∀ s ∈ Ioo a t, c < w s) → c < w t) :
    ∀ t ∈ Ioc a T, c < w t := by
  intro t ht
  by_cases htb : t ≤ b
  · exact hprefix t ⟨ht.1, htb⟩
  · have hbt : b ≤ t := (lt_of_not_ge htb).le
    by_contra hn
    have hbad : w t ≤ c := le_of_not_gt hn
    have hcont' : ContinuousOn w (Icc b t) :=
      hcont.mono (Icc_subset_Icc le_rfl ht.2)
    obtain ⟨s, hs, hsBad, hsBefore⟩ :=
      first_bad_point_after_strict_prefix
        w a b t c hab hbt hcont' hprefix hbad
    have hsGood := hstep s ⟨hs.1, le_trans hs.2 ht.2⟩ hsBefore
    exact (not_le_of_gt hsGood) hsBad

end GSTStage157

#print axioms GSTStage157.first_bad_point_after_strict_prefix
#print axioms GSTStage157.strict_threshold_persistence
