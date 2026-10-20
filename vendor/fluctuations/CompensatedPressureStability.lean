module

public import SKFluctuationsOAI.Probability.SKFluctuations.RealSKPressureL1

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem compensatedPressure_lower_approximate
    (n : ℕ) (hn : 0 < n) (b h e r bApprox hApprox : ℝ → ℝ)
    (he : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ e u)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0)
    (hbc : MonotoneOn (fun u => b u - e u) (Icc (0 : ℝ) 1))
    (hhc : MonotoneOn (fun u => h u + e u * r u) (Icc (0 : ℝ) 1))
    (hbc0 : 0 ≤ b 0 - e 0) (hhc0 : 0 ≤ h 0 + e 0 * r 0)
    (hp : MonotoneOn (fun u => e u * (r u) ^ 2) (Icc (0 : ℝ) 1))
    (hbApprox : MonotoneOn bApprox (Icc (0 : ℝ) 1))
    (hhApprox : MonotoneOn hApprox (Icc (0 : ℝ) 1))
    (hbApprox0 : 0 ≤ bApprox 0) (hhApprox0 : 0 ≤ hApprox 0)
    (x : OrderedFeatureIndex n → ℝ) :
    realOrderedSKPathPressure n b h x ≤
      realOrderedSKPathPressure n bApprox hApprox x +
        (1 / 4 : ℝ) * (∫ u in (0 : ℝ)..1, e u * (r u) ^ 2) +
        (1 / 4 : ℝ) * (∫ u in (0 : ℝ)..1, |(b u - e u) - bApprox u|) +
        (1 / 2 : ℝ) * (∫ u in (0 : ℝ)..1, |(h u + e u * r u) - hApprox u|) := by
  have hchord := pathCompensatedPressure_lower n hn b h e r he hb hh hb0 hh0
    hbc hhc hbc0 hhc0 hp x
  unfold pathCompensatedPressure at hchord
  have hdist := realOrderedSKPathPressure_l1_comparison n hn
    (fun u => b u - e u) (fun u => h u + e u * r u) bApprox hApprox
    hbc hhc hbApprox hhApprox hbc0 hhc0 hbApprox0 hhApprox0 x
  have hdist' := (le_abs_self _).trans hdist
  linarith

theorem compensatedPressure_lower_approximate_uniform
    (n : ℕ) (hn : 0 < n) (b h e r bApprox hApprox : ℝ → ℝ) (B H : ℝ)
    (he : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ e u)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0)
    (hbc : MonotoneOn (fun u => b u - e u) (Icc (0 : ℝ) 1))
    (hhc : MonotoneOn (fun u => h u + e u * r u) (Icc (0 : ℝ) 1))
    (hbc0 : 0 ≤ b 0 - e 0) (hhc0 : 0 ≤ h 0 + e 0 * r 0)
    (hp : MonotoneOn (fun u => e u * (r u) ^ 2) (Icc (0 : ℝ) 1))
    (hbApprox : MonotoneOn bApprox (Icc (0 : ℝ) 1))
    (hhApprox : MonotoneOn hApprox (Icc (0 : ℝ) 1))
    (hbApprox0 : 0 ≤ bApprox 0) (hhApprox0 : 0 ≤ hApprox 0)
    (hB : ∀ u ∈ Icc (0 : ℝ) 1, |(b u - e u) - bApprox u| ≤ B)
    (hH : ∀ u ∈ Icc (0 : ℝ) 1, |(h u + e u * r u) - hApprox u| ≤ H)
    (x : OrderedFeatureIndex n → ℝ) :
    realOrderedSKPathPressure n b h x ≤
      realOrderedSKPathPressure n bApprox hApprox x +
        (1 / 4 : ℝ) * (∫ u in (0 : ℝ)..1, e u * (r u) ^ 2) + B / 4 + H / 2 := by
  have hchord := pathCompensatedPressure_lower n hn b h e r he hb hh hb0 hh0
    hbc hhc hbc0 hhc0 hp x
  unfold pathCompensatedPressure at hchord
  have hdist := realOrderedSKPathPressure_uniform_comparison n hn
    (fun u => b u - e u) (fun u => h u + e u * r u) bApprox hApprox
    hbc hhc hbApprox hhApprox hbc0 hhc0 hbApprox0 hhApprox0 hB hH x
  have hdist' := (le_abs_self _).trans hdist
  linarith

end OAI.SKFluctuations
