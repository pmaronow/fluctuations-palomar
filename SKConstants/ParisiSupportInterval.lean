module

public import SKConstants.Upstream.OAI.Probability.SKSupport.Support.Closure
public import Mathlib.Probability.CDF

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

namespace SKConstants.ParisiFullSupport

theorem exists_bounded_support_gap {S : Set ℝ} (hS : IsClosed S)
    {Q x : ℝ} (h0 : 0 ∈ S) (hQ : Q ∈ S) (hx0 : 0 ≤ x) (hxQ : x ≤ Q)
    (hx : x ∉ S) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ Q ∧ a ∈ S ∧ b ∈ S ∧
      ∀ t ∈ Ioo a b, t ∉ S := by
  have hA : IsCompact (S ∩ Icc 0 x) := isCompact_Icc.inter_left hS
  have hB : IsCompact (S ∩ Icc x Q) := isCompact_Icc.inter_left hS
  obtain ⟨a, ha⟩ := hA.exists_isGreatest ⟨0, h0, le_rfl, hx0⟩
  obtain ⟨b, hb⟩ := hB.exists_isLeast ⟨Q, hQ, hxQ, le_rfl⟩
  have hax : a < x := lt_of_le_of_ne ha.1.2.2 (by
    intro he
    exact hx (he ▸ ha.1.1))
  have hxb : x < b := lt_of_le_of_ne hb.1.2.1 (by
    intro he
    exact hx (he ▸ hb.1.1))
  refine ⟨a, b, ha.1.2.1, hax.trans hxb, hb.1.2.2, ha.1.1, hb.1.1, ?_⟩
  intro t ht hts
  by_cases htx : t ≤ x
  · exact (not_lt_of_ge (ha.2 ⟨hts, ha.1.2.1.trans ht.1.le, htx⟩)) ht.1
  · exact (not_lt_of_ge (hb.2 ⟨hts, (le_of_not_ge htx),
      ht.2.le.trans hb.1.2.2⟩)) ht.2

theorem cdf_constant_on_support_gap (μ : ProbabilityMeasure ℝ) {a b : ℝ}
    (hab : a < b) (hgap : ∀ t ∈ Ioo a b, t ∉ (μ : Measure ℝ).support) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t ∈ Ioo a b, cdf (μ : Measure ℝ) t = c := by
  let m := (a + b) / 2
  have hm : m ∈ Ioo a b := by constructor <;> dsimp [m] <;> linarith
  refine ⟨cdf (μ : Measure ℝ) m, cdf_nonneg _ _, ?_⟩
  have he {u v : ℝ} (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) (huv : u ≤ v) :
      cdf (μ : Measure ℝ) u = cdf (μ : Measure ℝ) v := by
    have hz : (μ : Measure ℝ) (Ioc u v) = 0 := by
      apply measure_mono_null _ (μ : Measure ℝ).measure_compl_support
      intro z hz
      exact hgap z ⟨hu.1.trans hz.1, hz.2.trans_lt hv.2⟩
    rw [← measure_cdf (μ : Measure ℝ), StieltjesFunction.measure_Ioc,
      ENNReal.ofReal_eq_zero] at hz
    linarith [(cdf (μ : Measure ℝ)).mono huv]
  intro t ht
  rcases le_total t m with htm | hmt
  · exact he ht hm htm
  · exact (he hm ht hmt).symm

theorem support_interval_of_gap_curvature (μ : ProbabilityMeasure ℝ) (Q : ℝ)
    (q q' : ℝ → ℝ)
    (hS : (μ : Measure ℝ).support ⊆ Icc 0 Q)
    (h0 : 0 ∈ (μ : Measure ℝ).support) (hQ : Q ∈ (μ : Measure ℝ).support)
    (hq : ContinuousOn q (Icc 0 Q)) (hq' : ContinuousOn q' (Icc 0 Q))
    (hd : ∀ t ∈ Ioo 0 Q, HasDerivAt q (q' t) t)
    (hcontact : ∀ t ∈ (μ : Measure ℝ).support, q t = t ∧ q' t ≤ 1)
    (hpositive : ∀ a b c : ℝ, 0 ≤ a → a < b → b ≤ Q → 0 < c →
      (∀ t ∈ Ioo a b, cdf (μ : Measure ℝ) t = c) →
      ∀ t ∈ Ioo a b, 0 < (deriv^[2] q') t)
    (hzero : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ Q →
      (∀ t ∈ Ioo a b, cdf (μ : Measure ℝ) t = 0) →
      ∀ t ∈ Ioo a b, 0 < deriv q' t) :
    (μ : Measure ℝ).support = Icc 0 Q ∧ ∀ t ∈ Icc 0 Q, q t = t := by
  have hfull : Icc 0 Q ⊆ (μ : Measure ℝ).support := by
    intro x hx
    by_contra hxs
    obtain ⟨a, b, ha, hab, hb, haS, hbS, hgap⟩ :=
      exists_bounded_support_gap (μ : Measure ℝ).isClosed_support h0 hQ hx.1 hx.2 hxs
    have hsub : Icc a b ⊆ Icc 0 Q := by
      intro t ht
      exact ⟨ha.trans ht.1, ht.2.trans hb⟩
    have hderiv : ∀ t ∈ Ioo a b, HasDerivAt q (q' t) t := by
      intro t ht
      exact hd t ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩
    obtain ⟨c, hc, hconstant⟩ := cdf_constant_on_support_gap μ hab hgap
    rcases eq_or_lt_of_le hc with hc | hc
    · exact SKConstantsOAI.ZeroTemperatureSK.SupportDeterministic.Variation.no_zero_constant_gap
        hab (hq.mono hsub) (hq'.mono hsub) hderiv (hcontact a haS).1
        (hcontact b hbS).1 (hzero a b ha hab hb (by simpa only [← hc] using hconstant))
        (hcontact b hbS).2
    · exact SKConstantsOAI.ZeroTemperatureSK.SupportDeterministic.Variation.no_positive_constant_gap
        hab (hq.mono hsub) (hq'.mono hsub) hderiv (hcontact a haS).1
        (hcontact b hbS).1 (hpositive a b c ha hab hb hc hconstant)
        (hcontact a haS).2 (hcontact b hbS).2
  exact ⟨Subset.antisymm hS hfull, fun t ht => (hcontact t (hfull ht)).1⟩

end SKConstants.ParisiFullSupport
