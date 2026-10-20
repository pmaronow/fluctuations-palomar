module

public import ComparisonShiftedQuantileCDF

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 3200000

theorem comparison_actual_rescaled_clock_laws_ae_identified
    (q r : ℕ → ℝ → ℝ) (x : ℕ → ℝ) (U V : ℝ → ℝ)
    (hq : ∀n, MonotoneOn (q n) (Icc (0 : ℝ) 1))
    (hr : ∀n, MonotoneOn (r n) (Icc (0 : ℝ) 1))
    (hqb : ∀n u, u ∈ Icc (0 : ℝ) 1 → q n u ∈ Icc (0 : ℝ) 1)
    (hrb : ∀n u, u ∈ Icc (0 : ℝ) 1 → r n u ∈ Icc (0 : ℝ) 1)
    (hx : ∀n, 0 < x n) (hVm : Monotone V)
    (hU : ∀t : ℝ, Tendsto (fun n => (quantileMassProfile (q n) (hqb n)).val (x n*t)/x n)
      atTop (𝓝 (U t)))
    (hV : ∀t : ℝ, Tendsto (fun n => (quantileMassProfile (r n) (hrb n)).val (x n*t)/x n)
      atTop (𝓝 (V t)))
    (hlocal : ∀R : ℝ, 0 < R → ∃v : ℕ → ℝ,
      (∀n, v n ∈ Icc (0 : ℝ) 1) ∧
      (∀ᶠ n in atTop, x n*R < q n (v n) ∧ x n*R < r n (v n)) ∧
      Tendsto (fun n => (∫w : ParisiFinite.OrderPoint in {w | (w : ℝ) ≤ v n},
        |q n (w : ℝ)-r n (w : ℝ)| ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(x n)^2)
        atTop (𝓝 0)) : U =ᵐ[volume] V := by
  have hc : ∀ᵐ t : ℝ, ContinuousAt V t := by
    apply ae_iff.mpr
    exact hVm.countable_not_continuousAt.measure_zero volume
  filter_upwards [hc] with t ht
  let R := max (t+1) 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have htR : t < R := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  obtain ⟨v,hv,hcut,hzero⟩ := hlocal R hR
  exact comparison_actual_rescaled_clock_laws_identified q r x v U V hq hr hqb hrb hx hv
    hcut (fun s _ => hU s) (fun s _ => hV s) hzero htR ht

theorem comparison_shifted_scalar_radius_laws_ae_identified
    (A : ComparisonShiftedInverseSequence) (q : ℕ → ℝ → ℝ) (x : ℕ → ℝ)
    (U V : ℝ → ℝ) (horigin : ∀n, 0 ≤ A.origin n)
    (hq : ∀n, MonotoneOn (q n) (Icc (0 : ℝ) 1))
    (hqb : ∀n u, u ∈ Icc (0 : ℝ) 1 → q n u ∈ Icc (0 : ℝ) 1)
    (hx : ∀n, 0 < x n) (hVm : Monotone V)
    (hu0 : Tendsto (fun n => A.u0 n/x n) atTop (𝓝 0))
    (hU : ∀t : ℝ, Tendsto (fun n => (quantileMassProfile (q n) (hqb n)).val (x n*t)/x n)
      atTop (𝓝 (U t)))
    (hV : ∀t : ℝ, Tendsto (fun n => (A.alpha n).val.val (x n*t)/x n)
      atTop (𝓝 (V t)))
    (hlocal : ∀R : ℝ, 0 < R → ∃v : ℕ → ℝ,
      (∀n, v n ∈ Icc (0 : ℝ) 1) ∧
      (∀ᶠ n in atTop, x n*R < q n (v n) ∧ x n*R < A.radius n (v n)) ∧
      Tendsto (fun n => (∫w : ParisiFinite.OrderPoint in {w | (w : ℝ) ≤ v n},
        |q n (w : ℝ)-A.radius n (w : ℝ)| ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(x n)^2)
        atTop (𝓝 0)) : U =ᵐ[volume] V := by
  exact comparison_actual_rescaled_clock_laws_ae_identified q A.radius x U V hq
    (fun n => (A.radius_monotone n).monotoneOn _) hqb (A.radiusUnitBounds horigin)
    hx hVm hU (A.radius_quantile_cdf_limit horigin x hx hu0 V hV) hlocal

end OAI.SKFluctuations.LaplaceWindowFormalization
