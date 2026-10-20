module

public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyFullThermalGapIntegration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology ENNReal
set_option maxHeartbeats 18000000
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}
theorem inherited_scalar_cavity_residual_normalized_integral_exact {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {x v : ℝ} (hx : 0 < x) (hv : v ∈ Icc (0:ℝ) 1) :
    (∫w : ParisiFinite.OrderPoint, |M.inheritedScalarCavityResidual hT htotal w/x^3|
      ∂comparisonNormalizedClockMass x v) =
      (∫u in 0..v, |M.inheritedScalarCavityResidual hT htotal u|)/x^4 :=
  comparison_normalized_cubic_residual_integral_exact _ hx hv

theorem inherited_scalar_cavity_residual_normalized_integral_le {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {A eta v : ℝ} (hA : 0 < A) (hAx : A*M.xs ≤ 1)
    (hv : v ∈ Icc (0:ℝ) 1) (hvA : v ≤ A*M.xs)
    (Hgap : (∫u in 0..A*M.xs, |M.inheritedScalarCavityResidual hT htotal u|)
      ≤ eta*M.xs^4) :
    (∫w : ParisiFinite.OrderPoint, |M.inheritedScalarCavityResidual hT htotal w/M.xs^3|
      ∂comparisonNormalizedClockMass M.xs v) ≤ eta := by
  rw [M.inherited_scalar_cavity_residual_normalized_integral_exact hT htotal M.hxs hv]
  apply (div_le_iff₀ (pow_pos M.hxs 4)).mpr
  apply le_trans _ Hgap
  exact intervalIntegral.integral_mono_interval le_rfl hv.1 hvA
    (ae_of_all _ (fun _ => abs_nonneg _))
    (M.original_scalar_gap_intervalIntegrable hT (M.inheritedScalarMassProfile hT htotal)
      ⟨(mul_pos hA M.hxs).le,hAx⟩).abs

end ActualHighOnlyOverlapMinimum
theorem actual_original_scalar_gap_normalized_envelope_along_high_only
    {m delta cl cu Az C0 Ct D Bclock T : ℝ} {dim : ℕ→ℕ}
    (hT : 0 < T) {A : ℝ} (hA : 0 < A) (eta : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (Hgap : ActualOriginalScalarGapIntegralOnBandAlong_high_only hT A eta M) :
    ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
      ∀v∈Icc (0:ℝ) 1,v ≤ A*(M n).xs →
        Integrable (fun w : ParisiFinite.OrderPoint =>
          (M n).inheritedScalarCavityResidual hT htotal w/(M n).xs^3)
          (comparisonNormalizedClockMass (M n).xs v) ∧
        (∫w : ParisiFinite.OrderPoint,
          |(M n).inheritedScalarCavityResidual hT htotal w/(M n).xs^3|
            ∂comparisonNormalizedClockMass (M n).xs v) ≤ eta n := by
  have Hsmall := (hxlim.const_mul A).eventually
    (eventually_le_nhds (show A*(0:ℝ) < 1 by simp))
  filter_upwards [Hgap,Hsmall] with n hn hsmall
  obtain ⟨htotal,hgap⟩ := hn
  refine ⟨htotal,?_⟩
  intro v hv hvA
  exact ⟨(M n).inherited_scalar_cavity_residual_normalized_integrable hT htotal _ _,
    (M n).inherited_scalar_cavity_residual_normalized_integral_le hT htotal
      hA hsmall hv hvA hgap⟩

theorem actual_original_scalar_gap_normalized_l1_tendsto_zero_along_high_only
    {m delta cl cu Az C0 Ct D Bclock T : ℝ} {dim : ℕ→ℕ}
    (hT : 0 < T) {A : ℝ} (hA : 0 < A) (eta : ℕ→ℝ)
    (heta : Tendsto eta atTop (𝓝 0))
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (Hgap : ActualOriginalScalarGapIntegralOnBandAlong_high_only hT A eta M)
    (v : ℕ→ℝ) (hv : ∀n,v n∈Icc (0:ℝ) 1)
    (hvA : ∀ᶠn in atTop,v n ≤ A*(M n).xs) :
    (∀n,Integrable (fun w : ParisiFinite.OrderPoint =>
      (M n).inheritedScalarCavityResidual hT (htotal n) w/(M n).xs^3)
      (comparisonNormalizedClockMass (M n).xs (v n))) ∧
    Tendsto (fun n=>∫w : ParisiFinite.OrderPoint,
      |(M n).inheritedScalarCavityResidual hT (htotal n) w/(M n).xs^3|
        ∂comparisonNormalizedClockMass (M n).xs (v n)) atTop (𝓝 0) := by
  refine ⟨fun n=>(M n).inherited_scalar_cavity_residual_normalized_integrable
    hT (htotal n) _ _,?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun _=>integral_nonneg (fun _=>abs_nonneg _))) _ heta
  filter_upwards [actual_original_scalar_gap_normalized_envelope_along_high_only hT hA eta M hxlim Hgap,hvA]
    with n hn hnA
  obtain ⟨htotal',hn⟩ := hn
  exact (hn (v n) (hv n) hnA).2

end OAI.SKFluctuations.LaplaceWindowFormalization
