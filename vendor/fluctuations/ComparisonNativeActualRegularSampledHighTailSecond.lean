module

public import ComparisonNativeActualRegularHighMassPhysicalDyad
public import ComparisonNativeHighTailL1Transfer
public import ComparisonNativeActualRegularHighMassThermalTail

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_regular_sampled_original_high_tail_second
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0<c) (hcouter : 2*cu*(Az+1)≤c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
        M.xs^2≤Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale≤1 →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀U : ℕ,U≤as.length → 2*c*M.canonicalDirectTestBandScale≤partitionPoint 0 as U →
          ClockTree.edgeBudget 0 as
            (fun j=>if j<U then 0 else (nativeOriginalCutLowErrorRadius n M.bf M.hf as j)^2)≤
            M.context.N^(-(actualMassSavingExponent m delta/8))*
              (M.xs^4/M.canonicalDirectTestBandScale^2) := by
  have Htail:=eventually_actual_regular_strong_high_mass_thermal_tail
    (D:=D) (Cs:=Cs) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let eta:=actualMassSavingExponent m delta
  have heta : 0<eta:=actualMassSavingExponent_pos hm hdelta
  have Hcoef:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=2) (d:=1) (q:=-eta/4) (r:=-eta/8)
      zero_lt_one (by linarith))
  filter_upwards [Htail,Hcoef] with n hnTail hnCoef
  intro M hclock hsmall hW1 us hus
  let q:=2*c*M.canonicalDirectTestBandScale
  let A:=M.context.N^(-eta/8)*(M.xs^4/M.canonicalDirectTestBandScale^2)
  have hA : 0<A:=by have :=M.hxs;have :=M.canonical_direct_test_band_pos;dsimp [A];positivity
  have hq0 : 0≤q:=by have :=M.canonical_direct_test_band_pos;dsimp [q];positivity
  by_cases hq1 : q≤1
  swap
  · apply Eventually.of_forall
    intro jGrid
    dsimp only
    intro U hU hqU
    exact False.elim (hq1 (hqU.trans (partitionPoint_mem (finiteCutMasses us jGrid)
      (finiteCutMasses_ordered us hus jGrid) U).2))
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbf:=toNNReal_monotoneOn had.1
  have hhf:=toNNReal_monotoneOn had.2.1
  have Hmesh : Tendsto (fun j : ℕ=>((j+1:ℕ):ℝ)⁻¹*(3*physicalBApproximationConstant n M.bf M.hf+1)) atTop (𝓝 0) := by
    simpa only [zero_mul] using uniformMasses_mesh_tendsto.mul_const (3*physicalBApproximationConstant n M.bf M.hf+1)
  have Hfine:=Hmesh.eventually (eventually_le_nhds (show (0:ℝ)<A/2 by positivity))
  have Horiginal:=hnTail M hclock hsmall hW1 q le_rfl hq1
  have Hc : 2*M.context.N^(-eta/4)≤M.context.N^(-eta/8) := by
    simpa only [NativeOverlapContext.N,mul_one,one_mul,neg_div] using hnCoef
  have Hrate:=mul_le_mul_of_nonneg_right Hc
    (show 0≤M.xs^4/M.canonicalDirectTestBandScale^2 by positivity)
  have Horiginal' : (∫s in q..1,orderedPathB (n+1) M.bf M.hf s-(orderedPathS (n+1) M.bf M.hf s)^2)≤A/2 := by
    dsimp only [A,eta] at Hrate ⊢
    simp only [neg_div] at Hrate Horiginal ⊢
    linarith only [Horiginal,Hrate]
  filter_upwards [Hfine] with jGrid hjGrid
  dsimp only
  intro U hU hqU
  have Hsample:=native_original_high_second_edgeBudget_le_thermal_add_mesh n M.bf M.hf hbf hhf
    (finiteCutMasses_ordered us hus jGrid) (finiteCutMasses_end us hus jGrid)
    (finiteCutMasses_mesh us hus jGrid) ⟨hq0,hq1⟩ U hU hqU
  dsimp only [A,eta] at hjGrid Horiginal'
  simp only [neg_div] at hjGrid Horiginal' ⊢
  linarith only [Hsample,Horiginal',hjGrid]

end OAI.SKFluctuations.LaplaceWindowFormalization
