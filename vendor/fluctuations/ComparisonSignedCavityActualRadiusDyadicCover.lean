module

public import ComparisonSignedCavityActualGammaRowInterval
public import ComparisonSignedCavityActualBufferDyadicCount
public import ComparisonNativeDyadicContactCover

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity

theorem native_radius_dyadic_card_le {N V : ℝ}
    (hN : 1 < N) (hlog : 1 ≤ Real.log N) (hV : 0 < V) (hV1 : V ≤ 1)
    (hlower : N^(-(2:ℝ)) ≤ V) :
    ((comparisonMassDyadicIndices V).card:ℝ) ≤ (2/Real.log 2+2)*Real.log N := by
  have hlog2 : 0 < Real.log 2:=Real.log_pos (by norm_num)
  have hq : 0 ≤ Real.log (1/V)/Real.log 2:=div_nonneg
    (Real.log_nonneg ((one_le_div hV).mpr hV1)) hlog2.le
  have Hcard : (comparisonMassDyadicIndices V).card ≤
      Nat.ceil (Real.log (1/V)/Real.log 2)+1 := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have Hcast : ((comparisonMassDyadicIndices V).card:ℝ) ≤
      (Nat.ceil (Real.log (1/V)/Real.log 2):ℝ)+1 := by exact_mod_cast Hcard
  have Hceil:=Nat.ceil_lt_add_one hq
  have Hlog:=Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans hN) _) hlower
  rw [Real.log_rpow (zero_lt_one.trans hN)] at Hlog
  have Hq : Real.log (1/V)/Real.log 2 ≤ 2/Real.log 2*Real.log N := by
    rw [one_div,Real.log_inv]
    apply (div_le_iff₀ hlog2).mpr
    field_simp
    nlinarith only [Hlog]
  nlinarith only [Hcast,Hceil,Hq,hlog]

theorem native_original_radius_dyadic_cover
    {R : ℝ → ℝ} {as : List PositiveMass} {V : ℝ} (hV : 0 < V)
    (cut : ℕ) (hlo : V ≤ R (partitionPoint 0 as cut))
    (hhi : R (partitionPoint 0 as cut) ≤ 1) :
    ∃j : comparisonMassDyadicIndices V,
      nativeRadiusRowBand R as (V*(2:ℝ)^(j:ℕ)) cut=1 := by
  obtain ⟨j,hj,hj'⟩:=comparison_mass_dyadic_cover hV hlo hhi
  exact ⟨j,ite_eq_left ⟨hj,hj'.le⟩⟩

theorem eventually_actual_minimum_radius_dyadic_cover
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀V : ℝ,M.xs ≤ V → V ≤ 1 →
        ((comparisonMassDyadicIndices V).card:ℝ) ≤
          (2/Real.log 2+2)*Real.log ((n+1:ℕ):ℝ) ∧
        ∀(as : List PositiveMass) (cut : ℕ),V ≤ M.R (partitionPoint 0 as cut) →
          ∃j : comparisonMassDyadicIndices V,
            nativeRadiusRowBand M.R as (V*(2:ℝ)^(j:ℕ)) cut=1 := by
  have Hlower:=NativeOverlapMinimum.eventually_actual_minimum_scale_polynomial_lower
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  have Hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((n+1:ℕ):ℝ) :=
    (tendsto_add_atTop_nat 1).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  filter_upwards [Hlower,Hlog,eventually_gt_atTop (0:ℕ)] with n hn hlog hn0
  intro M V hxV hV1
  have hV:=M.hxs.trans_le hxV
  refine ⟨native_radius_dyadic_card_le (by exact_mod_cast (show 1 < n+1 by omega))
    hlog hV hV1 ((hn M).trans hxV),?_⟩
  intro as cut hlo
  exact native_original_radius_dyadic_cover hV cut hlo
    (comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha (partitionPoint 0 as cut)).2

end OAI.SKFluctuations.LaplaceWindowFormalization
