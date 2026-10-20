module

public import ComparisonSignedCavitySecondLowOccupiedOldCBaselineSource
public import ComparisonSignedCavityActualFreshCentering

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

private theorem centered_source_disorder_sub_mul
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n) as)
    (q : ℕ→RestCoordinate n→ℝ) (P Q : T.Assignment→ℝ) (c : ℝ) :
    T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>P σ-c*Q σ) 0=
      T.disorderExpect (restWeight n) (restFeature n) 0 q P 0-
        c*T.disorderExpect (restWeight n) (restFeature n) 0 q Q 0 := by
  unfold ClockTree.disorderExpect
  simp only [mul_sub,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem native_second_low_joint_ledger_sub_const
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot) (c : ℝ) :
    nativeSecondLowJointLedger n q U b h K T (fun σ=>P σ-c) es=
      nativeSecondLowJointLedger n q U b h K T P es-
        c*nativeSecondLowJointLedger n q U b h K T (fun _=>1) es := by
  have Htest (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
      (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) :
      nativeSecondLowJointRestTest n U b h K (fun σ=>P σ-c) p r s t=
        fun τ=>nativeSecondLowJointRestTest n U b h K P p r s t τ-
          c*nativeSecondLowJointRestTest n U b h K (fun _=>1) p r s t τ := by
    funext τ
    rw [native_second_low_joint_rest_test_product,native_second_low_joint_rest_test_product,
      native_second_low_joint_rest_test_product]
    ring
  unfold nativeSecondLowJointLedger
  rw [←native_second_low_double_average_sub]
  apply native_second_low_double_average_congr
  intro p _ r _
  rw [←native_second_low_double_average_sub]
  apply native_second_low_double_average_congr
  intro s _ t _
  rw [Htest,centered_source_disorder_sub_mul]
  ring

theorem native_second_low_unweighted_c_replacement_sub_const
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (f c z : T.Slot)
    (P : T.cavityLeft.Assignment→ℝ) (a : ℝ) :
    nativeSecondLowUnweightedCReplacementRow n q U b h K T f c z (fun σ=>P σ-a)=
      nativeSecondLowUnweightedCReplacementRow n q U b h K T f c z P-
        a*nativeSecondLowUnweightedCReplacementRow n q U b h K T f c z (fun _=>1) := by
  have Htest (p : MarkedPlacement T) :
      (fun τ=>nativeSecondLowUnweightedCPayload n U b h K T f c z (fun σ=>P σ-a) p τ-
        nativeSecondLowUnweightedCOldPayload n U b h K T f c z (fun σ=>P σ-a) (p.restRestrict τ))=
      fun τ=>(nativeSecondLowUnweightedCPayload n U b h K T f c z P p τ-
        nativeSecondLowUnweightedCOldPayload n U b h K T f c z P (p.restRestrict τ))-
        a*(nativeSecondLowUnweightedCPayload n U b h K T f c z (fun _=>1) p τ-
          nativeSecondLowUnweightedCOldPayload n U b h K T f c z (fun _=>1) (p.restRestrict τ)) := by
    funext τ
    unfold nativeSecondLowUnweightedCPayload nativeSecondLowUnweightedCOldPayload
    ring
  unfold nativeSecondLowUnweightedCReplacementRow
  simp_rw [Htest,centered_source_disorder_sub_mul,mul_sub]
  rw [sum_map_sub_explicit]
  congr 1
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  ring

theorem native_second_low_canonical_c_replacement_sub_const
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a c z : T.Slot) (μ : ℝ) :
    nativeSecondLowCanonicalCReplacementSource n q U b h K T (fun σ=>P σ-μ) a c z=
      nativeSecondLowCanonicalCReplacementSource n q U b h K T P a c z-
        μ*nativeSecondLowCanonicalCReplacementSource n q U b h K T (fun _=>1) a c z := by
  unfold nativeSecondLowCanonicalCReplacementSource
  dsimp only
  simp_rw [native_second_low_unweighted_c_replacement_sub_const,mul_sub]
  rw [sum_map_sub_explicit]
  congr 1
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  ring

theorem native_second_low_fresh_occupied_c_replacement_sub_const
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment→ℝ) (μ : ℝ) :
    nativeSecondLowFreshOccupiedCReplacementSource n q U b h K T s star hU (fun σ=>P σ-μ)=
      nativeSecondLowFreshOccupiedCReplacementSource n q U b h K T s star hU P-
        μ*nativeSecondLowFreshOccupiedCReplacementSource n q U b h K T s star hU (fun _=>1) := by
  unfold nativeSecondLowFreshOccupiedCReplacementSource
  dsimp only
  simp_rw [native_second_low_canonical_c_replacement_sub_const]
  rw [Finset.sum_sub_distrib,Finset.mul_sum]

def nativeSecondLowFreshB0MinusCReplacementSource
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment→ℝ) : ℝ:=
  let g:=nativeFreshAtSlot T 0 s star
  let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  nativeSecondLowJointLedger n q U b h K g.tree (fun σ=>P (g.restRestrict σ)) [g.embed s,g.mark]/2-
    χ^2*nativeSecondLowFreshOccupiedCReplacementSource n q U b h K T s star hU P

theorem native_second_low_fresh_B0_minus_c_replacement_sub_const
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment→ℝ) (μ : ℝ) :
    nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T s star hU (fun σ=>P σ-μ)=
      nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T s star hU P-
        μ*nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T s star hU (fun _=>1) := by
  unfold nativeSecondLowFreshB0MinusCReplacementSource
  dsimp only
  rw [native_second_low_joint_ledger_sub_const,native_second_low_fresh_occupied_c_replacement_sub_const]
  ring

theorem native_second_low_original_centered_fresh_B0_minus_c_replacement
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment→ℝ) :
    nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T s star hU
      (nativeOriginalCenteredRestTest n q U b h K T P)=
      nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T s star hU P-
        nativeOriginalRestTestExpectation n q U b h K T P*
          nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T s star hU (fun _=>1) := by
  exact native_second_low_fresh_B0_minus_c_replacement_sub_const n q U b h K T s star hU P _

end OAI.SKFluctuations.Cavity
