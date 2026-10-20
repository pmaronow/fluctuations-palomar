module

public import ComparisonSignedCavityActualFourOtherSourceCategories
public import ComparisonSignedCavityActualResourceGammaRestorationReadout
public import ComparisonSignedCavityActualCenteredResourceFreshRestReadout
public import ComparisonSignedCavityActualSmallSourceTaylorDenominator
public import ComparisonSignedCavityActualFourForestNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

def nativeActualGammaRestorationCategory (high : Bool) : NativeActualOtherSourceCategory :=
  if high then .gammaHighRestoration else .gammaLowRestoration

theorem native_actual_four_gamma_restoration_contrast_eq_resources
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (ho : MassOrdered 0 as) (high : Bool) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourOtherCategoryContrast M U st (nativeActualGammaRestorationCategory high)=
      chi*(nativeActualResourceGammaSecondRestoration M U st.term high-
        (1/2:ℝ)*nativeActualResourceGammaSecondRestoration M U (st.term.retarget 0) high) := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C st.tree st.term ho
  dsimp only at Hread
  rw [HQ] at Hread
  dsimp only
  cases high <;>
    simp only [nativeActualGammaRestorationCategory,Bool.false_eq_true,ite_false,ite_true] <;>
    unfold nativeActualOriginalFourOtherCategoryContrast
      nativeActualOriginalOtherSourceCategory nativeActualResourceGammaSecondRestoration
       <;>
    simp only [nativeGammaProjectedSecondRestoration,Bool.false_eq_true,ite_false,ite_true] <;>
    rw [Hread] <;>
    dsimp only [b,h,K,C,q,NativeResourceTerm.retarget,NativeResourceMonomial.retarget,
      NativeGeneratedTest.retarget] <;>
    ring

def nativeActualOriginalFourGammaRestorationError
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (high : Bool) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (1/(chi*K star))*((W⁻¹)^st.generation*
    nativeActualOriginalFourOtherCategoryContrast M U st (nativeActualGammaRestorationCategory high))

theorem actual_minimum_four_gamma_restoration_error_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U ≤ as.length) (high : Bool)
    {W cK B : ℝ} (hW : 0 < W) (hcK : 0 < cK) (hB : 0 ≤ B)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (H0 : |(W⁻¹)^st.generation*nativeActualResourceGammaSecondRestoration M U st.term high| ≤
      |st.term.coefficient| *W*B)
    (H1 : |(W⁻¹)^st.generation*nativeActualResourceGammaSecondRestoration M U (st.term.retarget 0) high| ≤
      |st.term.coefficient| *W*B) :
    |nativeActualOriginalFourGammaRestorationError M U W st high| ≤
      |st.term.coefficient| *(2/(Real.exp (-4*(Temp+2*Cf))*cK))*B := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  obtain ⟨hden,hchi1,hdenlo⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks M
    hCf HS hxs hW hcK ho hs hU hstarK
  have hKpos : 0 < K star:=(mul_pos hcK hW).trans_le hstarK
  have hchi0 : 0 ≤ chi:=by nlinarith
  have hchi : |chi|≤1:=by rw [abs_of_nonneg hchi0];exact hchi1
  have Hdiff : |(W⁻¹)^st.generation*nativeActualResourceGammaSecondRestoration M U st.term high-
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceGammaSecondRestoration M U (st.term.retarget 0) high)| ≤
      2*(|st.term.coefficient| *W*B) := by
    apply (abs_sub _ _).trans
    rw [abs_mul (1/2:ℝ),abs_of_pos (show (0:ℝ)<1/2 by norm_num)]
    nlinarith [show 0≤|st.term.coefficient| *W*B by positivity]
  have Hcat : |(W⁻¹)^st.generation*nativeActualOriginalFourOtherCategoryContrast M U st
      (nativeActualGammaRestorationCategory high)|≤2*(|st.term.coefficient| *W*B) := by
    rw [native_actual_four_gamma_restoration_contrast_eq_resources M U st ho high]
    have HE : (W⁻¹)^st.generation*(chi*(nativeActualResourceGammaSecondRestoration M U st.term high-
        (1/2:ℝ)*nativeActualResourceGammaSecondRestoration M U (st.term.retarget 0) high))=
        chi*((W⁻¹)^st.generation*nativeActualResourceGammaSecondRestoration M U st.term high-
          (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceGammaSecondRestoration M U (st.term.retarget 0) high)) := by ring
    rw [HE,abs_mul]
    exact (mul_le_mul hchi Hdiff (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  unfold nativeActualOriginalFourGammaRestorationError
  dsimp only
  rw [abs_mul,abs_of_pos (div_pos zero_lt_one hden)]
  apply (mul_le_mul_of_nonneg_left Hcat (div_nonneg zero_le_one hden.le)).trans
  have Hfrac : 1/(chi*K star) ≤ 1/(Cd*W):=div_le_div_of_nonneg_left zero_le_one (mul_pos hCd hW) hdenlo
  apply (mul_le_mul_of_nonneg_right Hfrac (by positivity)).trans_eq
  dsimp only [Cd]
  field_simp

theorem actual_gamma_restoration_category_signed_sum_abs_le_error_sum
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U ≤ as.length) {W cK : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) (high : Bool) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast M U Q
      (nativeActualGammaRestorationCategory high))).sum|/(chi*K star) ≤
      (xs.map (fun Q=>|nativeActualOriginalFourGammaRestorationError M U W Q high|)).sum := by
  dsimp only
  obtain ⟨hden,_,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks M hCf HS hxs hW hcK ho hs hU hstarK
  have H:=native_abs_sum_map_le xs (fun Q=>nativeActualOriginalFourGammaRestorationError M U W Q high)
  unfold nativeActualOriginalFourGammaRestorationError at H
  dsimp only at H
  rw [List.sum_map_mul_left,abs_mul,abs_of_pos (div_pos zero_lt_one hden)] at H
  simpa only [nativeActualOriginalFourGammaRestorationError,one_div,one_mul,mul_comm,div_eq_mul_inv] using H

end OAI.SKFluctuations.Cavity
