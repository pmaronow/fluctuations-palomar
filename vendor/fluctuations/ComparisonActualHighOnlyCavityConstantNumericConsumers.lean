module

public import ComparisonActualHighOnlyActualConstantSourceRatesOnCutsAlong
public import ComparisonActualHighOnlyActualConstantSourceClosedRatesAlong
public import ComparisonActualHighOnlyCavityCategoryReduction
public import ComparisonActualHighOnlyActualSharpSourceCurrentGaAlong
public import ComparisonActualHighOnlyCavityCategoryInterfaces
public import ComparisonActualHighOnlyLowB0OriginalConstantConsumerSourceAlong
public import ComparisonActualHighOnlyLowB0FullModulusConsumerSourceAlong
public import ComparisonActualHighOnlyLowB0WeightedConsumerSourceAlong
public import ComparisonActualHighOnlyCavityEarlyNumericConsumers
public import ComparisonActualHighOnlyCavityTargetReadoutConsumers
public import ComparisonActualHighOnlyPullbackFourProducers
public import ComparisonActualHighOnlyCavityConsumerPrimitives
public import ComparisonActualHighOnlyComparableBandStarBond
public import ComparisonActualHighOnlySquareConsumerActualSharpFourTerminalAlong
public import ComparisonActualHighOnlyTargetRefinement

@[expose] public section
noncomputable section
set_option autoImplicit false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 26000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {star U : ℕ}

def nativeActualConstantSourceRemainingCategoryEnvelope_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren_high_only M as star U hs hU
  ((List.range depth).map (fun j=>
    (nativeActualOtherSourceCategories.map (fun cat=>
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children) cat|)).sum/
      (Real.exp (-4*Temp)*cK*W))).sum

theorem actual_minimum_constant_source_category_envelope_le_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cKcut cK CK : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcKcut : 0 < cKcut) (hcK : 0 < cK)
    (ho : MassOrdered 0 as) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cKcut*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (hupper : nativeContinuumMixedClock n M.bf M.hf as star ≤ CK*W)
    (depth : ℕ) (BG BR BF : ℕ → ℝ)
    (HG : ∀j < depth,((nativeActualMinimumFourCenteredForest_high_only M hs hU W j
      (nativeActualConstantSourceChildren_high_only M as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourGaCurrentError_high_only M U W Q|)).sum ≤ BG j)
    (HR : ∀j < depth,((nativeActualMinimumFourCenteredForest_high_only M hs hU W j
      (nativeActualConstantSourceChildren_high_only M as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourGaRestorationError_high_only M U W Q|)).sum ≤ BR j)
    (HF : ∀j < depth,((nativeActualMinimumFourCenteredForest_high_only M hs hU W j
      (nativeActualConstantSourceChildren_high_only M as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourFirstHighError_high_only M U W Q|)).sum ≤ BF j) :
    nativeActualConstantSourceErrorEnvelope_high_only M hs hU W Temp cK depth ≤
      ((List.range depth).map (fun j=>(CK/(Real.exp (-4*Temp)*cK))*(BG j+BR j)+BF j)).sum+
        nativeActualConstantSourceRemainingCategoryEnvelope_high_only M hs hU W Temp cK depth := by
  unfold nativeActualConstantSourceErrorEnvelope_high_only nativeActualConstantSourceRemainingCategoryEnvelope_high_only
  dsimp only
  rw [←List.sum_map_add]
  apply List.sum_le_sum
  intro j hj
  have hj':=List.mem_range.mp hj
  exact actual_minimum_four_other_source_closed_categories_abs_le_high_only M htotal hW hcKcut hcK ho
    (Nat.zero_le _) hs hU hstarK hupper _
    (nativeActualFourCenteredForest_valid _ hs (hs.le.trans hU) _ j _
      (fun Q hQ=>nativeActualConstantSourceChildren_valid_high_only M hs hU Q hQ))
    (HG j hj') (HR j hj') (HF j hj')

end OAI.SKFluctuations.Cavity

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
set_option maxHeartbeats 30000000
variable {dim : ℕ → ℕ}

def ActualConstantSourceCategoryEnvelopeAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Temp cK rho C : ℝ)
    (M : (n:ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let star:=retainedMassPrefixIndex (w n).star.val as
    let U:=retainedMassPrefixIndex (high n).val as
    ∃hs : star < U,∃hU : U ≤ as.length,
    nativeActualConstantSourceErrorEnvelope_high_only (M n) hs hU (W n) Temp cK depth ≤
      C*((dim n+1:ℕ):ℝ)^(-rho)*(M n).xs^2+
        nativeActualConstantSourceRemainingCategoryEnvelope_high_only (M n) hs hU (W n) Temp cK depth

theorem actual_constant_source_category_envelope_along_of_closed_rates_high_only
    {m delta eta cl cu Az C0 Ct D Bclock Temp cK cKcut cFirst A CK : ℝ}
    (depth : ℕ) (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta)
    (hcK : 0 < cK) (hcKcut : 0 < cKcut) (hCK : 0 < CK)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (hupper : ∀ᶠn in atTop,actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val ≤ CK*W n)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry_high_only (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cKcut A)
    (Hrates : ∀d : ℕ,∃Cg Cr Cf : ℝ,0 < Cg ∧ 0 < Cr ∧ 0 < Cf ∧
      ActualConstantSourceGaCurrentOnGivenCutsAlong_high_only d eta Cg M W w high outer ∧
      ActualConstantSourceGaRestorationOnGivenCutsAlong_high_only d Cr M W w high outer ∧
      ActualConstantSourceFirstHighOnGivenCutsAlong_high_only d Cf M W w high outer) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceCategoryEnvelopeAlong_high_only depth Temp cK
      (min eta (actualMassSavingExponent m delta/256)) C M W w high outer := by
  choose Cg Cr Cf hCg hCr hCf HG HR HF using Hrates
  let rho:=min eta (actualMassSavingExponent m delta/256)
  have hrho : 0 < rho:=lt_min heta (div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num))
  let L:=CK/(Real.exp (-4*Temp)*cK)
  have hL : 0 ≤ L:=by dsimp only [L];positivity
  let J:=fun d=>L*((1/2:ℝ)^(-rho)*Cg d+Cr d)+Cf d
  have hJ d : 0 ≤ J d:=by
    dsimp only [J]
    exact add_nonneg
      (mul_nonneg hL (add_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hCg d).le) (hCr d).le)) (hCf d).le
  let C:=((List.range depth).map J).sum+1
  have hC : 0 < C:=by
    have H : 0 ≤ ((List.range depth).map J).sum:=List.sum_nonneg (by
      intro x hx;obtain ⟨d,_,rfl⟩:=List.mem_map.mp hx;exact hJ d)
    dsimp only [C];linarith
  have HGN:=Filter.eventually_all.mpr (fun d : Fin depth=>HG d.val)
  have HRN:=Filter.eventually_all.mpr (fun d : Fin depth=>HR d.val)
  have HFN:=Filter.eventually_all.mpr (fun d : Fin depth=>HF d.val)
  refine ⟨C,hC,?_⟩
  filter_upwards [HGN,HRN,HFN,htotal,hupper,Hcuts,hdim.eventually (eventually_ge_atTop 1)]
    with n hnG hnR hnF hnTotal hnUpper hnCuts hn1
  intro Lnet us hus hret hmesh hstar hhigh houter
  have HGgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>hnG d Lnet us hus hret hmesh hstar hhigh houter)
  have HRgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>hnR d Lnet us hus hret hmesh hstar hhigh houter)
  have HFgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>hnF d Lnet us hus hret hmesh hstar hhigh houter)
  filter_upwards [HGgrid,HRgrid,HFgrid] with j hjG hjR hjF
  dsimp only at hjG hjR hjF ⊢
  obtain ⟨Hs,HUV,HV,_,_,_,_,_,_,_,_,HK,_⟩:=hnCuts.finite_net_readout us hus hstar hhigh houter j
  have hU:=HUV.le.trans HV
  refine ⟨Hs,hU,?_⟩
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have HKupper : nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star ≤ CK*W n:=by
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho
      (w n).star (finiteCutMasses_nodes us j hstar)]
    exact hnUpper
  let N:=((dim n+1:ℕ):ℝ)
  let rate:=N^(-rho)*(M n).xs^2
  have hrate : 0 ≤ rate:=by dsimp only [rate,N];positivity
  have hN : 1 ≤ N:=by dsimp only [N];exact_mod_cast (show 1 ≤ dim n+1 by omega)
  have Hpow : N^(-(actualMassSavingExponent m delta/256)) ≤ N^(-rho):=
    Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (min_le_right _ _))
  have HpowG:=actual_source_dimension_power_le hrho.le (min_le_left _ _) (dim n) hn1
  let BG:=fun d=>(1/2:ℝ)^(-rho)*Cg d*rate
  let BR:=fun d=>Cr d*rate
  let BF:=fun d=>Cf d*rate
  have GG d (hd : d < depth) : ((nativeActualMinimumFourCenteredForest_high_only (M n) Hs hU (W n) d
      (nativeActualConstantSourceChildren_high_only (M n) as star U Hs hU)).map
      (fun Q=>|nativeActualOriginalFourGaCurrentError_high_only (M n) U (W n) Q|)).sum ≤ BG d:=by
    obtain ⟨_,_,H⟩:=hjG ⟨d,hd⟩
    apply H.trans
    have HH:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left HpowG (hCg d).le) (sq_nonneg (M n).xs)
    convert HH using 1
    dsimp only [BG,rate,N]
    ring
  have RR d (hd : d < depth) : ((nativeActualMinimumFourCenteredForest_high_only (M n) Hs hU (W n) d
      (nativeActualConstantSourceChildren_high_only (M n) as star U Hs hU)).map
      (fun Q=>|nativeActualOriginalFourGaRestorationError_high_only (M n) U (W n) Q|)).sum ≤ BR d:=by
    obtain ⟨_,_,H⟩:=hjR ⟨d,hd⟩
    apply H.trans
    have HH:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hpow (hCr d).le) (sq_nonneg (M n).xs)
    convert HH using 1
    dsimp only [BR,rate,N]
    ring
  have FF d (hd : d < depth) : ((nativeActualMinimumFourCenteredForest_high_only (M n) Hs hU (W n) d
      (nativeActualConstantSourceChildren_high_only (M n) as star U Hs hU)).map
      (fun Q=>|nativeActualOriginalFourFirstHighError_high_only (M n) U (W n) Q|)).sum ≤ BF d:=by
    obtain ⟨_,_,H⟩:=hjF ⟨d,hd⟩
    apply H.trans
    have HH:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hpow (hCf d).le) (sq_nonneg (M n).xs)
    convert HH using 1
    dsimp only [BF,rate,N]
    ring
  have H:=actual_minimum_constant_source_category_envelope_le_high_only (M n) hnTotal hW hcKcut hcK ho
    Hs hU HK HKupper depth BG BR BF GG RR FF
  apply H.trans
  apply add_le_add _ le_rfl
  change ((List.range depth).map (fun d=>L*(BG d+BR d)+BF d)).sum ≤ C*N^(-rho)*(M n).xs^2
  have HE : ((List.range depth).map (fun d=>L*(BG d+BR d)+BF d)).sum=
      ((List.range depth).map J).sum*rate:=by
    rw [←List.sum_map_mul_right]
    congr 1
    apply List.map_congr_left
    intro d _
    dsimp only [J,BG,BR,BF]
    ring
  rw [HE]
  have HH:=mul_le_mul_of_nonneg_right (show ((List.range depth).map J).sum ≤ C by dsimp only [C];linarith) hrate
  simpa only [rate,mul_assoc] using HH

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem actual_constant_deleted_site_category_family_abs_le_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    {as : List PositiveMass} {star U : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (ho : MassOrdered 0 as) (hs : star < U) (hU : U ≤ as.length)
    (W B : ℝ) (depth : ℕ) (hB : 0 ≤ B)
    (H : ∀Q∈nativeActualConstantSourceChildren_high_only M as star U hs hU,
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W depth [Q]) .deletedSite| ≤
        |Q.term.coefficient| *B) :
    |nativeActualFourOtherCategorySum_high_only M U W
      (nativeActualMinimumFourCenteredForest_high_only M hs hU W depth
        (nativeActualConstantSourceChildren_high_only M as star U hs hU)) .deletedSite| ≤ 6*B := by
  let xs:=nativeActualConstantSourceChildren_high_only M as star U hs hU
  let F:=fun (Q : NativeActualResourceState (Spin n×Bool) as 0 star)=>
    nativeActualFourOtherCategorySum_high_only M U W
      (nativeActualMinimumFourCenteredForest_high_only M hs hU W depth [Q]) .deletedSite
  have HD : nativeActualMinimumFourCenteredForest_high_only M hs hU W depth xs=
      xs.flatMap (fun Q=>nativeActualMinimumFourCenteredForest_high_only M hs hU W depth [Q]):=by
    unfold nativeActualMinimumFourCenteredForest_high_only
    exact nativeActualFourCenteredForest_eq_flatMap_singletons _ _ _ _ _ _
  unfold nativeActualFourOtherCategorySum_high_only
  rw [HD,List.map_flatMap,native_sum_flatMap]
  apply (native_abs_sum_map_le xs F).trans
  apply (List.sum_le_sum H).trans
  rw [List.sum_map_mul_right]
  exact mul_le_mul_of_nonneg_right
    (nativeActualConstantSourceChildren_coefficient_variation_high_only M htotal ho hs hU) hB

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}

theorem actual_constant_source_remaining_envelope_deleted_site_paid_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (hW : 0 < W) (hcK : 0 < cK) (C : ℕ→ℝ)
    (H : ∀j < depth,
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
          (nativeActualConstantSourceChildren_high_only M as star U hs hU)) .deletedSite| ≤
        C j*((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2)) :
    nativeActualConstantSourceRemainingCategoryEnvelope_high_only M hs hU W Temp cK depth ≤
      nativeActualConstantSourcePendingCategoryEnvelope_high_only M hs hU W Temp cK depth+
        (((List.range depth).map C).sum/(Real.exp (-4*Temp)*cK))*
          ((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*M.xs^2 := by
  let children:=nativeActualConstantSourceChildren_high_only M as star U hs hU
  let D:=Real.exp (-4*Temp)*cK*W
  have hD : 0 < D:=by dsimp only [D];positivity
  have HD0 : Real.exp (-4*Temp)*cK≠0:=mul_ne_zero (Real.exp_ne_zero _) hcK.ne'
  have HE : nativeActualConstantSourceRemainingCategoryEnvelope_high_only M hs hU W Temp cK depth=
      nativeActualConstantSourcePendingCategoryEnvelope_high_only M hs hU W Temp cK depth+
        ((List.range depth).map (fun j=>
          |nativeActualFourOtherCategorySum_high_only M U W
            (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children) .deletedSite|/D)).sum:=by
    unfold nativeActualConstantSourceRemainingCategoryEnvelope_high_only nativeActualConstantSourcePendingCategoryEnvelope_high_only
    rw [←List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    rw [native_actual_other_source_categories_split_deleted,List.map_append,List.sum_append]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,add_div]
    rfl
  rw [HE]
  apply add_le_add (le_refl _)
  have Hr j (hj : j∈List.range depth) :
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children) .deletedSite|/D ≤
        (C j/(Real.exp (-4*Temp)*cK))*((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*M.xs^2:=by
    apply (div_le_div_of_nonneg_right (H j (List.mem_range.mp hj)) hD.le).trans_eq
    dsimp only [D]
    field_simp [HD0,hW.ne']
  apply (List.sum_le_sum Hr).trans_eq
  simp only [div_eq_mul_inv,List.sum_map_mul_right]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
variable {dim : ℕ→ℕ}

def ActualConstantSourcePendingCategoryEnvelopeAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Temp cK C : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star < U,∃hU : U ≤ as.length,
      nativeActualConstantSourceRemainingCategoryEnvelope_high_only (M n) hs hU (W n) Temp cK depth ≤
        C*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2+
          nativeActualConstantSourcePendingCategoryEnvelope_high_only (M n) hs hU (W n) Temp cK depth

theorem actual_constant_pending_category_envelope_along_of_deleted_rates_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp cK cFirst cKcut A : ℝ}
    (depth : ℕ) (hcK : 0 < cK)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hW : ∀n,0 < W n)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry_high_only (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cKcut A)
    (Hrates : ∀d : ℕ,∃C : ℝ,0 < C ∧ ActualConstantSourceDeletedSiteOnGivenCutsAlong_high_only d C M W w high outer) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourcePendingCategoryEnvelopeAlong_high_only depth Temp cK C M W w high outer := by
  choose C hC HC using Hrates
  let J:=((List.range depth).map C).sum
  have hJ : 0 ≤ J:=List.sum_nonneg (by
    intro z hz;obtain ⟨j,_,rfl⟩:=List.mem_map.mp hz;exact (hC j).le)
  let Aout:=J/(Real.exp (-4*Temp)*cK)+1
  have hAout : 0 < Aout:=by dsimp only [Aout];positivity
  have HG:=Filter.eventually_all.mpr (fun j : Fin depth=>HC j.val)
  refine ⟨Aout,hAout,?_⟩
  filter_upwards [HG,Hcuts] with n hn hcuts
  intro L us hus hret hmesh hstar hhigh houter
  have Hnet:=Filter.eventually_all.mpr (fun j : Fin depth=>hn j L us hus hret hmesh hstar hhigh houter)
  filter_upwards [Hnet] with jGrid hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,_,_,_,_,_,_,_,_,_,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  refine ⟨Hs,hU,?_⟩
  have Hr j (hjd : j < depth) := hj ⟨j,hjd⟩
  have H:=actual_constant_source_remaining_envelope_deleted_site_paid_high_only (M n) Hs hU (W n) Temp cK depth
    (hW n) hcK C (by intro j hjd;obtain ⟨_,_,Hj⟩:=Hr j hjd;exact Hj)
  have Hcoef : J/(Real.exp (-4*Temp)*cK) ≤ Aout:=by dsimp only [Aout];linarith
  have Hrate:=mul_le_mul_of_nonneg_right Hcoef
    (show 0 ≤ ((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2 by positivity)
  apply H.trans
  have H':=add_le_add_left Hrate
    (nativeActualConstantSourcePendingCategoryEnvelope_high_only (M n) Hs hU (W n) Temp cK depth)
  calc
    _=J/(Real.exp (-4*Temp)*cK)*(((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2)+
        nativeActualConstantSourcePendingCategoryEnvelope_high_only (M n) Hs hU (W n) Temp cK depth:=by
      dsimp only [J];ring
    _≤Aout*(((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2)+
        nativeActualConstantSourcePendingCategoryEnvelope_high_only (M n) Hs hU (W n) Temp cK depth:=H'
    _=_:=by ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 6000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}

theorem actual_constant_source_post_Taylor_envelope_longitudinal_paid_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (err : ℕ→ℝ)
    (H : ∀j < depth,∀right : Bool,
      |nativeActualFourOtherCategorySum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
          (nativeActualConstantSourceChildren_high_only M as star U hs hU)) (nativeActualLongitudinalCategory right)|/
        (Real.exp (-4*Temp)*cK*W) ≤ err j*M.xs^2) :
    nativeActualConstantSourcePostTaylorCategoryEnvelope_high_only M hs hU W Temp cK depth ≤
      nativeActualConstantSourcePostLongitudinalCategoryEnvelope_high_only M hs hU W Temp cK depth+
        2*((List.range depth).map err).sum*M.xs^2 := by
  have HE : nativeActualConstantSourcePostTaylorCategoryEnvelope_high_only M hs hU W Temp cK depth=
      nativeActualConstantSourcePostLongitudinalCategoryEnvelope_high_only M hs hU W Temp cK depth+
        ((List.range depth).map (fun j=>
          (|nativeActualFourOtherCategorySum_high_only M U W
            (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
              (nativeActualConstantSourceChildren_high_only M as star U hs hU)) .longitudinalLeft|+
           |nativeActualFourOtherCategorySum_high_only M U W
            (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
              (nativeActualConstantSourceChildren_high_only M as star U hs hU)) .longitudinalRight|)/
            (Real.exp (-4*Temp)*cK*W))).sum := by
    unfold nativeActualConstantSourcePostTaylorCategoryEnvelope_high_only nativeActualConstantSourcePostLongitudinalCategoryEnvelope_high_only
    rw [←List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    rw [(native_actual_post_Taylor_categories_perm_longitudinal.map _).sum_eq]
    simp only [List.map_cons,List.sum_cons,add_div]
    ring
  rw [HE]
  apply add_le_add le_rfl
  have Hrow j (hj : j∈List.range depth) := add_le_add (H j (List.mem_range.mp hj) false)
    (H j (List.mem_range.mp hj) true)
  simp only [nativeActualLongitudinalCategory,Bool.false_eq_true,ite_false,ite_true] at Hrow
  have Hsum:=List.sum_le_sum Hrow
  simp only [List.sum_map_add,List.sum_map_mul_right] at Hsum
  simp only [add_div,List.sum_map_add]
  exact Hsum.trans_eq (by ring)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualConstantSourcePostLongitudinalEnvelopeAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Temp cK : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star < U,∃hU : U ≤ as.length,
      nativeActualConstantSourcePostTaylorCategoryEnvelope_high_only (M n) hs hU (W n) Temp cK depth ≤
        nativeActualConstantSourcePostLongitudinalCategoryEnvelope_high_only (M n) hs hU (W n) Temp cK depth+
          err n*(M n).xs^2

end OAI.SKFluctuations.Cavity

