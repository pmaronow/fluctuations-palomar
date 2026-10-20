module

public import ComparisonSignedCavityActualFourGBranches
public import ComparisonSignedCavityActualInheritedContinuumGWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 10000000

theorem nativeOriginalClockParentWeight_four_beta_abs_le
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} (W : ℝ) (U : ℕ) (K b : ℕ→ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (C : ℝ)
    (H : ∀tag,|nativeOriginalClockParentWeight W U K st
      (nativeOriginalClockGBranchBeta U K b st tag)|≤C) (tag : ℕ) :
    |nativeOriginalClockParentWeight W U K st
      (nativeOriginalClockFourGBranchBeta U K b st tag)|≤C := by
  unfold nativeOriginalClockFourGBranchBeta
  split_ifs
  · simpa only [nativeOriginalClockParentWeight,neg_div,mul_neg,abs_neg] using H tag
  · have he : nativeOriginalClockParentWeight W U K st
        (nativeOriginalClockGBranchBeta U K b st (tag-2)/2)=
        nativeOriginalClockParentWeight W U K st
          (nativeOriginalClockGBranchBeta U K b st (tag-2))/2 := by
      unfold nativeOriginalClockParentWeight
      ring
    rw [he,abs_div]
    rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [H (tag-2),abs_nonneg (nativeOriginalClockParentWeight W U K st
      (nativeOriginalClockGBranchBeta U K b st (tag-2)))]

theorem nativeOriginalClockFourGBranchBeta_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U≤as.length) (K : ℕ→ℝ)
    (hK : ∀j,0≤K j) (hKm : Monotone K)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) :
    |nativeOriginalClockFourGBranchBeta U K (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) st tag|≤Temp := by
  have H:=fun tag=>nativeOriginalClockGBranchBeta_bound M htotal ho hs hU K hK hKm st tag
  unfold nativeOriginalClockFourGBranchBeta
  split_ifs
  · simpa only [abs_neg] using H tag
  · rw [abs_div]
    rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [H (tag-2),abs_nonneg (nativeOriginalClockGBranchBeta U K
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) st (tag-2))]

theorem actual_continuum_four_G_weight_bound_of_total_clock
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp W cK : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (hW : 0<W) (hcK : 0<cK)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {i star U : ℕ} (hs : star<U) (hU : U≤as.length)
    (hstarK : cK*W≤nativeContinuumMixedClock n M.bf M.hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockFourGBranchBeta U K b st tag)|≤
      Temp/(Real.exp (-4*Temp)*cK) := by
  apply nativeOriginalClockParentWeight_four_beta_abs_le
  intro j
  exact actual_continuum_G_weight_bound_of_total_clock M htotal hW hcK as ho hs hU hstarK st j

theorem actual_retained_continuum_four_G_weight_bound_of_total_clock
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp W cK : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (hW : 0<W) (hcK : 0<cK)
    (u : PositiveMass) (hclock : cK*W≤actualMixedClock (n+1) M.bf M.hf u.val)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hu : u∈as)
    {i U : ℕ} (hs : retainedMassPrefixIndex u.val as<U) (hU : U≤as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i (retainedMassPrefixIndex u.val as))
    (tag : ℕ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockFourGBranchBeta U K b st tag)|≤
      Temp/(Real.exp (-4*Temp)*cK) := by
  apply nativeOriginalClockParentWeight_four_beta_abs_le
  intro j
  exact actual_retained_continuum_G_weight_bound_of_total_clock M htotal hW hcK u hclock as ho hu hs hU st j

theorem actual_calibrated_continuum_four_G_weight_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp L Cs W : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0<cu) (hAz : 0≤Az) (hTemp : 0<Temp) (hW : 0<W)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0)
    (w : ActualSlowWindowChoice) (Hw : IsActualCalibratedSlowWindow M W Temp L Cs w)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hstar : w.star∈as)
    (i U : ℕ) (hs : retainedMassPrefixIndex w.star.val as<U) (hU : U≤as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i (retainedMassPrefixIndex w.star.val as))
    (tag : ℕ) :
    let c:=starMassBandConstant cu Az/cu
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockFourGBranchBeta U K b st tag)|≤
      Temp/(Real.exp (-4*Temp)*(3*Temp*c/8)) := by
  apply nativeOriginalClockParentWeight_four_beta_abs_le
  intro j
  exact actual_calibrated_continuum_G_weight_bound M hcu hAz hTemp hW hb hh w Hw as ho hstar i U hs hU st j

end OAI.SKFluctuations.Cavity
