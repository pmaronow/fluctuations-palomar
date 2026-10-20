module

public import ComparisonSignedCavityActualOriginalTargetCommonNet
public import ComparisonSignedCavityActualContinuumTargetResidualModulus
public import ComparisonSignedCavityActualRetainedTargetRadiusLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def ActualInitialFullResidualOnRetainedTargetsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}
    (depth : ℕ) (Atarget Cr : ℝ) (er : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop:=
  ∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
    (∀v∈us,v.val ≤ 1) → (∀v∈uniformMasses Lnet,v∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
  ∀ᶠjGrid in atTop,
    let as:=finiteCutMasses us jGrid
    let star:=retainedMassPrefixIndex (w n).star.val as
    let V:=retainedMassPrefixIndex (high n).val as
    ∀(i : ℕ) (hi : i < star) (hs : star<V) (hV : V ≤ as.length),
      partitionPoint 0 as i ≤ Atarget*(M n).xs →
    let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.le.trans (hs.le.trans hV))
    |nativeActualMinimumFourResidualSum (M n) hs hV (W n) depth [st]| ≤
      Cr*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
        er n*(M n).xs^3

def ActualOriginalTargetScalarGapModulusAlong
    {m delta cl cu Az C0 Ct D Bclock Temp : ℝ} {dim : ℕ→ℕ}
    (hTemp : 0 < Temp) (Atarget C : ℝ) (rate : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (w : ℕ→ActualSlowWindowChoice) : Prop:=
  ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp,
    ∀u : PositiveMass,u.val ≤ Atarget*(M n).xs → u.val < (w n).star.val →
    |orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
      scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
        (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)| ≤
      C*(M n).xs^2*(Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u.val-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u.val)^2)+1/(dim n+1:ℕ))+
        rate n*(M n).xs^3

theorem actual_original_target_gap_from_full_residual_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cf cFirst cK A Rmacro Cx c Atarget Ctgt Cr : ℝ}
    {dim : ℕ→ℕ} (hTemp : 0 < Temp) (depth : ℕ) (Cinner : ℝ)
    (hc : 0 < c) (hCx : 2*c ≤ Cx) (hAtarget : Atarget < 2*c) (hCinner : 2*c ≤ Cinner)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A Rmacro Cx)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (et er : ℕ→ℝ) (Ht : Tendsto et atTop (𝓝 0)) (Hr : Tendsto er atTop (𝓝 0))
    (Htarget : ActualContinuumTargetResidualModulusAlong hTemp depth Cinner A c Ctgt et M W
      (fun n=>(M n).xs) w)
    (Hfull : ActualInitialFullResidualOnRetainedTargetsAlong depth Atarget Cr er M W w high outer) :
    ∃rate : ℕ→ℝ,(∀n,0 ≤ rate n) ∧ Tendsto rate atTop (𝓝 0) ∧
      ActualOriginalTargetScalarGapModulusAlong hTemp Atarget (Ctgt+2*Temp*Cr) rate M w := by
  let rawRate:=fun n=>et n+2*Temp*er n
  let rate:=fun n=>|rawRate n|
  have Hrate : Tendsto rate atTop (𝓝 0):=by
    simpa only [rate,rawRate,mul_zero,add_zero,abs_zero] using (Ht.add (Hr.const_mul (2*Temp))).abs
  refine ⟨rate,fun n=>abs_nonneg _,Hrate,?_⟩
  filter_upwards [Hcuts,Hsource,Htarget,Hfull] with n hcuts hsource htarget hfull
  obtain ⟨htotal,htarget⟩:=htarget
  refine ⟨htotal,?_⟩
  intro u hu hustar
  obtain ⟨Lnet,hLnet⟩:=exists_nat_one_div_lt (M n).hxs
  have hmesh : ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs:=by
    simpa only [Nat.cast_add,Nat.cast_one,one_div] using hLnet.le
  obtain ⟨us,hus,huRet,hiRet,hstar,hhigh,houter,hnodes,hnet,_,Hread⟩:=
    hcuts.exists_original_target_common_net hc hCx hAtarget hu hustar Lnet [] (by simp)
  have Hfixed : ∀ᶠjGrid in atTop,
      |orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
        scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)| ≤
      (Ctgt+2*Temp*Cr)*(M n).xs^2*
        (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid)
          (retainedMassPrefixIndex u.val (finiteCutMasses us jGrid))+1/(dim n+1:ℕ))+
          rate n*(M n).xs^3:=by
    filter_upwards [htarget Lnet us hus hstar hnet hmesh,
      hfull Lnet us hus hnet hmesh hstar hhigh houter hnodes] with jGrid htgrid hrgrid
    dsimp only at htgrid hrgrid ⊢
    let as:=finiteCutMasses us jGrid
    let i:=retainedMassPrefixIndex u.val as
    let star:=retainedMassPrefixIndex (w n).star.val as
    let U:=retainedMassPrefixIndex (2*c*(M n).xs) as
    let V:=retainedMassPrefixIndex (high n).val as
    have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have hread:=Hread jGrid
    have hU : U ≤ as.length:=hread.inner_le_coarse.trans hread.coarse_le_length
    have htgt:=htgrid u huRet U V hread.target_lt_star.le hread.target_lt_inner
      hread.inner_le_coarse hread.star_lt_coarse hread.coarse_le_length
      (by rw [hread.inner_mass])
      (by rw [hread.inner_mass];exact mul_le_mul_of_nonneg_right hCinner (M n).hxs.le)
      hread.coarse_scale
    have hr:=hrgrid i hread.target_lt_star hread.star_lt_coarse hread.coarse_le_length
      (by rw [hread.target_mass];exact hu)
    let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0
      (hread.target_lt_star.le.trans (hread.star_lt_coarse.le.trans hread.coarse_le_length))
    let residual:=nativeActualMinimumFourResidualSum (M n) hread.star_lt_coarse hread.coarse_le_length (W n) depth [st]
    have hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid (M n) as ho U
      ((Nat.zero_le i).trans_lt hread.target_lt_inner) hU
    have hb:((M n).bf u.val:ℝ) ≤ Temp:=(hsource u.val ⟨u.property.le,hus u huRet⟩).1
    have ha : |2*((M n).bf u.val:ℝ)*chi| ≤ 2*Temp:=by
      have HM:=mul_le_mul hb hchi.2 hchi.1 hTemp.le
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) hchi.1)]
      nlinarith only [HM]
    have Hprod : |2*((M n).bf u.val:ℝ)*chi*residual| ≤
        2*Temp*(Cr*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+
          1/(dim n+1:ℕ))+er n*(M n).xs^3):=by
      rw [abs_mul]
      exact mul_le_mul ha hr (abs_nonneg _) (show 0 ≤ 2*Temp by positivity)
    have HH:=(abs_add_le
      (orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
        scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)-2*((M n).bf u.val:ℝ)*chi*residual)
      (2*((M n).bf u.val:ℝ)*chi*residual)).trans
      (add_le_add htgt Hprod)
    have Hraw : |orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
        scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)| ≤
      (Ctgt+2*Temp*Cr)*(M n).xs^2*
        (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
          rawRate n*(M n).xs^3:=by
      have HH' : |orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
          scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)| ≤
          Ctgt*(M n).xs^2*
            (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
            et n*(M n).xs^3+2*Temp*
              (Cr*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+
                1/(dim n+1:ℕ))+er n*(M n).xs^3) := by
        simpa only [sub_add_cancel] using HH
      dsimp only [rawRate]
      nlinarith only [HH']
    apply Hraw.trans
    dsimp only [rate,as,i]
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (le_abs_self (rawRate n))
      (pow_nonneg (M n).hxs.le 3))
  have Hrad:=actual_original_retained_target_low_radius_with_site_tendsto (M n) us hus u huRet
  have Hright:=((Hrad.const_mul ((Ctgt+2*Temp*Cr)*(M n).xs^2)).add_const (rate n*(M n).xs^3))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds Hright Hfixed

end OAI.SKFluctuations.Cavity
