module

public import ComparisonSignedCavityActualConstantFreshLowTaylorRateAlong
public import ComparisonSignedCavityActualConstantResourceFreshLowTaylorRateAlong
public import ComparisonSignedCavityActualConstantResourceGammaLowRateAlong
public import ComparisonSignedCavityActualInitialResourceGammaLowRateAlong
public import ComparisonSignedCavityActualConstantResourceFreshJointLowRestorationRateAlong
public import ComparisonSignedCavityActualConstantChildGammaLowRateAlong
public import ComparisonSignedCavityActualInitialGammaLowRateAlong
public import ComparisonSignedCavityActualConstantChildJointLowRestorationRateAlong
public import ComparisonSignedCavityActualConstantChildJointLowRestorationCategoryAlong
public import ComparisonSignedCavityInitialInheritedThirdLowSavingAlong
public import ComparisonSignedCavityInitialInheritedResourceThirdLowSavingAlong
public import ComparisonSignedCavityInitialInheritedCenteredResourceThirdLowSavingAlong
public import ComparisonSignedCavityInitialInheritedFreshResourceThirdLowSavingAlong
public import ComparisonActualHighOnlyLowPhysicalSourceAlong
public import ComparisonActualHighOnlyInitialLowModulusSourceAlong
public import ComparisonActualHighOnlyLowDensitySourceAlong
public import ComparisonActualHighOnlyLowSharpRadiusCompatibleSourceAlong
public import ComparisonActualHighOnlyPullbackFourInterfaces

@[expose] public section
noncomputable section
set_option maxHeartbeats 60000000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
open NativeOverlapMinimum (ActualSlowWindowChoice)

theorem actual_inherited_constant_fresh_third_LOW_rate_along_high_only
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0 < Ccut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) (hCs : 0≤Cs)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠ n : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠ n : ℕ in atTop,(M n).xs^2≤Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠ n : ℕ in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs → (w n).star ∈ us →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀U : ℕ,star < U → U≤as.length → partitionPoint 0 as U≤ min (Ccut*W n) 1 →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) seedMass (singleSlot as) star
          ∀(a z : g.tree.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
            |nativeActualCenteredThirdLowPart (dim n) q U b h K g.tree (fun _=>1) a z l t|≤
              err n*(W n*(M n).xs^2) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_constant_centered_third_LOW_profile_high_only
    (D:=D) 2 Bclock Temp Cf Ccut hTemp hCf hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let eta:=actualMassSavingExponent m delta
  let amp:=fun n=>actualMinimumInheritedLowErrorDensityAmplitude_high_only (M n) Temp Cf Ccut
  let err:=fun n=>C*(((dim n+1:ℕ):ℝ)^(-eta/32)+W n*amp n)
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along_high_only hm hdelta hC0 Cerr
    (actualLowErrorComparisonConstant_nonneg _ hTemp) dim hdim M W hcanonical hWlim w hw
  have Hamp : Tendsto amp atTop (𝓝 0):=by
    apply actualMinimumInheritedLowErrorDensityAmplitude_regular_tendsto_zero_along_high_only
      hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M hsmall _ Hclock Homit Hcutoff Ccut hCcut
    simpa only [←hcanonical] using hWlim
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/32 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    have H:=(Hpow.add (hWlim.mul Hamp)).const_mul C
    simpa only [err,Function.comp_def,zero_mul,add_zero,mul_zero,neg_div] using H
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HC,HR,Hsource,HW1,Hcutoff] with n hnC hnR hsource hW1 hnCutoff
  have hxW : (M n).xs≤W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hx1:=hxW.trans hW1
  intro L us hus hret hmesh hstar
  filter_upwards [hnC (M n) hnCutoff.1 hnCutoff.2 hsource hx1 L us hus hret hmesh,hnR us hus hstar,
    actual_minimum_inherited_current_low_error_saved_density_on_every_final_net_high_only (M n)
      Temp Cf Ccut hTemp hCf hCcut hsource hx1 us hus] with jGrid hgridC hgridR hgridD
  dsimp only at hgridC hgridR hgridD ⊢
  intro U hs hU hcut seedMass a z l t hl ht
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) seedMass (singleSlot as) star
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeWholeLawErrorRadius (dim n) as (cutFullVariance (dim n) q U l t b h K) (cutLowError (dim n) U b h K)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves≤2:=by
    have H:=(single (S:=Spin (dim n)×Bool) as).markedAttach_leaves seedMass _
      (nativeFreshAtSlot_mem (single as) seedMass (singleSlot as) star)
    simpa only [g,single_leaves_exact] using H
  have HF : g.tree.forkCost R=R star:=by
    rw [nativeFreshAtSlot_forkCost,single_forkCost,zero_add,Nat.min_eq_left (hs.le.trans hU)]
  have Hrad : R star≤((dim n+1:ℕ):ℝ)^(-eta/32)*((M n).xs^2/W n):=by
    have H:=actual_minimum_inherited_current_low_error_radius_le_original_high_only (M n) Temp Cf hTemp hCf
      hsource hx1 ho U hl ht star (hs.le.trans hU)
    change R star≤ if star<U then Cerr*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as star+1/(dim n+1:ℕ)) else 0 at H
    have hs' : star<U:=hs
    rw [ite_eq_left hs'] at H
    exact H.trans (by simpa only [eta,neg_div] using hgridR)
  have HD : edgeBudget 0 as R≤amp n*(M n).xs^2:=by
    apply hgridD U hU
    · simpa only [hcanonical] using hcut
    · exact hl
    · exact ht
  have H:=hgridC U g.tree (W n) l t hU hg hxW hW1
    (hcut.trans (min_le_left _ _)) hl ht a z
  rw [HF] at H
  have HCW : 0≤C*(W n)^2:=mul_nonneg hC.le (sq_nonneg _)
  have Hsum:=mul_le_mul_of_nonneg_left (add_le_add Hrad HD) HCW
  apply H.trans (Hsum.trans_eq _)
  dsimp only [err,eta,amp]
  have hW : W n≠0:=((M n).hxs.trans_le hxW).ne'
  field_simp

theorem actual_inherited_constant_resource_fresh_third_LOW_rate_along_high_only
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠ n : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠ n : ℕ in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠ n : ℕ in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star ∈ us →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀U : ℕ,star < U → U ≤ as.length → partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        ∀(i k : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U [] k T P → i ≤ star →
          T.leaves ≤ rBound → k ≤ degree →
          partitionPoint 0 as i ≤ Cmass*(M n).xs → partitionPoint 0 as star ≤ Cmass*W n →
          ∀(l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
            |((W n)⁻¹)^k*nativeActualOriginalFreshResourceThirdLowPart_high_only (M n) U P l t| ≤
              |P.coefficient| *err n*(W n*(M n).xs^2) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_centered_resource_third_LOW_from_minimum_high_only
    (D:=D) degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let eta:=actualMassSavingExponent m delta
  let amp:=fun n=>actualMinimumInheritedLowErrorDensityAmplitude_high_only (M n) Temp Cf Ccut
  let err:=fun n=>C*((rBound:ℝ)*((dim n+1:ℕ):ℝ)^(-eta/32)+W n*amp n)
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along_high_only hm hdelta hC0 Cerr
    (actualLowErrorComparisonConstant_nonneg _ hTemp) dim hdim M W hcanonical hWlim w hw
  have Hamp : Tendsto amp atTop (𝓝 0):=by
    apply actualMinimumInheritedLowErrorDensityAmplitude_regular_tendsto_zero_along_high_only
      hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M hsmall _ Hclock Homit Hcutoff Ccut hCcut
    simpa only [←hcanonical] using hWlim
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/32 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    have H:=((Hpow.const_mul (rBound:ℝ)).add (hWlim.mul Hamp)).const_mul C
    simpa only [err,Function.comp_def,zero_mul,add_zero,mul_zero,neg_div] using H
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HC,HR,Hsource,HW1,Hcutoff] with n hnC hnR hsource hW1 hnCutoff
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hx1:=hxW.trans hW1
  intro L us hus hret hmesh hstar
  filter_upwards [hnC (M n) hnCutoff.1 hnCutoff.2 hsource hx1 L us hus hret hmesh,hnR us hus hstar,
    actual_minimum_inherited_current_low_error_saved_density_on_every_final_net_high_only (M n)
      Temp Cf Ccut hTemp hCf hCcut hsource hx1 us hus] with jGrid hgridC hgridR hgridD
  dsimp only at hgridC hgridR hgridD ⊢
  intro U hs hU hcut i k T P hP hi hT hdepth hmi hms l t hl ht
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeWholeLawErrorRadius (dim n) as (cutFullVariance (dim n) q U l t b h K) (cutLowError (dim n) U b h K)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have hR j : 0 ≤ R j:=nativeWholeLawErrorRadius_nonneg _ _ _ _ _
  have HF : g.tree.forkCost R ≤ (rBound:ℝ)*R star:=by
    have H:=hP.retarget.constant_low_forkCost_le hs R hR
      (fun j hj=>native_low_error_radius_above_cut_zero (dim n) U b h K as _ j hj)
    have Hcast : (g.tree.leaves:ℝ)-1 ≤ rBound:=by
      have Hcast' : (g.tree.leaves:ℝ) ≤ (rBound:ℝ)+1:=by exact_mod_cast hg
      linarith
    exact H.trans (mul_le_mul_of_nonneg_right Hcast (hR star))
  have Hrad : R star ≤ ((dim n+1:ℕ):ℝ)^(-eta/32)*((M n).xs^2/W n):=by
    have H:=actual_minimum_inherited_current_low_error_radius_le_original_high_only (M n) Temp Cf hTemp hCf
      hsource hx1 ho U hl ht star (hs.le.trans hU)
    change R star ≤ if star<U then Cerr*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as star+1/(dim n+1:ℕ)) else 0 at H
    have hs' : star<U:=hs
    rw [ite_eq_left hs'] at H
    exact H.trans (by simpa only [eta,neg_div] using hgridR)
  have HD : edgeBudget 0 as R ≤ amp n*(M n).xs^2:=by
    apply hgridD U hU
    · simpa only [hcanonical] using hcut
    · exact hl
    · exact ht
  have H:=hgridC i star U k [] g.tree (P.retarget 0) hP.retarget hi hs hU hg (by simpa using hdepth)
    (W n) hxW hW1 hmi hms (hcut.trans (min_le_left _ _)) (g.embed P.live.test.target) g.mark l t hl ht
  change |((W n)⁻¹)^k*nativeActualOriginalCenteredResourceThirdLowPart_high_only (M n) U (P.retarget 0)
      (g.embed P.live.test.target) g.mark l t| ≤ |P.coefficient| *
        nativeResourceScale (M n).xs (W n) 1 []*(C*(W n)^2*(g.tree.forkCost R+edgeBudget 0 as R)) at H
  simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at H
  rw [native_actual_original_fresh_resource_third_LOW_eq_centered_retarget_high_only (M n) U P ho]
  have HF' := HF.trans (mul_le_mul_of_nonneg_left Hrad (Nat.cast_nonneg rBound))
  have Hsum:=mul_le_mul_of_nonneg_left (add_le_add HF' HD)
    (show 0 ≤ |P.coefficient| *C*(W n)^2 by positivity)
  have hW : W n≠0:=((M n).hxs.trans_le hxW).ne'
  apply H.trans
  convert Hsum using 1 <;> (try dsimp only [err,eta,amp]) <;> field_simp [hW]

theorem actual_inherited_constant_resource_gamma_LOW_restoration_rate_along_high_only
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠ n : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠ n : ℕ in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star ∈ us →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀U : ℕ,star < U → U ≤ as.length → partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        ∀(i k : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U [] k T P → i ≤ star →
          T.leaves ≤ rBound → k ≤ degree →
          partitionPoint 0 as i ≤ Cmass*(M n).xs → partitionPoint 0 as star ≤ Cmass*W n →
          |((W n)⁻¹)^k*nativeActualResourceGammaSecondRestoration_high_only (M n) U P false| ≤
              |P.coefficient| *err n*(W n*(M n).xs^2) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_resource_gamma_LOW_restoration_from_minimum_high_only
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut.le
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let eta:=actualMassSavingExponent m delta
  let err:=fun n=>C*((dim n+1:ℕ):ℝ)^(-eta/32)
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along_high_only hm hdelta hC0 Cerr
    (actualLowErrorComparisonConstant_nonneg _ hTemp) dim hdim M W hcanonical hWlim w hw
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/32 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,Function.comp_def,mul_zero,neg_div] using Hpow.const_mul C
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HC,HR,Hsource,HW1,Hcutoff] with n hnC hnR hsource hW1 hnCutoff
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hx1:=hxW.trans hW1
  intro L us hus hret hmesh hstar
  filter_upwards [hnC (M n) hnCutoff.1 hnCutoff.2 hsource hx1 L us hus hret hmesh,hnR us hus hstar] with jGrid hgridC hgridR
  dsimp only at hgridC hgridR ⊢
  intro U hs hU hcut i k T P hP hi hT hdepth hmi hms
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  have H:=hgridC i star U k [] T P hP hi hs hU hT (by simpa using hdepth)
    (M n).xs (W n) le_rfl hxW hW1 hmi hms (hcut.trans (min_le_left _ _))
  simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at H
  have HD:=mul_le_mul_of_nonneg_left hgridR
    (show 0 ≤ |P.coefficient| *C*(W n)^2 by positivity)
  have hW : W n≠0:=((M n).hxs.trans_le hxW).ne'
  apply H.trans
  convert HD using 1 <;> (try dsimp only [err,eta,Cerr,star,as]) <;> field_simp [hW]

theorem actual_inherited_initial_resource_gamma_LOW_restoration_rate_along_high_only
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠ n : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (x : ℕ→ℝ) (hxsx : ∀ᶠn in atTop,(M n).xs ≤ x n)
    (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠ n : ℕ in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star ∈ us →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀U : ℕ,star < U → U ≤ as.length → partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        ∀(i k : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U [.initial] k T P → i ≤ star →
          T.leaves ≤ rBound → 1+k ≤ degree →
          partitionPoint 0 as i ≤ Cmass*x n → partitionPoint 0 as star ≤ Cmass*W n →
          |((W n)⁻¹)^k*nativeActualResourceGammaSecondRestoration_high_only (M n) U P false| ≤
              |P.coefficient| *err n*(W n*(M n).xs^2*x n) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_resource_gamma_LOW_restoration_from_minimum_high_only
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut.le
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let eta:=actualMassSavingExponent m delta
  let err:=fun n=>C*((dim n+1:ℕ):ℝ)^(-eta/32)
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along_high_only hm hdelta hC0 Cerr
    (actualLowErrorComparisonConstant_nonneg _ hTemp) dim hdim M W hcanonical hWlim w hw
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/32 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,Function.comp_def,mul_zero,neg_div] using Hpow.const_mul C
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HC,HR,Hsource,HW1,hxsx,hxW,Hcutoff] with n hnC hnR hsource hW1 hxsxn hxWn hnCutoff
  have hx1:=hxsxn.trans (hxWn.trans hW1)
  have hx : 0 < x n:=(M n).hxs.trans_le hxsxn
  intro L us hus hret hmesh hstar
  filter_upwards [hnC (M n) hnCutoff.1 hnCutoff.2 hsource hx1 L us hus hret hmesh,hnR us hus hstar] with jGrid hgridC hgridR
  dsimp only at hgridC hgridR ⊢
  intro U hs hU hcut i k T P hP hi hT hdepth hmi hms
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  have H:=hgridC i star U k [.initial] T P hP hi hs hU hT (by simpa using hdepth)
    (x n) (W n) hxsxn hxWn hW1 hmi hms (hcut.trans (min_le_left _ _))
  simp only [nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    NativeResourceMark.savedScale,mul_one] at H
  have HD:=mul_le_mul_of_nonneg_left hgridR
    (show 0 ≤ |P.coefficient| *C*x n*(W n)^2 by positivity)
  have hW : W n≠0:=(hx.trans_le hxWn).ne'
  apply H.trans
  convert HD using 1 <;> (try dsimp only [err,eta,Cerr,star,as]) <;> field_simp [hW]

theorem actual_inherited_constant_resource_fresh_joint_LOW_restoration_rate_along_high_only
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠ n : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠ n : ℕ in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star ∈ us →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀U : ℕ,star < U → U ≤ as.length → partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        ∀(i k : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U [] k T P → i ≤ star →
          T.leaves ≤ rBound → k ≤ degree →
          partitionPoint 0 as i ≤ Cmass*(M n).xs → partitionPoint 0 as star ≤ Cmass*W n →
          |((W n)⁻¹)^k*nativeActualOriginalFreshResourceJointLowRestoration_high_only (M n) U P| ≤
              |P.coefficient| *err n*(W n*(M n).xs^2) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_centered_resource_joint_LOW_restoration_from_minimum_high_only
    (D:=D) degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut.le
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let eta:=actualMassSavingExponent m delta
  let err:=fun n=>C*((dim n+1:ℕ):ℝ)^(-eta/32)
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along_high_only hm hdelta hC0 Cerr
    (actualLowErrorComparisonConstant_nonneg _ hTemp) dim hdim M W hcanonical hWlim w hw
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/32 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,Function.comp_def,mul_zero,neg_div] using Hpow.const_mul C
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HC,HR,Hsource,HW1,Hcutoff] with n hnC hnR hsource hW1 hnCutoff
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hx1:=hxW.trans hW1
  intro L us hus hret hmesh hstar
  filter_upwards [hnC (M n) hnCutoff.1 hnCutoff.2 hsource hx1 L us hus hret hmesh,hnR us hus hstar] with jGrid hgridC hgridR
  dsimp only at hgridC hgridR ⊢
  intro U hs hU hcut i k T P hP hi hT hdepth hmi hms
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have Hsplit : g.tree.splitIndex (g.embed P.live.test.target) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,
      min_eq_left (hs.le.trans hU)]
  have H:=hgridC i star U k [] g.tree (P.retarget 0) hP.retarget hi hs hU hg (by simpa using hdepth)
    (W n) hxW hW1 hmi hms (hcut.trans (min_le_left _ _)) (g.embed P.live.test.target) g.mark
    (by rw [Hsplit];exact hs)
  rw [Hsplit] at H
  simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one,NativeResourceTerm.retarget] at H
  rw [native_actual_original_fresh_resource_joint_LOW_restoration_eq_centered_retarget_high_only (M n) U P ho]
  have HD:=mul_le_mul_of_nonneg_left hgridR
    (show 0 ≤ |P.coefficient| *C*(W n)^2 by positivity)
  have hW : W n≠0:=((M n).hxs.trans_le hxW).ne'
  apply H.trans
  convert HD using 1 <;> (try dsimp only [err,eta,Cerr,star,as]) <;> field_simp [hW]

theorem actual_inherited_constant_child_gamma_LOW_restoration_forest_rate_along_high_only
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(U : ℕ) (hs : star<U) (hU : U ≤ as.length),
        partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_high_only (M n) as star U hs hU)).map
          (fun Q=>|nativeActualOriginalFourGammaRestorationError_high_only (M n) U (W n) Q false|)).sum ≤
            err n*(M n).xs^2 := by
  let degree:=1+depth
  let rBound:=3+6*depth
  obtain ⟨eLow,heLow,HLow⟩:=actual_inherited_constant_resource_gamma_LOW_restoration_rate_along_high_only
    degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource Hcutoff w hw
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 3 depth
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVv : 0 ≤ Vv:=nativeActualWeightedFrontierCost_nonneg _ hCw _ _ _
  let err:=fun n=>(24*Vv/Cd)*|eLow n|
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,mul_zero,abs_zero] using heLow.abs.const_mul (24*Vv/Cd)
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HLow,Hsource,HW1,Hcutoff] with n hnL hsource hW1 hnCutoff
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnL L us hus hret hmesh hstar] with jGrid hgridL
  dsimp only at hgridL ⊢
  intro U hs hU hcut hmassstar hstarK
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as 0 star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let children:=nativeActualConstantSourceChildren_high_only (M n) as star U hs hU
  let rows:=nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth children
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks_high_only (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have Hleaves Q (hQ : Q∈children) : Q.tree.leaves ≤ 3:=nativeActualConstantSourceChildren_leaves_high_only (M n) hs hU Q hQ
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
    (fun P hP=>nativeActualConstantSourceChildren_valid_high_only (M n) hs hU P hP) Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
    1 (fun P hP=>nativeActualConstantSourceChildren_generation_high_only (M n) hs hU P hP) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
    3 Hleaves Q hQ
  have Hmi : partitionPoint 0 as 0 ≤ Cmass*(M n).xs:=by
    simp only [partitionPoint,partitionValues_zero,id_eq]
    exact mul_nonneg hCmass (M n).hxs.le
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourGammaRestorationError_high_only (M n) U (W n) Q false| ≤
      |Q.term.coefficient| *(2/Cd)*(|eLow n| *(M n).xs^2):=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    have HD : Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ rBound+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [rBound]
      omega
    have Hlow0:=hgridL U hs hU hcut 0 Q.generation Q.tree Q.term HV (Nat.zero_le star)
      (by dsimp only [rBound];omega) HD Hmi hmassstar
    have Hlow1:=hgridL U hs hU hcut 0 Q.generation g.tree (Q.term.retarget 0) HV.retarget (Nat.zero_le star)
      hg HD Hmi hmassstar
    have Hlowmajor : |Q.term.coefficient| *eLow n*(W n*(M n).xs^2) ≤
        |Q.term.coefficient| *W n*(|eLow n| *(M n).xs^2):=by
      have H:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self (eLow n)) (abs_nonneg Q.term.coefficient))
        (show 0 ≤ W n*(M n).xs^2 by positivity)
      convert H using 1
      ring
    have Herror:=actual_minimum_four_gamma_restoration_error_abs_le_high_only (M n) hCf hsource hxs1 Q ho hs hU false hW hcK
      (show 0 ≤ |eLow n| *(M n).xs^2 by positivity) hstarK
      (Hlow0.trans Hlowmajor) (Hlow1.trans Hlowmajor)
    simpa only [Cd] using Herror
  have Hvariation:=nativeActualFourCenteredForest_coefficient_variation_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth children 3 Hleaves
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi1,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_high_only (M n)
    hCf hsource hxs1 hW hcK ho hs hU hstarK
  have hKpos : 0 < K star:=(mul_pos hcK hW).trans_le hstarK
  have hchi0 : 0 ≤ chi:=by nlinarith
  have hchi : |chi| ≤ 1:=by rw [abs_of_nonneg hchi0];exact hchi1
  have Hcoeff : (children.map (fun Q=>|Q.term.coefficient|)).sum ≤ 6:=by
    have H:=native_actual_constant_child_family_coefficient_variation_le (i:=0) ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi
    norm_num only [NativeActualExpansionOp.coefficientCost,Nat.cast_one] at H
    exact H
  have Htotal : (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤ 12*Vv:=by
    apply Hvariation.trans
    have H:=mul_le_mul_of_nonneg_left Hcoeff (show 0 ≤ 2*Vv by positivity)
    convert H using 1
    ring
  have Hsum:=List.sum_le_sum Hrow
  rw [List.sum_map_mul_right,List.sum_map_mul_right] at Hsum
  apply Hsum.trans
  have H:=mul_le_mul_of_nonneg_right Htotal
    (show 0 ≤ (2/Cd)*(|eLow n| *(M n).xs^2) by positivity)
  convert H using 1 <;> (try dsimp only [err]) <;> ring

theorem actual_inherited_constant_child_gamma_LOW_restoration_category_rate_along_high_only
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(U : ℕ) (hs : star<U) (hU : U ≤ as.length),
        partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_high_only (M n) as star U hs hU)).map
          (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_high_only (M n) U Q .gammaLowRestoration)).sum|/
          (chi*K star) ≤ err n*(M n).xs^2 := by
  obtain ⟨err,herr,H⟩:=actual_inherited_constant_child_gamma_LOW_restoration_forest_rate_along_high_only
    depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim Hsource Hcutoff w hw
  refine ⟨err,herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1,Hcutoff] with n hn hsClocks hW1 hnCutoff
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro U hs hU hcut hmassstar hstarK
  apply (actual_gamma_restoration_category_signed_sum_abs_le_error_sum_high_only (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _ false).trans
  exact hj U hs hU hcut hmassstar hstarK

theorem actual_inherited_initial_gamma_LOW_restoration_forest_rate_along_high_only
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (x : ℕ→ℝ) (hxsx : ∀ᶠn in atTop,(M n).xs ≤ x n)
    (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as i ≤ Cmass*x n →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀seedMass : ℝ,
        ((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
          [nativeActualInitialState as i star seedMass (hi.trans (hs.le.trans hU))]).map
          (fun Q=>|nativeActualOriginalFourGammaRestorationError_high_only (M n) U (W n) Q false|)).sum ≤
            err n*(x n*(M n).xs^2) := by
  let degree:=1+depth
  let rBound:=2+6*depth
  obtain ⟨eLow,heLow,HLow⟩:=actual_inherited_initial_resource_gamma_LOW_restoration_rate_along_high_only
    degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource Hcutoff x hxsx hxW w hw
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 2 depth
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVv : 0 ≤ Vv:=nativeActualWeightedFrontierCost_nonneg _ hCw _ _ _
  let err:=fun n=>(4*Vv/Cd)*|eLow n|
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,mul_zero,abs_zero] using heLow.abs.const_mul (4*Vv/Cd)
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HLow,Hsource,HW1,hxsx,Hcutoff] with n hnL hsource hW1 hxn hnCutoff
  have hxW0 : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW0.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW0
  intro L us hus hret hmesh hstar
  filter_upwards [hnL L us hus hret hmesh hstar] with jGrid hgridL
  dsimp only at hgridL ⊢
  intro i U hi hs hU hcut hmi hmassstar hstarK seedMass
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
  let children:=[st]
  let rows:=nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth children
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks_high_only (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have hst : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU seedMass .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have Hleaves Q (hQ : Q∈children) : Q.tree.leaves ≤ 2:=by
    have heq : Q=st:=List.mem_singleton.mp hQ
    subst Q
    exact nativeActualInitialState_leaves_le as i star seedMass (hi.trans (hs.le.trans hU))
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
    (fun P hP=>by have heq : P=st:=List.mem_singleton.mp hP;subst P;exact hst) Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
    0 (fun P hP=>by have heq : P=st:=List.mem_singleton.mp hP;subst P;rfl) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
    2 Hleaves Q hQ
  have hx : 0 < x n:=(M n).hxs.trans_le hxn
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourGammaRestorationError_high_only (M n) U (W n) Q false| ≤
      |Q.term.coefficient| *(2/Cd)*(|eLow n| *((M n).xs^2*x n)):=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    have HD : 1+Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ rBound+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [rBound]
      omega
    have Hlow0:=hgridL U hs hU hcut i Q.generation Q.tree Q.term HV hi
      (by dsimp only [rBound];omega) HD hmi hmassstar
    have Hlow1:=hgridL U hs hU hcut i Q.generation g.tree (Q.term.retarget 0) HV.retarget hi
      hg HD hmi hmassstar
    have Hlowmajor : |Q.term.coefficient| *eLow n*(W n*(M n).xs^2*x n) ≤
        |Q.term.coefficient| *W n*(|eLow n| *((M n).xs^2*x n)):=by
      have H:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self (eLow n)) (abs_nonneg Q.term.coefficient))
        (show 0 ≤ W n*(M n).xs^2*x n by positivity)
      convert H using 1
      ring
    have Herror:=actual_minimum_four_gamma_restoration_error_abs_le_high_only (M n) hCf hsource hxs1 Q ho hs hU false hW hcK
      (show 0 ≤ |eLow n| *((M n).xs^2*x n) by positivity) hstarK
      (Hlow0.trans Hlowmajor) (Hlow1.trans Hlowmajor)
    simpa only [Cd] using Herror
  have Hvariation:=nativeActualFourCenteredForest_coefficient_variation_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth children 2 Hleaves
  have Htotal : (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤ 2*Vv:=by
    have Hcoeff : (children.map (fun Q=>|Q.term.coefficient|)).sum=1:=by
      simp only [children,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,add_zero]
    rw [Hcoeff,mul_one] at Hvariation
    exact Hvariation
  have Hsum:=List.sum_le_sum Hrow
  rw [List.sum_map_mul_right,List.sum_map_mul_right] at Hsum
  apply Hsum.trans
  have H:=mul_le_mul_of_nonneg_right Htotal
    (show 0 ≤ (2/Cd)*(|eLow n| *((M n).xs^2*x n)) by positivity)
  convert H using 1 <;> (try dsimp only [err]) <;> ring

theorem actual_inherited_initial_gamma_LOW_restoration_category_rate_along_high_only
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (x : ℕ→ℝ) (hxsx : ∀ᶠn in atTop,(M n).xs ≤ x n)
    (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as i ≤ Cmass*x n →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀seedMass : ℝ,
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
          [nativeActualInitialState as i star seedMass (hi.trans (hs.le.trans hU))]).map
          (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_high_only (M n) U Q .gammaLowRestoration)).sum|/
          (chi*K star) ≤ err n*(x n*(M n).xs^2) := by
  obtain ⟨err,herr,H⟩:=actual_inherited_initial_gamma_LOW_restoration_forest_rate_along_high_only
    depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim Hsource Hcutoff x hxsx hxW w hw
  refine ⟨err,herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1,Hcutoff] with n hn hsClocks hW1 hnCutoff
  have hxW0 : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW0.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW0
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro i U hi hs hU hcut hmi hmassstar hstarK seedMass
  apply (actual_gamma_restoration_category_signed_sum_abs_le_error_sum_high_only (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _ false).trans
  exact hj i U hi hs hU hcut hmi hmassstar hstarK seedMass

theorem actual_inherited_constant_child_joint_LOW_restoration_forest_rate_along_high_only
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(U : ℕ) (hs : star<U) (hU : U ≤ as.length),
        partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_high_only (M n) as star U hs hU)).map
          (fun Q=>|nativeActualOriginalFourJointLowRestorationError_high_only (M n) U (W n) Q|)).sum ≤
            err n*(M n).xs^2 := by
  let degree:=1+depth
  let rBound:=3+6*depth
  obtain ⟨eLow,heLow,HLow⟩:=actual_inherited_constant_resource_fresh_joint_LOW_restoration_rate_along_high_only
    degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource Hcutoff w hw
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 3 depth
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVv : 0 ≤ Vv:=nativeActualWeightedFrontierCost_nonneg _ hCw _ _ _
  let err:=fun n=>(24*Vv/Cd)*|eLow n|
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,mul_zero,abs_zero] using heLow.abs.const_mul (24*Vv/Cd)
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HLow,Hsource,HW1,Hcutoff] with n hnL hsource hW1 hnCutoff
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hnL L us hus hret hmesh hstar] with jGrid hgridL
  dsimp only at hgridL ⊢
  intro U hs hU hcut hmassstar hstarK
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as 0 star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let children:=nativeActualConstantSourceChildren_high_only (M n) as star U hs hU
  let rows:=nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth children
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks_high_only (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have Hleaves Q (hQ : Q∈children) : Q.tree.leaves ≤ 3:=nativeActualConstantSourceChildren_leaves_high_only (M n) hs hU Q hQ
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
    (fun P hP=>nativeActualConstantSourceChildren_valid_high_only (M n) hs hU P hP) Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
    1 (fun P hP=>nativeActualConstantSourceChildren_generation_high_only (M n) hs hU P hP) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
    3 Hleaves Q hQ
  have Hmi : partitionPoint 0 as 0 ≤ Cmass*(M n).xs:=by
    simp only [partitionPoint,partitionValues_zero,id_eq]
    exact mul_nonneg hCmass (M n).hxs.le
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourJointLowRestorationError_high_only (M n) U (W n) Q| ≤
      |Q.term.coefficient| *(2/Cd)*(|eLow n| *(M n).xs^2):=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    have HD : Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ rBound+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [rBound]
      omega
    have Hlow0:=hgridL U hs hU hcut 0 Q.generation Q.tree Q.term HV (Nat.zero_le star)
      (by dsimp only [rBound];omega) HD Hmi hmassstar
    have Hlow1:=hgridL U hs hU hcut 0 Q.generation g.tree (Q.term.retarget 0) HV.retarget (Nat.zero_le star)
      hg HD Hmi hmassstar
    have Hlowmajor : |Q.term.coefficient| *eLow n*(W n*(M n).xs^2) ≤
        |Q.term.coefficient| *W n*(|eLow n| *(M n).xs^2):=by
      have H:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self (eLow n)) (abs_nonneg Q.term.coefficient))
        (show 0 ≤ W n*(M n).xs^2 by positivity)
      convert H using 1
      ring
    have Herror:=actual_minimum_four_joint_LOW_restoration_error_abs_le_high_only (M n) hCf hsource hxs1 Q ho hs hU hW hcK
      (show 0 ≤ |eLow n| *(M n).xs^2 by positivity) hstarK
      (Hlow0.trans Hlowmajor) (Hlow1.trans Hlowmajor)
    simpa only [Cd] using Herror
  have Hvariation:=nativeActualFourCenteredForest_coefficient_variation_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth children 3 Hleaves
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi1,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_high_only (M n)
    hCf hsource hxs1 hW hcK ho hs hU hstarK
  have hKpos : 0 < K star:=(mul_pos hcK hW).trans_le hstarK
  have hchi0 : 0 ≤ chi:=by nlinarith
  have hchi : |chi| ≤ 1:=by rw [abs_of_nonneg hchi0];exact hchi1
  have Hcoeff : (children.map (fun Q=>|Q.term.coefficient|)).sum ≤ 6:=by
    have H:=native_actual_constant_child_family_coefficient_variation_le (i:=0) ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi
    norm_num only [NativeActualExpansionOp.coefficientCost,Nat.cast_one] at H
    exact H
  have Htotal : (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤ 12*Vv:=by
    apply Hvariation.trans
    have H:=mul_le_mul_of_nonneg_left Hcoeff (show 0 ≤ 2*Vv by positivity)
    convert H using 1
    ring
  have Hsum:=List.sum_le_sum Hrow
  rw [List.sum_map_mul_right,List.sum_map_mul_right] at Hsum
  apply Hsum.trans
  have H:=mul_le_mul_of_nonneg_right Htotal
    (show 0 ≤ (2/Cd)*(|eLow n| *(M n).xs^2) by positivity)
  convert H using 1 <;> (try dsimp only [err]) <;> ring

theorem actual_inherited_constant_child_joint_LOW_restoration_category_rate_along_high_only
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(U : ℕ) (hs : star<U) (hU : U ≤ as.length),
        partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren_high_only (M n) as star U hs hU)).map
          (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_high_only (M n) U Q .jointLowRestoration)).sum|/
          (chi*K star) ≤ err n*(M n).xs^2 := by
  obtain ⟨err,herr,H⟩:=actual_inherited_constant_child_joint_LOW_restoration_forest_rate_along_high_only
    depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim Hsource Hcutoff w hw
  refine ⟨err,herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1,Hcutoff] with n hn hsClocks hW1 hnCutoff
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro U hs hU hcut hmassstar hstarK
  apply (actual_joint_LOW_restoration_category_signed_sum_abs_le_error_sum_high_only (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _).trans
  exact hj U hs hU hcut hmassstar hstarK

theorem actual_inherited_initial_canonical_third_LOW_saving_along_high_only
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Cinitial Couter : ℝ)
    (hTemp : 0≤ Temp) (hCf : 0≤ Cf) (hCm : 0≤ Cmass) (hCinitial : 0≤ Cinitial) (hCouter : 0< Couter)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) (hCs : 0≤ Cs)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale) (hWlim : Tendsto W atTop (𝓝 0))
    (HS : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃Ci : ℝ,0< Ci ∧ ∃err : ℕ→ℝ,(∀n,0≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),(∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→
        ((L+1:ℕ):ℝ)⁻¹≤(M n).xs→(w n).star∈us→
      ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=> Sum.elim (fun _=> b j) (fun _=> h j)
        ∀(i V U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (l t : ℝ),
          U≤ as.length→0< V→i< V→V≤ star→star< U→T.leaves≤ rBound→NativePersistentLowForks i star U T→
          partitionPoint 0 as V≤ Cinitial*(M n).xs→partitionPoint 0 as U≤ Couter*W n→
          l∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        ∀(G : ActualNaturalBoundaryShape (dim n) aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)),
          (∀e,G.sourceLowMass e≤ Cmass*sourceFactorScale (M n).xs (W n) initial e)→
        ∀a z : T.Slot,a≠z→V≤ T.splitIndex a z→
        |nativeActualCenteredThirdLowPart (dim n) q U b h K T (G.canonicalHighOnlySource (M n) forms).restProduct a z l t|≤
          sourceMonomialScale (M n).xs (W n) initial*
            (Ci*W n*(M n).xs*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
              err n*W n*(M n).xs^2) := by
  obtain ⟨Ci,hCi,HI⟩:=eventually_actual_minimum_inherited_initial_centered_LOW_modulus_budget_high_only
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Cinitial Couter hTemp hCf hCm hCinitial hCouter.le
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_centered_transient_LOW_part_budget_high_only
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Couter hTemp hCf hCm hCouter.le
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let eta:=actualMassSavingExponent m delta
  let amp:=fun n=> actualMinimumInheritedLowErrorDensityAmplitude_high_only (M n) Temp Cf Couter
  let err:=fun n=> Cp*((rBound:ℝ)*((dim n+1:ℕ):ℝ)^(-eta/32)+W n*amp n)
  have HCerr:0≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along_high_only hm hdelta hC0 Cerr HCerr
    dim hdim M W hcanonical hWlim w hw
  have Hamp:Tendsto amp atTop (𝓝 0):=by
    apply actualMinimumInheritedLowErrorDensityAmplitude_regular_tendsto_zero_along_high_only
      hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M hsmall _ Hclock Homit Hcutoff Couter hCouter
    simpa only [←hcanonical] using hWlim
  have Hpow:=(tendsto_rpow_neg_atTop (show 0< eta/32 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr:Tendsto err atTop (𝓝 0):=by
    have H:=((Hpow.const_mul (rBound:ℝ)).add (hWlim.mul Hamp)).const_mul Cp
    simpa only [err,Function.comp_def,zero_mul,add_zero,mul_zero,neg_div] using H
  refine ⟨Ci,hCi,err,?_,Herr,?_⟩
  · intro n
    have HW:0< W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_pos
    have HA:0≤ amp n:=by
      have HD:0<(M n).actualOriginalLowErrorDensitySaving Couter:=(M n).actualOriginalLowErrorDensitySaving_pos hCouter
      dsimp [amp,actualMinimumInheritedLowErrorDensityAmplitude_high_only]
      positivity
    dsimp [err];positivity
  · have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
    filter_upwards [hdim.eventually HI,hdim.eventually HP,HR,HS,HW1,Hcutoff] with n hnI hnP hnR hs hw1 hnCutoff
    have hxsW:(M n).xs≤ W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
    have hxs1:=(hxsW.trans hw1)
    intro L us hus hret hmesh hStarNode
    filter_upwards [hnI (M n) hnCutoff.1 hnCutoff.2 hs hxs1 L us hus hret hmesh,hnP (M n) hnCutoff.1 hnCutoff.2 hs hxs1 L us hus hret hmesh,
      hnR us hus hStarNode,actual_minimum_inherited_current_low_error_saved_density_on_every_final_net_high_only (M n)
        Temp Cf Couter hTemp hCf hCouter hs hxs1 us hus] with k hkI hkP hkR hkD
    dsimp only at hkI hkP hkR hkD ⊢
    intro i V U T l t hU hV hiV hVstar hstar hLeaves hpersistent hcutI hcut hl ht G forms initial hmass a z haz htarget
    let as:=finiteCutMasses us k
    let star:=retainedMassPrefixIndex (w n).star.val as
    let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=> Sum.elim (fun _=> b j) (fun _=> h j)
    let P:=(G.canonicalHighOnlySource (M n) forms).restProduct
    let p0:=sourceMonomialScale (M n).xs (W n) initial
    let law:=cutFullVariance (dim n) q U l t b h K
    let R:=nativeWholeLawErrorRadius (dim n) as law (cutLowError (dim n) U b h K)
    have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus k
    have hW:0< W n:=(M n).hxs.trans_le hxsW
    have hxs:0<(M n).xs:=(M n).hxs
    have hp0:0≤ p0:=by dsimp [p0];unfold sourceMonomialScale;positivity
    have HIpoint:=hkI U V i star T l t hU hV (hVstar.trans hstar.le) hiV hcutI hl ht hLeaves
      G forms initial (M n).xs (W n) le_rfl hxsW hw1 hcut hmass a z haz htarget
    have HE (part : NativeTransientLowErrorPart):=hkP i star U part T l t hU hl ht hLeaves
      G forms initial (W n) hxsW hw1 hcut hmass a z
    have HstarCost:=native_transient_low_star_profile_le_fixed_radius (dim n) U i star b h K T ho hU hstar law hLeaves
    have Hrad:R star≤((dim n+1:ℕ):ℝ)^(-eta/32)*((M n).xs^2/W n):=by
      have H:=actual_minimum_inherited_current_low_error_radius_le_original_high_only (M n) Temp Cf hTemp hCf hs hxs1
        ho U hl ht star (hstar.le.trans hU)
      change R star≤ if star< U then Cerr*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as star+1/(dim n+1:ℕ)) else 0 at H
      rw [ite_eq_left hstar] at H
      exact H.trans (by simpa only [eta,Cerr,neg_div] using hkR)
    have HSpoint:=HE .star
    have HStarScaled:=mul_le_mul_of_nonneg_left HstarCost (show 0≤Cp*(W n)^2*p0 by positivity)
    have HH:|nativeTransientCenteredLowErrorPart (dim n) q i star U b h K T P (sitePair T a z) 0 .star l t|≤
      Cp*(W n)^2*p0*((rBound:ℝ)*R star):=HSpoint.trans HStarScaled
    have HM:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left Hrad (Nat.cast_nonneg rBound))
      (show 0≤ Cp*(W n)^2*p0 by positivity)
    have HSbound:=HH.trans HM
    have HmovingCost:=native_persistent_moving_low_profile_le_density (dim n) U i star b h K T ho hpersistent law
    have HD:edgeBudget 0 as R≤ amp n*(M n).xs^2:=by
      apply hkD U hU
      · simpa only [hcanonical] using le_min hcut (partitionPoint_mem as ho U).2
      · exact hl
      · exact ht
    have HMpoint:|nativeTransientCenteredLowErrorPart (dim n) q i star U b h K T P (sitePair T a z) 0 .moving l t|≤
      Cp*(W n)^2*p0*(amp n*(M n).xs^2):=(HE .moving).trans
        (mul_le_mul_of_nonneg_left (HmovingCost.trans HD) (by positivity))
    rw [native_actual_centered_third_LOW_part_eq_sum (dim n) q i star U]
    apply ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add HIpoint HSbound)) HMpoint)).trans_eq
    dsimp only [err,P,p0,eta,Cerr,K,q,b,h,as]
    field_simp [hW.ne']
    ring

theorem actual_inherited_initial_resource_third_LOW_saving_along_high_only
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Cinitial Couter : ℝ)
    (hTemp : 0≤ Temp) (hCf : 0≤ Cf) (hCm : 0≤ Cmass) (hCinitial : 0≤ Cinitial) (hCouter : 0< Couter)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) (hCs : 0≤ Cs)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale) (hWlim : Tendsto W atTop (𝓝 0))
    (HS : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃Ci : ℝ,0< Ci ∧ ∃err : ℕ→ℝ,(∀n,0≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),(∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→
        ((L+1:ℕ):ℝ)⁻¹≤(M n).xs→(w n).star∈us→
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i V U k : ℕ) (seed : List NativeResourceMark) (T : ClockTree (Spin (dim n)×Bool) as)
          (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed k T P→U≤ as.length→T.leaves≤ rBound→seed.length+k≤ degree→
          0< V→i< V→V≤ star→star< U→partitionPoint 0 as V≤ Cinitial*(M n).xs→
          partitionPoint 0 as i≤ Cmass*(M n).xs→partitionPoint 0 as star≤ Cmass*W n→
          partitionPoint 0 as U≤ Couter*W n→
        ∀(a z : T.Slot) (l t : ℝ),a≠z→V≤ T.splitIndex a z→l∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        |((W n)⁻¹)^k*nativeActualResourceThirdLowPart_high_only (M n) U P a z l t|≤
          |P.coefficient| * nativeResourceScale (M n).xs (W n) 1 seed*
            (Ci*W n*(M n).xs*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
              err n*W n*(M n).xs^2) := by
  classical
  have HP (a : Fin (degree+1)):=actual_inherited_initial_canonical_third_LOW_saving_along_high_only
    a.val rBound Bclock Temp Cf Cmass Cinitial Couter hTemp hCf hCm hCinitial hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M W hcanonical hWlim HS Hcutoff hsmall Hclock Homit w hw
  choose Ci hCi err herr Herr HC using HP
  let Cmax:=1+∑a,Ci a
  have hCmax:0< Cmax:=by
    have HH:0≤∑a:Fin (degree+1),Ci a:=Finset.sum_nonneg (fun a _=>(hCi a).le)
    dsimp [Cmax];linarith
  let E:=fun n=>∑a,err a n
  have hE n:0≤ E n:=Finset.sum_nonneg (fun a _=> herr a n)
  have HE:Tendsto E atTop (𝓝 0):=by
    simpa only [E,Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun a _=> Herr a)
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget_high_only
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0:0< A:=zero_lt_one.trans_le hA
  refine ⟨A^degree*Cmax,by positivity,fun n=> A^degree*E n,fun n=> mul_nonneg (pow_nonneg hA0.le _) (hE n),?_,?_⟩
  · simpa only [mul_zero] using HE.const_mul (A^degree)
  · have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
    filter_upwards [Filter.eventually_all.mpr HC,hdim.eventually HA,HS,HW1,Hcutoff] with n hnC hnA hs hw1 hnCutoff
    have hxsW:(M n).xs≤ W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
    have hxs1:=hxsW.trans hw1
    intro L us hus hret hmesh hStarNode
    filter_upwards [Filter.eventually_all.mpr (fun a=> hnC a L us hus hret hmesh hStarNode),
      hnA (M n) hnCutoff.1 hnCutoff.2 hs hxs1 L us hus hret hmesh] with jGrid hgC hgA
    dsimp only at hgC hgA ⊢
    intro i V U k seed T P hP hU hT hdepth hV hiV hVstar hstar hcutI hmi hms hcut aSlot z l t haz htarget hl ht
    let as:=finiteCutMasses us jGrid
    let star:=retainedMassPrefixIndex (w n).star.val as
    let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=> Sum.elim (fun _=> b j) (fun _=> h j)
    let G:=nativeActualResourceCanonicalShape P.live (hiV.le.trans hVstar) (hstar.trans_le hU)
    let I:=nativeActualResourceInitialFactors P.live
    let AI:=W n*(M n).xs*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
      (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))
    let AX:=W n*(M n).xs^2
    let price:=Cmax*AI+E n*AX
    have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have hW:0< W n:=(M n).hxs.trans_le hxsW
    have hx:0<(M n).xs:=(M n).hxs
    have hCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
    have hAI:0≤ AI:=by dsimp [AI,nativeOriginalCutLowErrorRadius];positivity
    have hAX:0≤ AX:=by dsimp [AX];positivity
    have hprice:0≤ price:=by
      have HEzero:=hE n
      dsimp only [price]
      positivity
    have Hdegree:P.resources.length≤ degree+1:=by rw [hP.total_factor_depth];omega
    have Hpair:=hgA U i star T P Hdegree (hiV.le.trans (hVstar.trans (hstar.le.trans hU))) (hstar.le.trans hU)
      (M n).xs (W n) le_rfl hxsW hmi hms 1 1 (by norm_num) (by norm_num)
    have Hlive:P.live.factors.length≤ degree:=by
      have HH:=hP.total_factor_depth
      simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,List.length_map] at HH
      omega
    let a:Fin (degree+1):=⟨P.live.factors.length,by omega⟩
    have HCsource:=hgC a i V U T l t hU hV hiV hVstar hstar hT (hP.persistentLowForks (hiV.le.trans hVstar))
      hcutI hcut hl ht G (fun _=>.centered) I
      (native_actual_resource_canonical_source_mass P.live (hiV.le.trans hVstar) (hstar.trans_le hU)
        Cmass (M n).xs (W n) hmi hms) aSlot z haz htarget
    rw [native_actual_resource_live_scale_eq_annotations] at HCsource
    have HCi:Ci a≤ Cmax:=by
      have HH:=Finset.single_le_sum (fun a _=>(hCi a).le) (Finset.mem_univ a)
      dsimp [Cmax];linarith
    have HEi:err a n≤ E n:=Finset.single_le_sum (fun a _=> herr a n) (Finset.mem_univ a)
    have Hmono:=add_le_add (mul_le_mul_of_nonneg_right HCi hAI) (mul_le_mul_of_nonneg_right HEi hAX)
    have HliveBound:|nativeActualCenteredThirdLowPart (dim n) q U b h K T
        (G.canonicalHighOnlySource (M n) (fun _=> NativeSourceFactorForm.centered)).restProduct aSlot z l t|≤
        nativeResourceScale (M n).xs (W n) 1 P.live.tags*price:=by
      apply HCsource.trans
      convert mul_le_mul_of_nonneg_left Hmono (actual_resource_raw_scale_pos _ hx hW).le using 1
      dsimp only [AI,AX,price,G,I,q,b,h,K,as]
      ring
    have H:=actual_resource_third_LOW_normalized_profile_le_high_only (M n) hP hdepth ho (hiV.le.trans hVstar)
      (hstar.trans_le hU) aSlot z l t hA le_rfl hxsW hprice Hpair HliveBound
    apply H.trans_eq
    dsimp only [price,AI,AX,E,as]
    ring

theorem actual_inherited_initial_centered_resource_third_LOW_saving_along_high_only
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Cinitial Couter : ℝ)
    (hTemp : 0≤ Temp) (hCf : 0≤ Cf) (hCm : 0≤ Cmass) (hCinitial : 0≤ Cinitial) (hCouter : 0< Couter)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) (hCs : 0≤ Cs)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale) (hWlim : Tendsto W atTop (𝓝 0))
    (HS : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃Ci : ℝ,0< Ci ∧ ∃err : ℕ→ℝ,(∀n,0≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),(∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→
        ((L+1:ℕ):ℝ)⁻¹≤(M n).xs→(w n).star∈us→
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i V U k : ℕ) (seed : List NativeResourceMark) (T : ClockTree (Spin (dim n)×Bool) as)
          (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed k T P→U≤ as.length→T.leaves≤ rBound→seed.length+k≤ degree→
          0< V→i< V→V≤ star→star< U→partitionPoint 0 as V≤ Cinitial*(M n).xs→
          partitionPoint 0 as i≤ Cmass*(M n).xs→partitionPoint 0 as star≤ Cmass*W n→
          partitionPoint 0 as U≤ Couter*W n→
        ∀(a z : T.Slot) (l t : ℝ),a≠z→V≤ T.splitIndex a z→l∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        |((W n)⁻¹)^k*nativeActualOriginalCenteredResourceThirdLowPart_high_only (M n) U P a z l t|≤
          |P.coefficient| * nativeResourceScale (M n).xs (W n) 1 seed*
            (Ci*W n*(M n).xs*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
              err n*W n*(M n).xs^2) := by
  obtain ⟨Ci,hCi,err,herr,Herr,H⟩:=actual_inherited_initial_resource_third_LOW_saving_along_high_only
    degree rBound Bclock Temp Cf Cmass Cinitial Couter hTemp hCf hCm hCinitial hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M W hcanonical hWlim HS Hcutoff hsmall Hclock Homit w hw
  refine ⟨2*Ci,by positivity,fun n=>2*err n,fun n=>mul_nonneg (by norm_num) (herr n),?_,?_⟩
  · simpa only [mul_zero] using Herr.const_mul 2
  · filter_upwards [H,Hcutoff] with n hn hnCutoff
    intro L us hus hret hmesh hStarNode
    filter_upwards [hn L us hus hret hmesh hStarNode] with jGrid hj
    dsimp only at hj ⊢
    intro i V U k seed T P hP hU hT hdepth hV hiV hVstar hstar hcutI hmi hms hcut a z l t haz htarget hl ht
    have ho:=finiteCutMasses_ordered us hus jGrid
    rw [native_actual_original_centered_resource_third_LOW_eq_two_resources_high_only (M n) U P ho a z l t,mul_add]
    have HP:=hj i V U k seed T P hP hU hT hdepth hV hiV hVstar hstar hcutI hmi hms hcut a z l t haz htarget hl ht
    have HF:=hj i V U k seed T P.freeze hP.freeze hU hT hdepth hV hiV hVstar hstar hcutI hmi hms hcut a z l t haz htarget hl ht
    simp only [NativeResourceTerm.freeze,abs_neg] at HF
    apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
    ring

theorem actual_inherited_initial_fresh_resource_third_LOW_saving_along_high_only
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Cinitial Couter : ℝ)
    (hTemp : 0≤ Temp) (hCf : 0≤ Cf) (hCm : 0≤ Cmass) (hCinitial : 0≤ Cinitial) (hCouter : 0< Couter)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) (hCs : 0≤ Cs)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale) (hWlim : Tendsto W atTop (𝓝 0))
    (HS : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃Ci : ℝ,0< Ci ∧ ∃err : ℕ→ℝ,(∀n,0≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),(∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→
        ((L+1:ℕ):ℝ)⁻¹≤(M n).xs→(w n).star∈us→
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i V U k : ℕ) (seed : List NativeResourceMark) (T : ClockTree (Spin (dim n)×Bool) as)
          (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed k T P→U≤ as.length→T.leaves≤ rBound→seed.length+k≤ degree→
          0< V→i< V→V≤ star→star< U→partitionPoint 0 as V≤ Cinitial*(M n).xs→
          partitionPoint 0 as i≤ Cmass*(M n).xs→partitionPoint 0 as star≤ Cmass*W n→
          partitionPoint 0 as U≤ Couter*W n→
        ∀(l t : ℝ),l∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        |((W n)⁻¹)^k*nativeActualOriginalFreshResourceThirdLowPart_high_only (M n) U P l t|≤
          |P.coefficient| * nativeResourceScale (M n).xs (W n) 1 seed*
            (Ci*W n*(M n).xs*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
              err n*W n*(M n).xs^2) := by
  obtain ⟨Ci,hCi,err,herr,Herr,H⟩:=actual_inherited_initial_centered_resource_third_LOW_saving_along_high_only
    degree (rBound+1) Bclock Temp Cf Cmass Cinitial Couter hTemp hCf hCm hCinitial hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M W hcanonical hWlim HS Hcutoff hsmall Hclock Homit w hw
  refine ⟨Ci,hCi,err,herr,Herr,?_⟩
  filter_upwards [H,Hcutoff] with n hn hnCutoff
  intro L us hus hret hmesh hStarNode
  filter_upwards [hn L us hus hret hmesh hStarNode] with jGrid hj
  dsimp only at hj ⊢
  intro i V U k seed T P hP hU hT hdepth hV hiV hVstar hstar hcutI hmi hms hcut l t hl ht
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hg:g.tree.leaves≤ rBound+1:=by
    have HH:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have Hsplit:g.tree.splitIndex (g.embed P.live.test.target) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,min_eq_left (hstar.le.trans hU)]
  have haz:g.embed P.live.test.target≠g.mark:=by
    intro heq
    have HH:=Hsplit
    rw [heq,g.tree.splitIndex_self] at HH
    dsimp only [star,as] at HH
    omega
  have HO:=hj i V U k seed g.tree (P.retarget 0) hP.retarget hU hg hdepth hV hiV hVstar hstar hcutI hmi hms hcut
    (g.embed P.live.test.target) g.mark l t haz (by rw [Hsplit];exact hVstar) hl ht
  rw [native_actual_original_fresh_resource_third_LOW_eq_centered_retarget_high_only (M n) U P ho]
  simpa only [NativeResourceTerm.retarget] using HO

end OAI.SKFluctuations.Cavity
