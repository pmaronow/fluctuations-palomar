module

public import ComparisonSignedCavityActualCenteredResourceLowTaylorFromMinimum
public import ComparisonSignedCavityActualFreshResourceLowTaylorReadout
public import ComparisonSignedCavityActualConstantResourceLowForks
public import ComparisonSignedCavityActualInheritedLowErrorDensityAlong
public import ComparisonSignedCavitySharpOriginalLowRadiusAlong
public import ComparisonSignedCavityTransientForkCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem actual_inherited_constant_resource_fresh_third_LOW_rate_along
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠ n : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠ n : ℕ in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠ n : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
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
            |((W n)⁻¹)^k*nativeActualOriginalFreshResourceThirdLowPart (M n) U P l t| ≤
              |P.coefficient| *err n*(W n*(M n).xs^2) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_centered_resource_third_LOW_from_minimum
    (D:=D) degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let eta:=actualMassSavingExponent m delta
  let amp:=fun n=>actualMinimumInheritedLowErrorDensityAmplitude (M n) Temp Cf Ccut
  let err:=fun n=>C*((rBound:ℝ)*((dim n+1:ℕ):ℝ)^(-eta/32)+W n*amp n)
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along hm hdelta hC0 Cerr
    (actualLowErrorComparisonConstant_nonneg _ hTemp) dim hdim M W hcanonical hWlim w hw
  have Hamp : Tendsto amp atTop (𝓝 0):=by
    apply actualMinimumInheritedLowErrorDensityAmplitude_regular_tendsto_zero_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M hsmall _ Hclock Ccut hCcut
    simpa only [←hcanonical] using hWlim
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/32 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    have H:=((Hpow.const_mul (rBound:ℝ)).add (hWlim.mul Hamp)).const_mul C
    simpa only [err,Function.comp_def,zero_mul,add_zero,mul_zero,neg_div] using H
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HC,HR,Hsource,HW1] with n hnC hnR hsource hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hx1:=hxW.trans hW1
  intro L us hus hret hmesh hstar
  filter_upwards [hnC (M n) hsource hx1 L us hus hret hmesh,hnR us hus hstar,
    actual_minimum_inherited_current_low_error_saved_density_on_every_final_net (M n)
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
    have H:=actual_minimum_inherited_current_low_error_radius_le_original (M n) Temp Cf hTemp hCf
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
  change |((W n)⁻¹)^k*nativeActualOriginalCenteredResourceThirdLowPart (M n) U (P.retarget 0)
      (g.embed P.live.test.target) g.mark l t| ≤ |P.coefficient| *
        nativeResourceScale (M n).xs (W n) 1 []*(C*(W n)^2*(g.tree.forkCost R+edgeBudget 0 as R)) at H
  simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at H
  rw [native_actual_original_fresh_resource_third_LOW_eq_centered_retarget (M n) U P ho]
  have HF' := HF.trans (mul_le_mul_of_nonneg_left Hrad (Nat.cast_nonneg rBound))
  have Hsum:=mul_le_mul_of_nonneg_left (add_le_add HF' HD)
    (show 0 ≤ |P.coefficient| *C*(W n)^2 by positivity)
  have hW : W n≠0:=((M n).hxs.trans_le hxW).ne'
  apply H.trans
  convert Hsum using 1 <;> (try dsimp only [err,eta,amp]) <;> field_simp [hW]

end OAI.SKFluctuations.Cavity
