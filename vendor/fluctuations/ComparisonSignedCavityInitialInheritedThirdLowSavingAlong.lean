module

public import ComparisonSignedCavityInitialInheritedCenteredModulusBudget
public import ComparisonSignedCavityInheritedCenteredTransientLowPart
public import ComparisonSignedCavityActualConstantTransientLowProfile
public import ComparisonSignedCavityActualInheritedLowErrorDensityAlong
public import ComparisonSignedCavitySharpOriginalLowRadiusAlong
public import ComparisonSignedCavityTransientLowStarProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_canonical_third_LOW_saving_along
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Cinitial Couter : ℝ)
    (hTemp : 0≤ Temp) (hCf : 0≤ Cf) (hCm : 0≤ Cmass) (hCinitial : 0≤ Cinitial) (hCouter : 0< Couter)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) (hCs : 0≤ Cs)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale) (hWlim : Tendsto W atTop (𝓝 0))
    (HS : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
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
        |nativeActualCenteredThirdLowPart (dim n) q U b h K T (G.canonicalMinimumSource (M n) forms).restProduct a z l t|≤
          sourceMonomialScale (M n).xs (W n) initial*
            (Ci*W n*(M n).xs*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
              err n*W n*(M n).xs^2) := by
  obtain ⟨Ci,hCi,HI⟩:=eventually_actual_minimum_inherited_initial_centered_LOW_modulus_budget
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Cinitial Couter hTemp hCf hCm hCinitial hCouter.le
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_centered_transient_LOW_part_budget
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Couter hTemp hCf hCm hCouter.le
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let eta:=actualMassSavingExponent m delta
  let amp:=fun n=> actualMinimumInheritedLowErrorDensityAmplitude (M n) Temp Cf Couter
  let err:=fun n=> Cp*((rBound:ℝ)*((dim n+1:ℕ):ℝ)^(-eta/32)+W n*amp n)
  have HCerr:0≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along hm hdelta hC0 Cerr HCerr
    dim hdim M W hcanonical hWlim w hw
  have Hamp:Tendsto amp atTop (𝓝 0):=by
    apply actualMinimumInheritedLowErrorDensityAmplitude_regular_tendsto_zero_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M hsmall _ Hclock Couter hCouter
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
      dsimp [amp,actualMinimumInheritedLowErrorDensityAmplitude]
      positivity
    dsimp [err];positivity
  · have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
    filter_upwards [hdim.eventually HI,hdim.eventually HP,HR,HS,HW1] with n hnI hnP hnR hs hw1
    have hxsW:(M n).xs≤ W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
    have hxs1:=(hxsW.trans hw1)
    intro L us hus hret hmesh hStarNode
    filter_upwards [hnI (M n) hs hxs1 L us hus hret hmesh,hnP (M n) hs hxs1 L us hus hret hmesh,
      hnR us hus hStarNode,actual_minimum_inherited_current_low_error_saved_density_on_every_final_net (M n)
        Temp Cf Couter hTemp hCf hCouter hs hxs1 us hus] with k hkI hkP hkR hkD
    dsimp only at hkI hkP hkR hkD ⊢
    intro i V U T l t hU hV hiV hVstar hstar hLeaves hpersistent hcutI hcut hl ht G forms initial hmass a z haz htarget
    let as:=finiteCutMasses us k
    let star:=retainedMassPrefixIndex (w n).star.val as
    let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=> Sum.elim (fun _=> b j) (fun _=> h j)
    let P:=(G.canonicalMinimumSource (M n) forms).restProduct
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
      have H:=actual_minimum_inherited_current_low_error_radius_le_original (M n) Temp Cf hTemp hCf hs hxs1
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

end OAI.SKFluctuations.Cavity
