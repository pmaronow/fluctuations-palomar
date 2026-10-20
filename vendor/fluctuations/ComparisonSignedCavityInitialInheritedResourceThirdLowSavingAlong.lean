module

public import ComparisonSignedCavityInitialInheritedThirdLowSavingAlong
public import ComparisonSignedCavityActualResourceLowTaylorReadout
public import ComparisonSignedCavityActualCenteredResourceLowTaylorReadout
public import ComparisonSignedCavityActualFreshResourceLowTaylorReadout
public import ComparisonSignedCavityInheritedRawResourcePairBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_resource_third_LOW_saving_along
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Cinitial Couter : ℝ)
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
        |((W n)⁻¹)^k*nativeActualResourceThirdLowPart (M n) U P a z l t|≤
          |P.coefficient| * nativeResourceScale (M n).xs (W n) 1 seed*
            (Ci*W n*(M n).xs*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
              err n*W n*(M n).xs^2) := by
  classical
  have HP (a : Fin (degree+1)):=actual_inherited_initial_canonical_third_LOW_saving_along
    a.val rBound Bclock Temp Cf Cmass Cinitial Couter hTemp hCf hCm hCinitial hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M W hcanonical hWlim HS hsmall Hclock w hw
  choose Ci hCi err herr Herr HC using HP
  let Cmax:=1+∑a,Ci a
  have hCmax:0< Cmax:=by
    have HH:0≤∑a:Fin (degree+1),Ci a:=Finset.sum_nonneg (fun a _=>(hCi a).le)
    dsimp [Cmax];linarith
  let E:=fun n=>∑a,err a n
  have hE n:0≤ E n:=Finset.sum_nonneg (fun a _=> herr a n)
  have HE:Tendsto E atTop (𝓝 0):=by
    simpa only [E,Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun a _=> Herr a)
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0:0< A:=zero_lt_one.trans_le hA
  refine ⟨A^degree*Cmax,by positivity,fun n=> A^degree*E n,fun n=> mul_nonneg (pow_nonneg hA0.le _) (hE n),?_,?_⟩
  · simpa only [mul_zero] using HE.const_mul (A^degree)
  · have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
    filter_upwards [Filter.eventually_all.mpr HC,hdim.eventually HA,HS,HW1] with n hnC hnA hs hw1
    have hxsW:(M n).xs≤ W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
    have hxs1:=hxsW.trans hw1
    intro L us hus hret hmesh hStarNode
    filter_upwards [Filter.eventually_all.mpr (fun a=> hnC a L us hus hret hmesh hStarNode),
      hnA (M n) hs hxs1 L us hus hret hmesh] with jGrid hgC hgA
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
        (G.canonicalMinimumSource (M n) (fun _=> NativeSourceFactorForm.centered)).restProduct aSlot z l t|≤
        nativeResourceScale (M n).xs (W n) 1 P.live.tags*price:=by
      apply HCsource.trans
      convert mul_le_mul_of_nonneg_left Hmono (actual_resource_raw_scale_pos _ hx hW).le using 1
      dsimp only [AI,AX,price,G,I,q,b,h,K,as]
      ring
    have H:=actual_resource_third_LOW_normalized_profile_le (M n) hP hdepth ho (hiV.le.trans hVstar)
      (hstar.trans_le hU) aSlot z l t hA le_rfl hxsW hprice Hpair HliveBound
    apply H.trans_eq
    dsimp only [price,AI,AX,E,as]
    ring

end OAI.SKFluctuations.Cavity
