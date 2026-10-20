module

public import ComparisonSignedCavitySecondLowActualHistoryFullResourceB0ModulusAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false

def ActualHistorySecondLowFullHalfRetargetB0ModulusOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Rmacro Cx Cerr Ci : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop:=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (w n).star∈us → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
  ∀ᶠjGrid in atTop,
    let as:=finiteCutMasses us jGrid
    ∀(pre mid tail : List PositiveMass),as=pre++(mid++tail) →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
    ∀(V U : ℕ) (_hU : U ≤ (pre++(mid++tail)).length)
      (seed : List NativeResourceMark)
      (st : NativeActualResourceState (Spin (dim n)×Bool) (pre++(mid++tail)) pre.length (pre.length+mid.length)),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed st.generation st.tree st.term → st.term.resources.length ≤ degree →
      0 < mid.length → 0 < V → pre.length < V → V ≤ pre.length+mid.length → pre.length+mid.length < U → st.tree.leaves ≤ rBound →
      partitionPoint 0 as V ≤ Ccut*(M n).xs → partitionPoint 0 as U ≤ Couter*W n →
    ∀(x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),(M n).xs ≤ x → x ≤ W n →
      partitionPoint 0 as pre.length ≤ Cmass*x → partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      4*W n ≤ (M n).R (partitionPoint 0 as U) →
      (M n).z ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).R (partitionPoint 0 as pre.length) ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
      Cx*(M n).xs ≤ sourceMass → partitionPoint 0 as U=sourceMass →
      (∀j ≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us) →
    |((W n)⁻¹)^st.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U st .secondLow| ≤
      |st.term.coefficient| *nativeResourceScale x (W n) 1 seed*
        (Ci*partitionPoint 0 as U*(M n).xs*Cerr*
          (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ))+
          eps n*W n*(M n).xs^2)

theorem native_actual_original_full_four_second_low_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (hU : U ≤ as.length)
    (ho : MassOrdered 0 as) (hs : star < U)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (W B : ℝ)
    (H0 : |(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceB0 M U st.term| ≤ B)
    (H1 : |(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceB0 M U (st.term.retarget 0)| ≤ B) :
    |(W⁻¹)^st.generation*nativeActualOriginalFourOtherCategoryContrast M U st .secondLow| ≤ (3/2:ℝ)*B := by
  rw [native_actual_four_second_low_eq_two_full_resource_sources M U hU ho hs st]
  have HE : (W⁻¹)^st.generation*(nativeActualOriginalCenteredResourceB0 M U st.term-
      (1/2:ℝ)*nativeActualOriginalCenteredResourceB0 M U (st.term.retarget 0))=
      (W⁻¹)^st.generation*nativeActualOriginalCenteredResourceB0 M U st.term-
        (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalCenteredResourceB0 M U (st.term.retarget 0)):=by ring
  rw [HE,sub_eq_add_neg]
  apply (abs_add_le _ _).trans
  rw [abs_neg,abs_mul (1/2:ℝ) _,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  exact (add_le_add H0 (mul_le_mul_of_nonneg_left H1 (by norm_num))).trans_eq (by ring)

theorem actual_second_low_full_half_retarget_from_actual_resource_rows_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Rmacro Cx Cerr Ci : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hrows : ActualHistorySecondLowFullResourceB0ModulusOnEveryFinalNetAlong degree (rBound+1)
      Cmass Ccut Couter Rmacro Cx Cerr Ci eps dim M W w) :
    ActualHistorySecondLowFullHalfRetargetB0ModulusOnEveryFinalNetAlong degree rBound
      Cmass Ccut Couter Rmacro Cx Cerr ((3/2:ℝ)*Ci) (fun n=>(3/2:ℝ)*eps n) dim M W w := by
  filter_upwards [Hrows] with n hn
  intro L us hus hstar hret hmesh
  filter_upwards [hn L us hus hstar hret hmesh] with jGrid hg
  dsimp only at hg ⊢
  intro pre mid tail hparts hindex V U hU seed st hP hdegree hmid hV hiV hVstar hs hT hcut houter
    x sourceMass hsourceMass hx hxW hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let price:=Ci*partitionPoint 0 (finiteCutMasses us jGrid) U*(M n).xs*Cerr*
      (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid) pre.length+1/(dim n+1:ℕ))+
    eps n*W n*(M n).xs^2
  let B:=|st.term.coefficient| *nativeResourceScale x (W n) 1 seed*price
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have hgLeaf : g.tree.leaves ≤ rBound+1:=by
    have HH:=st.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target star)
    omega
  have H0:=hg pre mid tail hparts hindex V U st.generation st.tree hU seed st.term hP hdegree
    hmid hV hiV hVstar hs (hT.trans (by omega)) hcut houter x sourceMass hsourceMass hx hxW hmi hms
    Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  have H1:=hg pre mid tail hparts hindex V U st.generation g.tree hU seed (st.term.retarget 0) hP.retarget
    (by simpa only [NativeResourceTerm.retarget_resources] using hdegree) hmid hV hiV hVstar hs hgLeaf
    hcut houter x sourceMass hsourceMass hx hxW hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
  have ho : MassOrdered 0 as:=by dsimp only [as];rw [←hparts];exact finiteCutMasses_ordered us hus jGrid
  have HO:=native_actual_original_full_four_second_low_abs_le (M n) U hU ho hs st (W n) B
    (by exact H0) (by simpa only [NativeResourceTerm.retarget] using H1)
  exact HO.trans_eq (by dsimp only [B,price];ring)

theorem actual_second_low_actual_history_full_half_retarget_B0_modulus_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs c0 : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Ccal Rmacro F Cx : ℝ)
    (hCx : 0 < Cx) (hTemp : 0 ≤ Temp) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hCouter : 0 ≤ Couter) (hCcal : 1 ≤ Ccal)
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0) (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cf Ci : ℝ,0 ≤ Cf ∧ 0 < Ci ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf) ∧
      ∃eps : ℕ→ℝ,(∀n,0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ActualHistorySecondLowFullHalfRetargetB0ModulusOnEveryFinalNetAlong degree rBound Cmass Ccut Couter Rmacro Cx
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Ci eps dim M W w := by
  obtain ⟨Cf,Ci,hCf,hCi,HS,eps,heps,HL,H⟩:=actual_second_low_actual_history_full_resource_B0_modulus_along
    degree (rBound+1) Cmass Ccut Couter Ccal Rmacro F Cx hCx hTemp hCm hCcut hCouter hCcal
    heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hc0 hmargin hcapmargin
    dim hdim root M epsilon shell hepsilon hb hh Hhistory W hcanonical hWlim w Hcompare hw
  refine ⟨Cf,(3/2:ℝ)*Ci,hCf,by positivity,HS,fun n=>(3/2:ℝ)*eps n,?_,?_,?_⟩
  · intro n;exact mul_nonneg (by norm_num) (heps n)
  · simpa only [mul_zero] using HL.const_mul (3/2:ℝ)
  · exact actual_second_low_full_half_retarget_from_actual_resource_rows_along degree rBound
      Cmass Ccut Couter Rmacro Cx (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Ci eps dim M W w H

end OAI.SKFluctuations.Cavity
