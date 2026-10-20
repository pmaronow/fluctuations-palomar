module

public import ComparisonSignedCavitySecondLowActualFreshFullB0BudgetAlong
public import ComparisonSignedCavitySecondLowActualFreshReplacementBudgetAlong
public import ComparisonActualHighOnlyLowB0UnobservedCompleteConsumerSourceAlong
public import ComparisonActualHighOnlyLowB0WholeObservedPhysicalSourceAlong
public import ComparisonActualHighOnlyLowB0OldCBaselineConsumerSourceAlong
public import ComparisonActualHighOnlyLowB0ResourceConsumerInterfacesSourceAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
open NativeOverlapMinimum (ActualSlowWindowChoice)
attribute [local instance] Classical.propDecidable
attribute [local instance] nativeSecondLowSlotFintype
private theorem low_b0_initial_second_low_list_two_cut_decomposition {α : Type} (as : List α)
    (i star : ℕ) (hi : i<star) (hstar : star≤as.length) :
    ∃pre mid tail : List α,as=pre++(mid++tail) ∧ pre.length=i ∧ pre.length+mid.length=star := by
  refine ⟨as.take i,(as.drop i).take (star-i),as.drop star,?_,?_,?_⟩
  · have H : i+(star-i)=star:=by omega
    have HD:=List.drop_take_append_drop as i (star-i)
    rw [H] at HD
    rw [HD,List.take_append_drop]
  · simp only [List.length_take,Nat.min_eq_left (by omega : i≤as.length)]
  · simp only [List.length_take,List.length_drop,Nat.min_eq_left (by omega : star-i≤as.length-i)]
    omega

private theorem low_b0_initial_second_low_power_succ_le {n : ℕ} (hn : 1≤n) {eta : ℝ} (heta : 0≤eta) :
    (n:ℝ)^(-eta)≤(2:ℝ)^eta*((n+1:ℕ):ℝ)^(-eta) := by
  have hnr : (1:ℝ)≤n:=by exact_mod_cast hn
  have hn0 : 0<(n:ℝ):=by linarith
  have hN0 : 0<((n+1:ℕ):ℝ):=by positivity
  have H:=Real.rpow_le_rpow_of_nonpos hN0
    (show ((n+1:ℕ):ℝ)≤2*(n:ℝ) by push_cast;linarith) (neg_nonpos.mpr heta)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hn0.le] at H
  have HE : (2:ℝ)^eta*(2:ℝ)^(-eta)=1:=by
    rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]
    simp
  have HM:=mul_le_mul_of_nonneg_left H (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) eta)
  simpa only [←mul_assoc,HE,one_mul] using HM

def ActualSecondLowFreshFullB0BudgetOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (saving eta Cmass Ccut Couter Cerr Cinitial Cmoving Csaved : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i V U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (hU : U≤as.length),
          0<V → i<V → V ≤ star → star<U → NativePersistentLowForks i star U T →
          partitionPoint 0 as V≤Ccut*(M n).xs → T.leaves≤rBound →
          partitionPoint 0 as U≤Couter*W n → W n≤(M n).R (partitionPoint 0 as U) →
          (M n).R (partitionPoint 0 as star)≤(M n).R (partitionPoint 0 as U)/2 →
          (M n).z≤(M n).R (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),(M n).xs≤x → x≤W n →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e) →
        ∀s : T.Slot,
          let g:=nativeFreshAtSlot T 0 s star
          let P:=(G.canonicalHighOnlySource (M n) forms).restProduct
          let Pg:=fun old=>P (g.restRestrict old)
          let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let p0:=sourceMonomialScale x (W n) initial
          let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ)
          let rho:=(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
            partitionPoint 0 as U/(dim n+1:ℕ)
          |nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
            χ^2*nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s star hU P|≤
            Cinitial*partitionPoint 0 as U*(M n).xs*Cerr*di*p0+
            16*((dim n+1:ℕ):ℝ)^(-saving)*W n*(M n).xs^2*p0+
            Cmoving*W n*Cerr*rho*p0+
            Csaved*((dim n+1:ℕ):ℝ)^(-eta)*W n*(M n).xs^2*p0

theorem actual_second_low_fresh_full_B0_budget_along_high_only
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    (hCcal : 1≤Ccal) (heta : 0≤eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cinitial Cmoving Csaved : ℝ,0<Cinitial ∧ 0<Cmoving ∧ 0<Csaved ∧
      ActualSecondLowFreshFullB0BudgetOnEveryFinalNetAlong_high_only degree rBound
        (actualMassSavingExponent m delta/32) eta Cmass Ccut Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cinitial Cmoving Csaved dim M W w := by
  obtain ⟨Ci,Cm,hCi,hCmRate,HU⟩:=actual_second_low_unobserved_total_budget_along_high_only degree (rBound+1) Cmass Ccut Couter
    hTemp hCf hCm hCcut hCouter hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource Hcutoff hw
  let Ccommon:=Cmass+Couter+1
  have hCommon : 0≤Ccommon:=by dsimp [Ccommon];linarith
  obtain ⟨Co,hCo,HO⟩:=eventually_actual_minimum_inherited_second_low_whole_observed_saved_rate_high_only
    (D:=D) degree rBound Bclock Temp Cf Ccommon Ccal hTemp hCf hCommon hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Ci,Cm,(2:ℝ)^eta*Co,hCi,hCmRate,mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hCo,?_⟩
  filter_upwards [HU,hdim.eventually HO,Hsource,Hcompare,HW1,hdim.eventually (eventually_ge_atTop (1:ℕ)),Hcutoff] with n hnU hnO HS hcompare hW1 hn hnCutoff
  have hxW : (M n).xs≤W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  have hW : 0<W n:=(M n).hxs.trans_le hxW
  have hWdef : W n=max (M n).xs (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)):=by
    rw [hcanonical]
    rfl
  intro L us hus hstar hret hmesh
  filter_upwards [hnU L us hus hstar hret hmesh,
    hnO (M n) hnCutoff.1 hnCutoff.2 HS (hxW.trans hW1) hcompare L us hus hret hmesh] with jGrid hgridU hgridO
  dsimp only [ActualSecondLowUnobservedTotalBudgetOnEveryFinalNetAlong_high_only] at hgridU
  dsimp only at hgridU hgridO ⊢
  rw [←hWdef] at hgridO
  generalize hAs : finiteCutMasses us jGrid=as at hgridU hgridO ⊢
  intro i V U T hU hV hiV hVstar hstarU hpersistent hcut hleaves houter hWU hRstar hz
    G forms initial x hxsx hxW hmass s
  let star:=retainedMassPrefixIndex (w n).star.val as
  have hiStar : i<star:=lt_of_lt_of_le hiV hVstar
  obtain ⟨pre,mid,tail,rfl,hpre,hstarLen⟩:=low_b0_initial_second_low_list_two_cut_decomposition as i star hiStar
    (hstarU.le.trans hU)
  have ho : MassOrdered 0 (pre++(mid++tail)):=hAs ▸ finiteCutMasses_ordered us hus jGrid
  let as:=pre++(mid++tail)
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let g:=nativeFreshAtSlot T 0 s star
  let Gfresh:=G.retainOnMarked 0 g (nativeFreshAtSlot_mem T 0 s star)
  let P:=(G.canonicalHighOnlySource (M n) forms).restProduct
  let Pg:=fun old=>P (g.restRestrict old)
  have HP : (Gfresh.canonicalHighOnlySource (M n) forms).restProduct=Pg:=by
    funext τ
    exact G.retained_canonical_restProduct_high_only (M n) forms 0 g (nativeFreshAtSlot_mem T 0 s star) τ
  have Hpersistent : NativePersistentLowForks i star U g.tree:=hpersistent.freshStar 0 s
  have Hleaves : g.tree.leaves≤rBound+1:=
    (T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 s star)).trans (Nat.add_le_add_right hleaves 1)
  have HmassFresh : ∀e,Gfresh.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e:=by
    intro e
    rw [ActualNaturalBoundaryShape.retained_source_mass]
    exact hmass e
  have Hsplit : g.tree.splitIndex (g.embed s) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (by omega)]
  have BU:=hgridU i V U g.tree hU hV hiV hVstar hstarU Hpersistent hcut Hleaves houter
    Gfresh forms initial x hxsx hxW HmassFresh (g.embed s) g.mark Hsplit
  rw [HP] at BU
  have HmassStar : partitionPoint 0 as (pre.length+mid.length)≤Ccommon*W n:=by
    rw [hstarLen]
    have HM:=(partitionPoint_mono as ho hstarU.le).trans houter
    apply HM.trans
    exact mul_le_mul_of_nonneg_right (by dsimp [Ccommon];linarith : Couter≤Ccommon) hW.le
  have HmassOld : ∀e,G.sourceLowMass e≤Ccommon*sourceFactorScale x (W n) initial e:=by
    intro e
    apply (hmass e).trans
    exact mul_le_mul_of_nonneg_right (by dsimp [Ccommon];linarith : Cmass≤Ccommon)
      (source_factor_scale_pos ((M n).hxs.trans_le hxsx) hW initial e).le
  have BO:=hgridO pre mid tail rfl HmassStar T s U hU (by omega) (by omega) hleaves
    (by rw [hstarLen,hpre];exact hpersistent) hWU (by simpa only [hstarLen] using hRstar) hz
    G forms initial x hxsx hxW HmassOld
  rw [hstarLen] at BO
  let p0:=sourceMonomialScale x (W n) initial
  have hp0 : 0≤p0:=by
    dsimp only [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos ((M n).hxs.trans_le hxsx) hW initial e).le
  have Hpow:=low_b0_initial_second_low_power_succ_le hn heta
  have Hsaved: |(∑j : Fin 8,nativeSecondLowClassLedger (dim n) q U b h K g.tree hU Pg (g.embed s) g.mark j true/2)-
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s star hU P|≤
      ((2:ℝ)^eta*Co)*((dim n+1:ℕ):ℝ)^(-eta)*W n*(M n).xs^2*p0 := by
    apply BO.trans
    have HM:=mul_le_mul_of_nonneg_left Hpow hCo.le
    have HR:=mul_le_mul_of_nonneg_right HM (show 0≤W n*(M n).xs^2*p0 by positivity)
    simpa only [p0,nativeSecondLowInheritedSavedMixedClock,mul_assoc,mul_left_comm,mul_comm] using HR
  have Hjoint:=native_second_low_joint_ledger_half_eq_observed_unobserved (dim n) q U b h K g.tree ho hU Pg
    (g.embed s) g.mark (Hsplit ▸ hstarU)
  have Hsource : nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s star hU P=
    ((∑j : Fin 8,nativeSecondLowClassLedger (dim n) q U b h K g.tree hU Pg (g.embed s) g.mark j true/2)-
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s star hU P)+
      (∑j : Fin 8,nativeSecondLowClassLedger (dim n) q U b h K g.tree hU Pg (g.embed s) g.mark j false/2) := by
    rw [Hjoint]
    ring
  rw [Hsource]
  apply (abs_add_le _ _).trans
  apply (add_le_add Hsaved BU).trans_eq
  ring

theorem actual_second_low_fresh_B0_modulo_c_replacement_budget_along_high_only
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    (hCcal : 1≤Ccal) (heta : 0≤eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cinitial Cmoving Csaved Cstar : ℝ,0<Cinitial ∧ 0<Cmoving ∧ 0<Csaved ∧ 0<Cstar ∧
      ActualSecondLowFreshB0ReplacementBudgetOnEveryFinalNetAlong_high_only degree rBound
        (actualMassSavingExponent m delta/32) eta Cmass Ccut Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Cinitial Cmoving Csaved Cstar dim M W w := by
  obtain ⟨Ci,Cm,Cs,hCi,hCmRate,hCs,HF⟩:=actual_second_low_fresh_full_B0_budget_along_high_only degree rBound
    Cmass Ccut Couter Ccal hTemp hCf hCm hCcut hCouter hCcal heta
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource Hcutoff Hcompare hw
  obtain ⟨Cb,Cstar,hCb,hCstar,HB⟩:=actual_second_low_occupied_old_c_baseline_budget_along_high_only degree rBound
    Cmass Ccut Couter hTemp hCf hCm hCcut hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim w Hsource Hcutoff hw
  refine ⟨Ci+Cb,Cm,Cs,16+Cstar,add_pos hCi hCb,hCmRate,hCs,by linarith,?_⟩
  filter_upwards [HF,HB] with n hnF hnB
  intro L us hus hstar hret hmesh
  filter_upwards [hnF L us hus hstar hret hmesh,hnB L us hus hstar hret hmesh] with jGrid hgridF hgridB
  dsimp only at hgridF hgridB ⊢
  intro i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter hWU hRstar hz
    G forms initial x hxsx hxW hmass s
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let g:=nativeFreshAtSlot T 0 s star
  let P:=(G.canonicalHighOnlySource (M n) forms).restProduct
  let Pg:=fun old=>P (g.restRestrict old)
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hfull:=hgridF i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter hWU hRstar hz
    G forms initial x hxsx hxW hmass s
  have Hbase:=hgridB i V U T hU hiV hVstar hstarU hT hpersistent hcut houter
    G forms initial x hxsx hxW hmass s
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Hchi:|chi|≤1:=native_second_low_original_chi_abs_le_one ho U K
  have Hchi2:|chi|^2≤1:=by nlinarith [abs_nonneg chi]
  have Hscaled:|chi^2*nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s star hU P|≤
      |nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s star hU P|:=by
    rw [abs_mul,abs_pow]
    exact (mul_le_mul_of_nonneg_right Hchi2 (abs_nonneg _)).trans_eq (one_mul _)
  have HS:=Hscaled.trans Hbase
  have Hjoin:=native_second_low_fresh_occupied_unweighted_eq_old_baseline_add_replacement
    (dim n) q U b h K T ho s star hstarU hU P
  have HE:nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
      chi^2*nativeSecondLowFreshOccupiedCReplacementSource (dim n) q U b h K T s star hU P=
      (nativeSecondLowJointLedger (dim n) q U b h K g.tree Pg [g.embed s,g.mark]/2-
        chi^2*nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s star hU P)+
      chi^2*nativeSecondLowFreshOccupiedOldCBaselineSource (dim n) q U b h K T s star hU P:=by
    rw [Hjoin]
    ring
  rw [HE]
  apply (abs_add_le _ _).trans
  apply (add_le_add Hfull HS).trans_eq
  ring

end OAI.SKFluctuations.Cavity
