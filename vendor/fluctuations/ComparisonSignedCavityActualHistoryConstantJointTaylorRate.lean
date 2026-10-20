module

public import ComparisonSignedCavityActualConstantFreshTaylorRateAlong
public import ComparisonSignedCavityActualConstantFreshRestorationRatesAlong
public import ComparisonSignedCavityConstantInheritedLowRestorationStarRateAlong
public import ComparisonSignedCavitySecondLowActualHistoryConstantB0VanishingAlong
public import ComparisonSignedCavityActualConstantJointRestoration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 30000000

theorem actual_selected_bad_history_constant_joint_Taylor_rate_along
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Ccompare c0 c : ℝ}
    (Ccut : ℝ) (hTemp : 0≤Temp) (hCcut : 0 < Ccut) (hCompare : 0≤Ccompare)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hc0 : 0 < c0) (hc : 0 < c) (hcouter : 2*cu*(Az+1)≤c)
    (hmargin : delta/4<3*m-99*delta) (hcapmargin : 100*delta<(1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0≤epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n))
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (w n).star∈us →
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) star
        ∀U : ℕ,star<U → U≤as.length → 2*c*W n≤partitionPoint 0 as U →
          partitionPoint 0 as U≤ min (Ccut*W n) 1 →
          |nativeActualJointRestoredForwardTaylorError (dim n) q U b h K S g.tree (fun _=>1)
            (g.embed (singleSlot as)) g.mark|≤err n*(W n*(M n).xs^2) := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Hshell : ∀ᶠn in atTop,∃(Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase epsilon shell ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u):=by
    filter_upwards [Hps] with n hn
    exact ⟨Temp,epsilon,shell,((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)),hn.2.1,hn.2.2⟩
  obtain ⟨eT,heT,HT⟩:=actual_inherited_constant_fresh_full_Taylor_rate_along
    (Cs:=Ccompare) (Cwindow:=Cs) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare hc hcouter dim hdim
    M W hcanonical hWlim Hsource hsmall Hshell w hw
  obtain ⟨C2,hC2,H2⟩:=eventually_actual_shell_history_constant_fresh_C_two_HIGH_rate_along
    (Cs:=Ccompare) dim hdim Bclock Temp Cf Ccut hTemp hCf hCcut.le
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare hc hcouter
  obtain ⟨C4,hC4,H4⟩:=eventually_actual_shell_history_constant_fresh_FOUR_G_LOW_rate_along
    (Cs:=Ccompare) dim hdim Bclock Temp Cf Ccut hTemp hCf hCcut.le
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare hc hcouter
  have HL:=actual_inherited_constant_low_restoration_star_rate_along
    2 Bclock Temp Cf Ccut hTemp hCf hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim Hsource w hw
  obtain ⟨eB,heB0,heB,HB⟩:=actual_second_low_actual_history_constant_B0_vanishing_along
    Ccut hTemp hCcut.le hCompare hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hmargin hcapmargin
    dim hdim root M epsilon shell hepsilon hb hh Hhistory W hcanonical hWlim w hw hsmall
  let eta:=actualMassSavingExponent m delta
  let err:=fun n=>eB n+|eT n|+(C2+C4)*((dim n+1:ℕ):ℝ)^(-eta/256)+((dim n+1:ℕ):ℝ)^(-eta/32)
  have Hpow (d : ℝ) (hd : 0 < d) :=(tendsto_rpow_neg_atTop (div_pos
    (actualMassSavingExponent_pos hm hdelta) hd)).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    have H:=((heB.add heT.abs).add ((Hpow 256 (by norm_num)).const_mul (C2+C4))).add
      (Hpow 32 (by norm_num))
    simpa only [err,eta,Function.comp_def,abs_zero,zero_mul,mul_zero,add_zero,neg_div] using H
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HT,H2,H4,HL,HB,Hsource,Hshell,hsmall,HW1] with n hnT hn2 hn4 hnL hnB hnSource hnShell hnSmall hnW
  rcases hnShell with ⟨Tbase,epsilon',shell',ts,hb',hh'⟩
  have hW1 : (M n).canonicalDirectTestBandScale≤1:=by simpa only [←hcanonical] using hnW
  have hxW : (M n).xs≤W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  intro L us hus hstar hret hmesh
  filter_upwards [hnT L us hus hret hmesh hstar,
    hn2 (M n) Tbase epsilon' shell' ts hnSource hb' hh' hnSmall hW1 L us hus hret hmesh,
    hn4 (M n) Tbase epsilon' shell' ts hnSource hb' hh' hnSmall hW1 L us hus hret hmesh,
    hnL L us hus hret hmesh hstar,hnB L us hus hstar hret hmesh]
      with jGrid hgridT hgrid2 hgrid4 hgridL hgridB
  dsimp only at hgridT hgrid2 hgrid4 hgridL hgridB ⊢
  intro U hs hU hcutlo hcut
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let T:=single (S:=Spin (dim n)×Bool) as
  let s : T.Slot:=singleSlot as
  let g:=nativeFreshAtSlot T 0 s star
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves≤2:=by
    have H:=T.markedAttach_leaves 0 _ (nativeFreshAtSlot_mem T 0 s star)
    simpa only [T,g,single_leaves_exact] using H
  have hsplit : g.tree.splitIndex (g.embed s) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (hs.le.trans hU)]
  have haz : g.tree.splitIndex (g.embed s) g.mark<U:=hsplit.trans_lt hs
  have HTay:=hgridT U hs hU hcutlo hcut 0 (g.embed s) g.mark
  have HC2:=hgrid2 star U hs hU (by simpa only [←hcanonical] using hcutlo)
    (by simpa only [←hcanonical] using hcut.trans (min_le_left _ _)) 0 (g.embed s) g.mark haz
  have HC4:=hgrid4 star U hs hU (by simpa only [←hcanonical] using hcutlo)
    (by simpa only [←hcanonical] using hcut.trans (min_le_left _ _)) 0 (g.embed s) g.mark
  have HCL:=hgridL U g.tree hU hg (hcut.trans (min_le_left _ _)) (g.embed s) g.mark hsplit hs
  have HB0:=hgridB U hU hs (hcut.trans (min_le_left _ _))
  have HBsource : (1/2:ℝ)*nativeRetainedCenteredCoefficient (dim n) q U b h K g.tree
      (fun _=>1) [g.embed s,g.mark] 2 0=
      nativeSecondLowJointLedger (dim n) q U b h K g.tree (fun _=>1) [g.embed s,g.mark]/2:=by
    rw [native_second_low_centered_eq_scalar_subtraction (dim n) q U b h K g.tree ho (fun _=>1)
      (g.embed s) g.mark hU haz,←native_second_low_joint_ledger_eq_scalar_subtraction
        (dim n) q U b h K g.tree ho (fun _=>1) [g.embed s,g.mark]]
    ring
  have hprice : 0≤W n*(M n).xs^2:=mul_nonneg ((M n).hxs.trans_le hxW).le (sq_nonneg _)
  have HTay' :=HTay.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hprice)
  have Habs : |nativeActualJointRestoredForwardTaylorError (dim n) q U b h K S g.tree (fun _=>1)
      (g.embed s) g.mark|≤
      |nativeSecondLowJointLedger (dim n) q U b h K g.tree (fun _=>1) [g.embed s,g.mark]/2|+
      |nativeActualTaylorRemainder (dim n) q U b h K g.tree (fun _=>1) (g.embed s) g.mark|+
      |nativeCenteredLowGammaHighSecondRemainder (dim n) q U b h K S g.tree (fun _=>1) (g.embed s) g.mark|+
      |nativeCenteredLowGammaLowRestoration (dim n) q U b h K S g.tree (fun _=>1) (g.embed s) g.mark|+
      |nativeOriginalGKernelLowRestoration (dim n) q U b h K S g.tree (fun _=>1) (g.embed s) g.mark
        (restCenteredLowKernel (dim n) U b S)|:=by
    unfold nativeActualJointRestoredForwardTaylorError nativeActualHigherAllocatedRemainder
    rw [HBsource]
    exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  have Htotal:=add_le_add (add_le_add (add_le_add (add_le_add HB0 HTay') HC2) HCL) HC4
  apply Habs.trans (Htotal.trans_eq _)
  dsimp only [err,eta]
  simp only [NativeOverlapContext.N,←hcanonical,neg_div]
  ring

end OAI.SKFluctuations.Cavity
