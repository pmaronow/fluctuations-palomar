module

public import ComparisonSignedCavityActualFourGaRestorationRateAlong
public import ComparisonSignedCavityActualFourRestorationSeedGeometry
public import ComparisonSignedCavityActualSharpSourceCutReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualInitialRestoredGaOnGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      ∀seedMass : ℝ,
        ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length)
            seedMass (by omega)]).map
          (fun Q=>|nativeActualOriginalFourGaRestorationError (M n) U (W n) Q|)).sum ≤
            err n*(M n).xs^3

theorem actual_inherited_initial_restored_Ga_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal c cK A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,∃(Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase epsilon shell ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialRestoredGaOnGivenCutsAlong depth A err M W w high outer := by
  have hA0 : 0 ≤ A:=zero_le_one.trans hA
  obtain ⟨C,hC,HR⟩:=eventually_actual_shell_history_resource_G_restoration_forest_rate_along
    (D:=D) (Cs:=Ccal^2) dim hdim 1 0 2 depth Bclock Temp Cf A A cK
    hTemp hCf hA0 hA0 hcK hm hdelta hroom hcl hcu hAz hC0 hCt
    (pow_nonneg (zero_le_one.trans hCcal) 2) hc hcouter
  let eta:=actualMassSavingExponent m delta
  let err:=fun n=>C*((dim n+1:ℕ):ℝ)^(-eta/256)
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/256 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,Function.comp_def,mul_zero,neg_div] using Hpow.const_mul C
  refine ⟨err,(fun n=>by dsimp only [err];positivity),Herr,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HR,Hsource,hcompare,Hshell,Hcuts,HW] with n hn hsource hsmall hshell hcuts hW1
  obtain ⟨Tbase,epsilon,shell,ts,hb,hh⟩:=hshell
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hn (M n) Tbase epsilon shell ts hsource hb hh hsmall
    (by rw [←hcanonical];exact hW1) L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  rw [←hcanonical n] at hj
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  obtain ⟨hs,HUV,HV,Hlo,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Hupper : partitionPoint 0 as U ≤ A*W n:=
    (partitionPoint_mono as ho HUV.le).trans Houter
  intro pre mid tail hcut hindex hmid hmi
  have HI : pre.length+mid.length<U:=by rw [hindex];exact hs
  have HU : U ≤ (pre++(mid++tail)).length:=by rw [hcut];exact hU
  refine ⟨HI,HU,?_⟩
  intro seedMass
  rw [←hcut] at hj
  let old:=pre++(mid++tail)
  let i:=pre.length
  let star:=pre.length+mid.length
  have hi : i ≤ star:=by dsimp only [i,star];omega
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) old i star seedMass (hi.trans (HI.le.trans HU))
  have hP : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed old HU seedMass .initial (Or.inl rfl) (hi.trans (HI.le.trans HU)))
  have H:=hj i star U [.initial] st (by simp) rfl
    (nativeActualInitialState_leaves_le old i star seedMass (hi.trans (HI.le.trans HU)))
    hP hi HI HU (by simpa only [hcut] using Hlo) (by simpa only [hcut] using Hupper)
    (by dsimp only [old,star];rw [hcut,hindex];exact Hmass)
    (by dsimp only [old,star];rw [hcut,hindex];exact HstarK)
    (actual_initial_four_seed_high_fork_free i star U hi HI HU seedMass)
    (M n).xs le_rfl (by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale)
    (by simpa only [old,i,hcut] using hmi)
  simp only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,
    nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    NativeResourceMark.savedScale,mul_one] at H
  apply H.trans_eq
  change C*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))*(M n).xs^2*(M n).xs=
    err n*(M n).xs^3
  dsimp only [err,eta]
  ring_nf

end OAI.SKFluctuations.Cavity
