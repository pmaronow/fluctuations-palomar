module

public import ComparisonSignedCavityActualInitialFullB0OnStrongCutsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def nativeActualInitialFullB0ResidualEnvelope
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (hs : star<U) (hU : U ≤ as.length)
    (W : ℝ) (depth : ℕ) (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  ((List.range depth).map (fun d=>|nativeActualFourOtherCategorySum M U W
    (nativeActualMinimumFourCenteredForest M hs hU W d xs) .secondLow|/(chi*K star))).sum

def ActualInitialFullB0ResidualOnStrongGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A Ci : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      ∀seedMass : ℝ,
        nativeActualInitialFullB0ResidualEnvelope (M n) hs hU (W n) depth
          [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) seedMass (by omega)] ≤
            Ci*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+
              1/(dim n+1:ℕ))+err n*(M n).xs^3

theorem actual_selected_bad_history_initial_full_b0_residual_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal Tstar Lwin Cwindow c0 c cK A Rmacro Cx : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A Rmacro Cx) :
    ∃Ci : ℝ,0 ≤ Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialFullB0ResidualOnStrongGivenCutsAlong depth A Ci err M W w high outer := by
  have Hlevels d:=actual_selected_bad_history_initial_full_b0_on_strong_given_cuts_along
    d hA hcK hmacro hRhalf hCx hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hdim root M epsilon shell hepsilon hTemp hb hh Hhistory W radius hcanonical hWlim hcompare
    w high outer hw Hcuts
  choose C hC e he0 helim HE using Hlevels
  let Cout:=((List.range depth).map C).sum
  let err n:=((List.range depth).map (fun d=>e d n)).sum
  have hCout : 0 ≤ Cout:=List.sum_nonneg (by
    intro a ha;obtain ⟨d,_,rfl⟩:=List.mem_map.mp ha;exact (hC d).le)
  have herr n : 0 ≤ err n:=List.sum_nonneg (by
    intro a ha;obtain ⟨d,_,rfl⟩:=List.mem_map.mp ha;exact he0 d n)
  have Hlim (ls : List ℕ) : Tendsto (fun n=>(ls.map (fun d=>e d n)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil=>simp only [List.map_nil,List.sum_nil];exact tendsto_const_nhds
    | cons d ds ih=>simpa only [List.map_cons,List.sum_cons,zero_add] using (helim d).add ih
  refine ⟨Cout,hCout,err,herr,Hlim (List.range depth),?_⟩
  have HN:=Filter.eventually_all.mpr (fun d : Fin depth=>HE d.val)
  filter_upwards [HN,Hcuts] with n hn hcuts
  intro L us hus hret hmesh hstar hhigh houter hnodes
  have Hgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>hn d L us hus hret hmesh hstar hhigh houter hnodes)
  filter_upwards [Hgrid] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  obtain ⟨hs,HUV,HV,_,_,_,_,_,_,_,_,_,_⟩:=
    hcuts.toActualSharpSourceCutGeometry.finite_net_readout us hus hstar hhigh houter jGrid
  intro pre mid tail hcut hindex hmid hmi
  have HI : pre.length+mid.length<U:=by rw [hindex];exact hs
  have HU : U ≤ (pre++(mid++tail)).length:=by rw [hcut];exact HUV.le.trans HV
  refine ⟨HI,HU,?_⟩
  intro seedMass
  let old:=pre++(mid++tail)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
  let Di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ)
  have Hrow d (hd : d∈List.range depth) :
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) HI HU (W n) d
          [nativeActualInitialState old pre.length (pre.length+mid.length) seedMass (by dsimp only [old];omega)])
        .secondLow|/(chi*K (pre.length+mid.length)) ≤ C d*(M n).xs^2*Di+e d n*(M n).xs^3:=by
    obtain ⟨_,_,H⟩:=hj ⟨d,List.mem_range.mp hd⟩ pre mid tail hcut hindex hmid hmi
    exact H seedMass
  have Hsum:=List.sum_le_sum Hrow
  simpa only [nativeActualInitialFullB0ResidualEnvelope,Cout,err,
    List.sum_map_add,List.sum_map_mul_right] using Hsum

end OAI.SKFluctuations.Cavity
