module

public import ComparisonSignedCavityActualInitialHigherTaylorCategoryModulusAlong
public import ComparisonSignedCavityActualInitialFullB0OnStrongCutsAlong
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem native_actual_initial_category_bound_partition_star_transport
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as bs : List PositiveMass} {i star star' U depth : ℕ} {W B seedMass : ℝ}
    {cat : NativeActualOtherSourceCategory}
    (hs : star < U) (hs' : star' < U) (hU : U ≤ as.length) (hU' : U ≤ bs.length)
    (hi : i ≤ as.length) (hi' : i ≤ bs.length)
    (hparts : as=bs) (hstar : star=star')
    (H : let K:=nativeContinuumMixedClock n M.bf M.hf as
         let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
         |nativeActualFourOtherCategorySum M U W
           (nativeActualMinimumFourCenteredForest M hs hU W depth
             [nativeActualInitialState as i star seedMass hi]) cat|/(chi*K star) ≤ B) :
    let K:=nativeContinuumMixedClock n M.bf M.hf bs
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks bs (relocatedClock U 0 K))).H 0 0
    |nativeActualFourOtherCategorySum M U W
      (nativeActualMinimumFourCenteredForest M hs' hU' W depth
        [nativeActualInitialState bs i star' seedMass hi']) cat|/(chi*K star') ≤ B := by
  subst bs
  subst star'
  exact H

def ActualInitialHigherTaylorOnStrongGivenCutsAlong
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
        let old:=pre++(mid++tail)
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
        |nativeActualFourOtherCategorySum (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
            [nativeActualInitialState old pre.length (pre.length+mid.length) seedMass (by dsimp only [old];omega)])
          .higherTaylor|/(chi*K (pre.length+mid.length)) ≤
            Ci*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+
              1/(dim n+1:ℕ))+err n*(M n).xs^3

theorem actual_selected_bad_history_initial_higher_Taylor_on_strong_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal Tstar Lwin Cwindow c0 c cK A Rmacro Cx : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) (_hmacro : 0 < Rmacro) (_hRhalf : Rmacro ≤ 1/2) (_hCx : 0 < Cx)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (_hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
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
    ∃Ci : ℝ,0 < Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialHigherTaylorOnStrongGivenCutsAlong depth A Ci err M W w high outer := by
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Hshell : ∀ᶠn in atTop,∃(Tbase eps sh : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase eps sh ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u):=by
    filter_upwards [Hps] with n hn
    exact ⟨Temp,epsilon,shell,((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)),hn.2.1,hn.2.2⟩
  obtain ⟨Ci,hCi,err,herr,Herr,H⟩:=actual_inherited_initial_higher_Taylor_category_modulus_along
    (Cs:=Ccal^2) depth Bclock Temp Cf A (A+1) A cK hTemp hCf hA0.le (by positivity) hA0 hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hc hcouter
    dim hdim M W hcanonical hWlim Hsource hcompare Hshell w hw
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let Cout:=Ci*Cerr+1
  have hCerr:0 ≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have hCout:0 < Cout:=by dsimp only [Cout];positivity
  refine ⟨Cout,hCout,err,herr,Herr,?_⟩
  filter_upwards [H,Hcuts] with n hn hcuts
  intro L us hus hret hmesh hstar hhigh houter hnodes
  have Hmesh:=uniformMasses_mesh_tendsto.eventually (eventually_le_nhds (M n).hxs)
  filter_upwards [hn L us hus hret hmesh hstar,Hmesh] with jGrid hj hmeshFine
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,HcutLo,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.toActualSharpSourceCutGeometry.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper:partitionPoint 0 as U ≤ A*W n:=(partitionPoint_mono as ho HUV.le).trans Houter
  intro pre mid tail hcut hindex hmid hmi
  have HI:pre.length+mid.length<U:=by rw [hindex];exact hs
  have HU:U ≤ (pre++(mid++tail)).length:=by rw [hcut];exact hU
  refine ⟨HI,HU,?_⟩
  intro seedMass
  have Hlow:partitionPoint 0 as (pre.length+1) ≤ (A+1)*(M n).xs:=
    actual_initial_successor_low_cut_mass_le hus hmeshFine hmi
  have Hraw:=hj pre.length (pre.length+1) U
    (by rw [←hindex];omega) hs hU HcutLo Hupper (by omega) (by omega)
    (by rw [←hindex];omega) Hlow hmi Hmass HstarK seedMass
  have hDi:0 ≤ nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ):=by
    dsimp only [nativeOriginalCutLowErrorRadius];positivity
  have HC:=mul_le_mul_of_nonneg_right (show Ci*Cerr ≤ Cout by dsimp only [Cout];linarith)
    (mul_nonneg (sq_nonneg (M n).xs) hDi)
  have Hmajor:=add_le_add_right HC (err n*(M n).xs^3)
  have Hraw': let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          [nativeActualInitialState as pre.length (retainedMassPrefixIndex (w n).star.val as) seedMass
            (by dsimp only [as];rw [←hcut];simp only [List.length_append];omega)]) .higherTaylor|/(chi*K (retainedMassPrefixIndex (w n).star.val as)) ≤
        Cout*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ))+
        err n*(M n).xs^3 := by
    apply Hraw.trans
    convert Hmajor using 1 <;> dsimp only [Cerr,as] <;> ring
  exact native_actual_initial_category_bound_partition_star_transport (M n) hs HI hU HU
    (by rw [←hcut];simp only [List.length_append];omega)
    (by simp only [List.length_append];omega) hcut.symm hindex.symm Hraw'

end OAI.SKFluctuations.Cavity
