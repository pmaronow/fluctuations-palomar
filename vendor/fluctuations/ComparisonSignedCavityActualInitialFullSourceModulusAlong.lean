module

public import ComparisonSignedCavityActualInitialFullResidualPrefixSource
public import ComparisonSignedCavityActualHistoryInitialHigherTaylorOnStrongCutsAlong
public import ComparisonSignedCavityActualHistoryInitialJointLowOnCutsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_initial_full_source_modulus_along
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 c cK A Tstar Lwin Cwindow Cj Rmacro Cx : ℝ}
    (depth : ℕ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
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
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (saving : ℝ) (hsaving : 0 < saving) (hCj : 0 ≤ Cj)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hsquare : ∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w)
    (HJ : ActualSusceptibilityCoefficientOnStrongCutsAlong Cj M W w high outer)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A Rmacro Cx) :
    ∃Ci : ℝ,0 ≤ Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialResidualFullModulusOnStrongCutsAlong depth A Ci err M W w high outer := by
  classical
  obtain ⟨Ci,hCi,eTwo,heTwo,hTwoLim,HTwo⟩:=actual_selected_bad_history_initial_residual_two_thermal_modulus_along
    depth hmacro hRhalf hCx hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0
    hmargin hcapmargin hdim root M epsilon shell hepsilon hTemp hb hh Hhistory W radius hcanonical hWlim
    hcompare saving hsaving hCj w high outer hw Hsquare HJ Hmixed Hcuts
  have Hhigher d:=actual_selected_bad_history_initial_higher_Taylor_on_strong_given_cuts_along
    d hA hcK hc hcouter hmacro hRhalf hCx hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0
    hmargin hcapmargin hdim root M epsilon shell hepsilon hTemp hb hh Hhistory W radius
    hcanonical hWlim (Eventually.of_forall hcompare) w high outer hw Hcuts
  have Hjoint d:=actual_selected_bad_history_initial_joint_LOW_restoration_on_given_cuts_along
    d (zero_lt_one.trans_le hA) hcK hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hmargin hcapmargin
    dim hdim root M epsilon shell hepsilon hTemp hb hh Hhistory W radius hcanonical hWlim
    w high outer hw (Hcuts.mono fun _ hn=>hn.toActualSharpSourceCutGeometry)
  choose C hC eH heH hHlim HH using Hhigher
  choose eJ heJ hJlim HJlow using Hjoint
  let Csum:=((List.range depth).map C).sum
  have hCsum:0 ≤ Csum:=List.sum_nonneg (by
    intro a ha
    obtain ⟨d,_,rfl⟩:=List.mem_map.mp ha
    exact (hC d).le)
  let eRest n:=((List.range depth).map (fun d=>eH d n+eJ d n)).sum
  have heRest n:0 ≤ eRest n:=List.sum_nonneg (by
    intro a ha
    obtain ⟨d,_,rfl⟩:=List.mem_map.mp ha
    exact add_nonneg (heH d n) (heJ d n))
  have Hlim (ls : List ℕ):Tendsto (fun n=>(ls.map (fun d=>eH d n+eJ d n)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil=>simp only [List.map_nil,List.sum_nil];exact tendsto_const_nhds
    | cons d ds ih=>simpa only [List.map_cons,List.sum_cons,zero_add] using ((hHlim d).add (hJlim d)).add ih
  refine ⟨Ci+Csum,add_nonneg hCi hCsum,(fun n=>eTwo n+eRest n),
    (fun n=>add_nonneg (heTwo n) (heRest n)),
    by simpa only [zero_add] using hTwoLim.add (Hlim (List.range depth)),?_⟩
  have HN:=Filter.eventually_all.mpr (fun d : Fin depth=>(HH d.val).and (HJlow d.val))
  filter_upwards [HTwo,HN] with n hnTwo hn
  intro L us hus hret hmesh hstar hhigh houter hnodes
  have Hgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>
    (hn d).1 L us hus hret hmesh hstar hhigh houter hnodes |>.and
      ((hn d).2 L us hus hret hmesh hstar hhigh houter))
  filter_upwards [hnTwo L us hus hret hmesh hstar hhigh houter hnodes,Hgrid] with jGrid hjTwo hj
  dsimp only at hjTwo hj ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  have hxW:(M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  intro pre mid tail hparts hindex hmid hmi
  obtain ⟨hs,hU,HT⟩:=hjTwo pre mid tail hparts hindex hmid hmi
  refine ⟨hs,hU,?_⟩
  have hHigher d:=(hj d).1 pre mid tail hparts hindex hmid hmi
  have hjJ d:=(hj d).2
  let old:=pre++(mid++tail)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) old pre.length (pre.length+mid.length) 0 (by dsimp only [old];omega)
  let Di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ)
  have Hrow d (hd : d∈List.range depth):
      nativeActualInitialTwoThermalCategoryEnvelope (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]) ≤
      C d*(M n).xs^2*Di+(eH d n+eJ d n)*(M n).xs^3 := by
    let fd:Fin depth:=⟨d,List.mem_range.mp hd⟩
    obtain ⟨_,_,BH⟩:=hHigher fd
    have BH0:=BH 0
    have hsNat:retainedMassPrefixIndex (w n).star.val as<U:=by
      rw [←hindex];exact hs
    have hiNat:pre.length ≤ retainedMassPrefixIndex (w n).star.val as:=by
      rw [←hindex];omega
    have hUas:U ≤ as.length:=by dsimp only [as];rw [←hparts];exact hU
    have BJ0:=hjJ fd pre.length hiNat hsNat hUas (M n).xs le_rfl hxW hmi 0
    have BJ:=actual_initial_seed_function_reindex as old hparts
      (retainedMassPrefixIndex (w n).star.val as) (pre.length+mid.length) hindex
      hiNat hsNat hUas (by omega) hs hU
      (fun bs st hs' hU' rows=>
        |nativeActualFourOtherCategorySum (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs' hU' (W n) d rows) .jointLowRestoration|/
        ((scalarTerminal.schedule (scalarBoundaryClocks bs (relocatedClock U 0
          (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf bs)))).H 0 0*
            nativeContinuumMixedClock (dim n) (M n).bf (M n).hf bs st))
      (eJ d n*(M n).xs*(M n).xs^2) BJ0
    change |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]) .higherTaylor|/
      (chi*K (pre.length+mid.length)) ≤ C d*(M n).xs^2*Di+eH d n*(M n).xs^3 at BH0
    change |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]) .jointLowRestoration|/
      (chi*K (pre.length+mid.length)) ≤ eJ d n*(M n).xs*(M n).xs^2 at BJ
    simp only [nativeActualInitialTwoThermalCategoryEnvelope,nativeActualInitialTwoThermalSourceCategories,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    change _+_ ≤ _
    nlinarith only [BH0,BJ]
  have Hsum:=List.sum_le_sum Hrow
  simp only [List.sum_map_add,List.sum_map_mul_right] at Hsum
  have Hsum':
      ((List.range depth).map (fun d=>nativeActualInitialTwoThermalCategoryEnvelope (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]))).sum ≤
      Csum*(M n).xs^2*Di+eRest n*(M n).xs^3:=by
    simpa only [Csum,eRest,List.sum_map_add] using Hsum
  apply HT.trans
  have Hpaid:=add_le_add_left Hsum' (Ci*(M n).xs^2*Di+eTwo n*(M n).xs^3)
  convert Hpaid using 1 <;> dsimp only [Di,st,old,U,as] <;> ring

end OAI.SKFluctuations.Cavity
