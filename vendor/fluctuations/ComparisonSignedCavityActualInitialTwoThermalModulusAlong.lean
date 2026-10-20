module

public import ComparisonSignedCavityActualInitialFourThermalModulusAlong
public import ComparisonSignedCavityActualHistoryInitialJointHighCategoriesAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 50000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def nativeActualInitialTwoThermalSourceCategories : List NativeActualOtherSourceCategory :=
  [.higherTaylor,.jointLowRestoration]

def nativeActualInitialTwoThermalCategoryEnvelope
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    {as : List PositiveMass} {i star : ℕ}
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (nativeActualInitialTwoThermalSourceCategories.map
    (fun cat=>|nativeActualFourOtherCategorySum M U W rows cat|/(chi*K star))).sum

theorem native_actual_initial_four_thermal_envelope_eq_two_add_joint_HIGH
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    {as : List PositiveMass} {i star : ℕ}
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualInitialRestThermalCategoryEnvelope M U W rows=
      nativeActualInitialTwoThermalCategoryEnvelope M U W rows+
      |nativeActualFourOtherCategorySum M U W rows .jointLowTwoHigh|/(chi*K star)+
      |nativeActualFourOtherCategorySum M U W rows .fourGLowRestoration|/(chi*K star) := by
  simp only [nativeActualInitialRestThermalCategoryEnvelope,nativeActualInitialRestThermalSourceCategories,
    nativeActualInitialTwoThermalCategoryEnvelope,nativeActualInitialTwoThermalSourceCategories,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

theorem native_actual_initial_category_bound_star_transport
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star star' U depth : ℕ} {W B seedMass : ℝ}
    {cat : NativeActualOtherSourceCategory}
    (hs : star < U) (hs' : star' < U) (hU : U ≤ as.length) (hi : i ≤ as.length)
    (hstar : star=star')
    (H : let K:=nativeContinuumMixedClock n M.bf M.hf as
         let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
         |nativeActualFourOtherCategorySum M U W
           (nativeActualMinimumFourCenteredForest M hs hU W depth
             [nativeActualInitialState as i star seedMass hi]) cat|/(chi*K star) ≤ B) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativeActualFourOtherCategorySum M U W
      (nativeActualMinimumFourCenteredForest M hs' hU W depth
        [nativeActualInitialState as i star' seedMass hi]) cat|/(chi*K star') ≤ B := by
  subst star'
  exact H

def ActualInitialResidualTwoThermalModulusOnStrongCutsAlong
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
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) (pre++(mid++tail))
        pre.length (pre.length+mid.length) 0 (by omega)
      |nativeActualMinimumFourResidualSum (M n) hs hU (W n) depth [st]| ≤ Ci*(M n).xs^2*
          (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ))+
        err n*(M n).xs^3+
        ((List.range depth).map (fun d=>nativeActualInitialTwoThermalCategoryEnvelope (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]))).sum
theorem actual_selected_bad_history_initial_residual_two_thermal_modulus_along
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
      ActualInitialResidualTwoThermalModulusOnStrongCutsAlong depth A Ci err M W w high outer := by
  classical
  obtain ⟨Ci,hCi,eFour,heFour,hFourLim,HFour⟩:=actual_selected_bad_history_initial_residual_four_thermal_modulus_along
    depth hmacro hRhalf hCx hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0
    hmargin hcapmargin hdim root M epsilon shell hepsilon hTemp hb hh Hhistory W radius hcanonical hWlim
    hcompare saving hsaving hCj w high outer hw Hsquare HJ Hmixed Hcuts
  have hA0:0 ≤ A:=zero_le_one.trans hA
  have hxW:∀ᶠn in atTop,(M n).xs ≤ W n:=Eventually.of_forall (fun n=>by
    rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale)
  have Hlevels d:=actual_selected_bad_history_initial_joint_HIGH_categories_rate_along
    (Cs:=Ccal^2) d Bclock Temp A A cK hTemp hA0 hA0 hcK hm hdelta hroom hcl hcu hAz hC0 hCt
    (sq_nonneg Ccal) hc hcouter hc0 hmargin hcapmargin dim hdim root M
    W hcanonical hWlim epsilon shell hepsilon hb hh Hhistory (fun n=>(M n).xs)
    (Eventually.of_forall (fun _=>le_rfl)) hxW (Eventually.of_forall hcompare) w
  choose Cf hCf Hsource Hkind using Hlevels
  choose eH heH hHlim HH using (fun d=>Hkind d .lowTwoHigh)
  choose eG heG hGlim HG using (fun d=>Hkind d .fourGLow)
  let eJoint n:=((List.range depth).map (fun d=>eH d n+eG d n)).sum
  have heJoint n:0 ≤ eJoint n:=List.sum_nonneg (by
    intro a ha
    obtain ⟨d,_,rfl⟩:=List.mem_map.mp ha
    exact add_nonneg (heH d n) (heG d n))
  have Hlim (ls : List ℕ):Tendsto (fun n=>(ls.map (fun d=>eH d n+eG d n)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil=>simp only [List.map_nil,List.sum_nil];exact tendsto_const_nhds
    | cons d ds ih=>simpa only [List.map_cons,List.sum_cons,zero_add] using ((hHlim d).add (hGlim d)).add ih
  refine ⟨Ci,hCi,(fun n=>eFour n+eJoint n),(fun n=>add_nonneg (heFour n) (heJoint n)),
    by simpa only [zero_add] using hFourLim.add (Hlim (List.range depth)),?_⟩
  have HN:=Filter.eventually_all.mpr (fun d : Fin depth=>(HH d.val).and (HG d.val))
  filter_upwards [HFour,Hcuts,HN] with n hnFour hnCuts hn
  intro L us hus hret hmesh hstar hhigh houter hnodes
  have Hgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>
    (hn d).1 L us hus hret hmesh hstar |>.and ((hn d).2 L us hus hret hmesh hstar))
  filter_upwards [hnFour L us hus hret hmesh hstar hhigh houter hnodes,Hgrid] with jGrid hjFour hj
  dsimp only at hjFour hj ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨_,HUV,HV,HcutLo,HstarMass,HouterMass,_,_,_,_,_,HstarK,_⟩:=
    hnCuts.toActualSharpSourceCutGeometry.finite_net_readout us hus hstar hhigh houter jGrid
  have HcutUp:partitionPoint 0 as U ≤ A*W n:=
    (partitionPoint_mono as ho HUV.le).trans HouterMass
  intro pre mid tail hparts hindex hmid hmi
  obtain ⟨hs,hU,HF⟩:=hjFour pre mid tail hparts hindex hmid hmi
  refine ⟨hs,hU,?_⟩
  have hjH d:=(hj d).1
  have hjG d:=(hj d).2
  change 2*c*W n ≤ partitionPoint 0 (finiteCutMasses us jGrid) U at HcutLo
  change partitionPoint 0 (finiteCutMasses us jGrid) U ≤ A*W n at HcutUp
  rw [←hparts] at hjH hjG hindex HcutLo HcutUp HstarMass HstarK hmi
  rw [←hindex] at HstarMass HstarK
  let old:=pre++(mid++tail)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) old pre.length (pre.length+mid.length) 0 (by dsimp only [old];omega)
  have Hrow d (hd : d∈List.range depth):
      nativeActualInitialRestThermalCategoryEnvelope (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]) ≤
      nativeActualInitialTwoThermalCategoryEnvelope (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st])+
        (eH d n+eG d n)*(M n).xs^3 := by
    let fd:Fin depth:=⟨d,List.mem_range.mp hd⟩
    have hsOld:retainedMassPrefixIndex (w n).star.val (pre++(mid++tail))<U := by
      rw [←hindex];exact hs
    have hiOld:pre.length ≤ retainedMassPrefixIndex (w n).star.val (pre++(mid++tail)) := by
      rw [←hindex];omega
    have HM:partitionPoint 0 (pre++(mid++tail))
        (retainedMassPrefixIndex (w n).star.val (pre++(mid++tail))) ≤ A*W n := by
      rw [←hindex];exact HstarMass
    have HK:cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (pre++(mid++tail))
        (retainedMassPrefixIndex (w n).star.val (pre++(mid++tail))) := by
      rw [←hindex];exact HstarK
    have BH0:=hjH fd pre.length U hiOld hsOld hU HcutLo HcutUp hmi HM HK 0
    have BG0:=hjG fd pre.length U hiOld hsOld hU HcutLo HcutUp hmi HM HK 0
    have BH:=native_actual_initial_category_bound_star_transport (M n) hsOld hs hU
      (by omega) hindex.symm BH0
    have BG:=native_actual_initial_category_bound_star_transport (M n) hsOld hs hU
      (by omega) hindex.symm BG0
    change |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]) .jointLowTwoHigh|/
      (chi*K (pre.length+mid.length)) ≤ eH d n*((M n).xs*(M n).xs^2) at BH
    change |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]) .fourGLowRestoration|/
      (chi*K (pre.length+mid.length)) ≤ eG d n*((M n).xs*(M n).xs^2) at BG
    rw [native_actual_initial_four_thermal_envelope_eq_two_add_joint_HIGH]
    nlinarith only [BH,BG]
  have Hsum:=List.sum_le_sum Hrow
  simp only [List.sum_map_add,List.sum_map_mul_right] at Hsum
  have Hsum':
      ((List.range depth).map (fun d=>nativeActualInitialRestThermalCategoryEnvelope (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]))).sum ≤
      ((List.range depth).map (fun d=>nativeActualInitialTwoThermalCategoryEnvelope (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]))).sum+eJoint n*(M n).xs^3 := by
    simpa only [eJoint,List.sum_map_add] using Hsum
  apply HF.trans
  have Hpaid:=add_le_add_left Hsum'
    (Ci*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid) pre.length+
      1/(dim n+1:ℕ))+eFour n*(M n).xs^3)
  convert Hpaid using 1 <;> dsimp only [st,old,U,as] <;> ring

end OAI.SKFluctuations.Cavity
