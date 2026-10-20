module

public import ComparisonSignedCavityActualInitialSavedResidualAlong
public import ComparisonSignedCavityActualInitialFullB0ResidualAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def nativeActualInitialRestThermalSourceCategories : List NativeActualOtherSourceCategory :=
  [.higherTaylor,.jointLowTwoHigh,.jointLowRestoration,.fourGLowRestoration]

def nativeActualInitialRestThermalCategoryEnvelope
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    {as : List PositiveMass} {i star : ℕ}
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (nativeActualInitialRestThermalSourceCategories.map
    (fun cat=>|nativeActualFourOtherCategorySum M U W rows cat|/(chi*K star))).sum

theorem actual_initial_thermal_residual_eq_full_B0_add_rest
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (hs : star < U) (hU : U ≤ as.length)
    (W : ℝ) (depth : ℕ) (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    ((List.range depth).map (fun d=>nativeActualInitialThermalCategoryEnvelope M U W
      (nativeActualMinimumFourCenteredForest M hs hU W d rows))).sum=
    nativeActualInitialFullB0ResidualEnvelope M hs hU W depth rows+
      ((List.range depth).map (fun d=>nativeActualInitialRestThermalCategoryEnvelope M U W
        (nativeActualMinimumFourCenteredForest M hs hU W d rows))).sum := by
  simp only [nativeActualInitialThermalCategoryEnvelope,nativeActualInitialThermalSourceCategories,
    nativeActualInitialRestThermalCategoryEnvelope,nativeActualInitialRestThermalSourceCategories,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,nativeActualInitialFullB0ResidualEnvelope,
    List.sum_map_add]

def ActualInitialResidualFourThermalModulusOnStrongCutsAlong
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
        ((List.range depth).map (fun d=>nativeActualInitialRestThermalCategoryEnvelope (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]))).sum

theorem actual_selected_bad_history_initial_residual_four_thermal_modulus_along
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
      ActualInitialResidualFourThermalModulusOnStrongCutsAlong depth A Ci err M W w high outer := by
  obtain ⟨eS,heS,hSlim,HS⟩:=actual_selected_bad_history_initial_residual_modulo_thermal_along
    depth hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hdim root M epsilon shell hepsilon hTemp hb hh Hhistory W radius hcanonical hWlim hcompare
    saving hsaving hCj w high outer hw Hsquare HJ Hmixed
    (Hcuts.mono fun _ hn=>hn.toActualSharpSourceCutGeometry)
  obtain ⟨Ci,hCi,eB,heB,hBlim,HB⟩:=actual_selected_bad_history_initial_full_b0_residual_on_given_cuts_along
    depth hA hcK hmacro hRhalf hCx hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hdim root M epsilon shell hepsilon hTemp hb hh Hhistory W radius hcanonical hWlim
    (Eventually.of_forall hcompare) w high outer hw Hcuts
  refine ⟨Ci,hCi,(fun n=>eS n+eB n),(fun n=>add_nonneg (heS n) (heB n)),
    by simpa only [zero_add] using hSlim.add hBlim,?_⟩
  filter_upwards [HS,HB] with n hnS hnB
  intro L us hus hret hmesh hstar hhigh houter hnodes
  filter_upwards [hnS L us hus hret hmesh hstar hhigh houter hnodes,
    hnB L us hus hret hmesh hstar hhigh houter hnodes] with jGrid hjS hjB
  dsimp only at hjS hjB ⊢
  intro pre mid tail hparts hindex hmid hmi
  obtain ⟨hs,hU,HS0⟩:=hjS pre mid tail hparts hindex hmid hmi
  obtain ⟨_,_,HB0⟩:=hjB pre mid tail hparts hindex hmid hmi
  refine ⟨hs,hU,?_⟩
  rw [actual_initial_thermal_residual_eq_full_B0_add_rest] at HS0
  have H:=HB0 0
  nlinarith only [HS0,H]

end OAI.SKFluctuations.Cavity
