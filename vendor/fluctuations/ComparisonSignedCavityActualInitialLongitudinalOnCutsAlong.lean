module

public import ComparisonSignedCavityActualInitialLongitudinalForestAlong
public import ComparisonSignedCavityActualStrongSharpSourceCutReadout
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def nativeActualInitialLongitudinalEnvelope
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    {as : List PositiveMass} {i star : ℕ}
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  |nativeActualFourOtherCategorySum M U W rows .longitudinalLeft|/(chi*K star)+
    |nativeActualFourOtherCategorySum M U W rows .longitudinalRight|/(chi*K star)

def ActualInitialLongitudinalOnGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star < U,∃hU : U ≤ as.length,
      ∀(i : ℕ) (hi : i ≤ star) (x : ℝ),(M n).xs ≤ x → x ≤ W n →
        partitionPoint 0 as i ≤ A*x →
        nativeActualInitialLongitudinalEnvelope (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
            [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))]) ≤ err n*(x*(M n).xs^2)

theorem actual_inherited_initial_longitudinal_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal c cK A : ℝ}
    (depth : ℕ) (hA : 0 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hdim : Tendsto dim atTop atTop)
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
      ActualInitialLongitudinalOnGivenCutsAlong depth A err M W w high outer := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_initial_longitudinal_category_rate_along
    dim hdim depth Bclock Temp Cf A A cK hTemp hCf hA hA hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hc hcouter
  let eta:=actualMassSavingExponent m delta/256
  let err n:=2*C*((dim n+1:ℕ):ℝ)^(-eta)
  have hlim : Tendsto err atTop (𝓝 0):=by
    have H0:=(tendsto_rpow_neg_atTop (div_pos (actualMassSavingExponent_pos hm hdelta)
      (by norm_num : (0:ℝ)<256))).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
    simpa only [err,eta,Function.comp_def,mul_zero] using H0.const_mul (2*C)
  refine ⟨err,(fun n=>by dsimp only [err];positivity),hlim,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,Hshell,Hcuts,hcompare,HW] with n hn hsClocks hshell hcuts hsmall hW1
  obtain ⟨Tbase,epsilon,shell,ts,hb,hh⟩:=hshell
  intro L us hus hret hmesh hstar hhigh houter
  have HW1 : (M n).canonicalDirectTestBandScale ≤ 1:=by rw [←hcanonical];exact hW1
  filter_upwards [hn (M n) Tbase epsilon shell ts hsClocks hb hh hsmall HW1 L us hus hret hmesh]
    with jGrid hj
  dsimp only at hj ⊢
  rw [←hcanonical n] at hj
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,Hlo,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper : partitionPoint 0 as U ≤ A*W n:=
    (partitionPoint_mono as ho HUV.le).trans Houter
  refine ⟨hs,hU,?_⟩
  intro i hi x hx hxW hmi
  have HL:=hj i star U hi hs hU Hlo Hupper Hmass HstarK x hx hxW hmi false
  have HR:=hj i star U hi hs hU Hlo Hupper Hmass HstarK x hx hxW hmi true
  have HB:=add_le_add HL HR
  apply HB.trans_eq
  change C*((dim n+1:ℕ):ℝ)^(-eta)*(M n).xs^2*x+
    C*((dim n+1:ℕ):ℝ)^(-eta)*(M n).xs^2*x=err n*(x*(M n).xs^2)
  dsimp only [err]
  ring

end OAI.SKFluctuations.Cavity
