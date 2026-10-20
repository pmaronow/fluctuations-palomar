module

public import ComparisonSignedCavityActualCalibratedInitialPairFeedbackAlong
public import ComparisonActualHighOnlySquareConsumerActualSharpFourTerminalAlong
public import ComparisonActualHighOnlyComparableBandStarBond

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualSusceptibilityCoefficientOnStrongCutsAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (C : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2| ≤ C*(W n)^2

def ActualInitialPairFeedbackResidualOnStrongCutsAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Temp cK Cmass : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star < U,∃hU : U ≤ as.length,
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      ∀(i : ℕ) (hi : i ≤ star),∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as i ≤ Cmass*x →
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ((List.range depth).map (fun d=>
        |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2| *
          |nativeActualFourPairSum_high_only (M n) U (W n)
            (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) d [st])|/
              (Real.exp (-4*Temp)*cK*W n))).sum ≤ err n*x*(M n).xs^2

theorem actual_calibrated_initial_pair_feedback_residual_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp cK Cmass gamma sharp cFirst A Cj : ℝ}
    (depth : ℕ) (hgamma : 0 ≤ gamma) (hsharp : 0 < sharp) (hcK : 0 < cK) (hCj : 0 ≤ Cj)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry_high_only (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A)
    (HJ : ActualSusceptibilityCoefficientOnStrongCutsAlong_high_only Cj M W w high outer)
    (Hpair : ∀d : ℕ,ActualOriginalFourInitialPairForestSavingAlong_high_only 0 d 2 gamma sharp Cmass M W w) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialPairFeedbackResidualOnStrongCutsAlong_high_only depth Temp cK Cmass err M W w high outer := by
  let D0:=Real.exp (-4*Temp)*cK
  have hD0 : 0 < D0:=mul_pos (Real.exp_pos _) hcK
  let rho n:=((dim n+1:ℕ):ℝ)^(-sharp/2)
  let err n:=(depth:ℝ)*(Cj/D0)*rho n
  have hrho n : 0 ≤ rho n:=by dsimp only [rho];positivity
  have Hlim : Tendsto rho atTop (𝓝 0):=by
    simpa only [rho,Function.comp_def,neg_div] using
      (tendsto_rpow_neg_atTop (div_pos hsharp (by norm_num : (0:ℝ) < 2))).comp
        (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  refine ⟨err,(fun n=>by dsimp only [err];positivity),?_,?_⟩
  · simpa only [err,mul_zero] using Hlim.const_mul ((depth:ℝ)*(Cj/D0))
  · have HP:=Filter.eventually_all.mpr (fun d : Fin depth=>Hpair d.val)
    filter_upwards [HP,Hcuts,HJ] with n hnP hcuts hnJ
    have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
    intro L us hus hret hmesh hstar hhigh houter hnodes
    have HG:=Filter.eventually_all.mpr (fun d : Fin depth=>hnP d L us hus hstar hret hmesh)
    filter_upwards [HG,hnJ L us hus hret hmesh hstar hhigh houter hnodes] with jGrid hjP hjJ
    dsimp only at hjP hjJ ⊢
    let as:=finiteCutMasses us jGrid
    let star:=retainedMassPrefixIndex (w n).star.val as
    let U:=retainedMassPrefixIndex (high n).val as
    obtain ⟨hs,HUV,HV,_⟩:=hcuts.finite_net_readout us hus hstar hhigh houter jGrid
    have hU:=HUV.le.trans HV
    refine ⟨hs,hU,?_⟩
    intro i hi x hx hxW hmi
    have hx0:0 ≤ x:=((M n).hxs.trans_le hx).le
    let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
    have hP:NativeActualResourceGenerated i star U [.initial] 0 st.tree st.term:=
      .physical (.seed as hU 0 .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
    have hleaf:=nativeActualInitialState_leaves_le (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
    let ep:=((dim n+1:ℕ):ℝ)^(-gamma)
    have hep:0 ≤ ep:=by dsimp only [ep];positivity
    have hep1:ep ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast;omega) (neg_nonpos.mpr hgamma)
    let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let J:=1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2
    have Hrow d (hd : d∈List.range depth) :
        |J| * |nativeActualFourPairSum_high_only (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) d [st])| /
          (D0*W n) ≤ (Cj/D0)*rho n*x*(M n).xs^2 := by
      have HPd:=hjP ⟨d,List.mem_range.mp hd⟩ U i hi hs hU st.tree st.term hP hleaf x hx hxW hmi
      have HB : |nativeActualFourPairSum_high_only (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) d [st])| ≤
          rho n*x*(ep^d)*((M n).xs^2/W n):=by
        simpa only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,zero_add,rho,ep] using HPd
      have HB' : |nativeActualFourPairSum_high_only (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) d [st])| ≤
          rho n*x*((M n).xs^2/W n):=by
        apply HB.trans
        calc
          rho n*x*(ep^d)*((M n).xs^2/W n) ≤ rho n*x*1*((M n).xs^2/W n) := by
            gcongr
            exact pow_le_one₀ hep hep1
          _ = _ := by ring
      exact actual_closed_susceptibility_pair_feedback_le hW hD0 hCj (hrho n) hx0 hjJ HB'
    have Hsum:=List.sum_le_sum Hrow
    simp only [List.map_const',List.sum_replicate,List.length_range,nsmul_eq_mul] at Hsum
    apply Hsum.trans_eq
    dsimp only [err,D0]
    ring

end OAI.SKFluctuations.Cavity
