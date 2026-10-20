module

public import ComparisonSignedCavityActualGeneratedGammaFirstHighProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeGammaFirstHighVariation (r : ℕ) : ℝ :=
  pairForkVariation (r+2)/2*(4*((r:ℝ)+1)+1)

theorem nativeGammaFirstHighVariation_nonneg (r : ℕ) : 0 ≤ nativeGammaFirstHighVariation r := by
  have H:=pairForkVariation_nonneg (r+2)
  unfold nativeGammaFirstHighVariation
  positivity

def nativeActualGeneratedFirstHigh {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (star U : ℕ)
    (P : NativeGeneratedTest T) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  nativeGammaProjectedFirstHighDisplacement T P.target star U
    (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h
    (nativeContinuumMixedClock n M.bf M.hf as) A
    (nativeRestGeneratedTestValue T P A (nativePhysicalResourceCenter n M.bf M.hf as))

theorem actual_minimum_generated_first_high_empty_live
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as)
    (hempty : P₀.live.test.edges=[]) :
    nativeActualGeneratedFirstHigh M T star U P₀.live.test=0 := by
  unfold nativeActualGeneratedFirstHigh
  dsimp only
  have HE (A : Spin n→Spin n→ℝ) (C : ℕ→ℝ) :
      nativeRestGeneratedTestValue T P₀.live.test A C=fun _=>1 := by
    funext σ
    simp only [nativeRestGeneratedTestValue,hempty,List.map_nil,List.prod_nil]
  rw [HE,actual_minimum_generated_Gamma_first_high_eq_paired_source M hP hi hs ho]
  simp only [native_rest_projected_paired_constant_zero,retained_signed_jets_zero_test,
    mul_zero,List.map_const',List.sum_replicate,nsmul_zero]

theorem eventually_actual_minimum_generated_first_high_bounded_degree
    (degree : ℕ) (Bclock Temp Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let W:=M.canonicalDirectTestBandScale
        ∀(T : ClockTree (Spin n×Bool) as) (i star U kGen rBound : ℕ)
          (seed : List NativeResourceMark) (P₀ : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed kGen T P₀ → P₀.live.test.edges.length ≤ degree →
          i ≤ star → star < U → U ≤ as.length → T.leaves ≤ rBound →
          W ≤ Rmacro/2 → (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4 →
          partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
          (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp
        |nativeActualGeneratedFirstHigh M T star U P₀.live.test| ≤
          C*sourceMonomialScale M.xs W (nativeGeneratedCompleteInitial P₀.live.test i)*W^2*
            nativeGammaFirstHighVariation rBound*(T.forkCost R+edgeBudget 0 as R) := by
  classical
  have Hchoose (j : Fin degree):=eventually_actual_minimum_generated_Gamma_first_high_profile
    (D:=D) (j.val+1) (by omega) Bclock Temp Cmass Ccal Rmacro F hTemp hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  choose Cs hCs H using Hchoose
  let C:=1+∑j : Fin degree,Cs j
  have hsum : 0 ≤ ∑j : Fin degree,Cs j:=Finset.sum_nonneg (fun j _=>(hCs j).le)
  have hC : 0 < C:=by dsimp only [C];linarith
  have hCj j : Cs j ≤ C := by
    have Hj:=Finset.single_le_sum (s:=Finset.univ) (f:=Cs) (fun k _=>(hCs k).le) (Finset.mem_univ j)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [Filter.eventually_all.mpr H] with n hn
  intro M hb hh hxs hcompare L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr (fun j : Fin degree=>hn j M hb hh hxs hcompare L us hus hret hmesh)] with k hk
  dsimp only at hk ⊢
  intro T i star U kGen rBound seed P₀ hP hdegree hi hs hlen hT hmacroW hsmall hmi hms
  let W:=M.canonicalDirectTestBandScale
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf (finiteCutMasses us k)
    (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp
  have ho:=finiteCutMasses_ordered us hus k
  have hx:=M.hxs
  have hW:=M.canonical_direct_test_band_pos
  have hscale : 0 ≤ sourceMonomialScale M.xs W (nativeGeneratedCompleteInitial P₀.live.test i) := by
    unfold sourceMonomialScale
    positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcost:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  by_cases hzero : P₀.live.test.edges.length=0
  · rw [actual_minimum_generated_first_high_empty_live M hP hi hs ho (List.length_eq_zero_iff.mp hzero),abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le hscale) (sq_nonneg W))
      (nativeGammaFirstHighVariation_nonneg rBound)) hcost
  · let j : Fin degree:=⟨P₀.live.test.edges.length-1,by omega⟩
    have Hrow:=hk j T i star U kGen rBound seed P₀ hP (by dsimp only [j];omega)
      hi hs hlen hT hmacroW hsmall hmi hms
    have HC:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCj j) hscale) (sq_nonneg W))
      (nativeGammaFirstHighVariation_nonneg rBound)) hcost
    apply le_trans _ HC
    convert Hrow using 1 <;>
      dsimp only [nativeActualGeneratedFirstHigh,nativePhysicalResourceCenter,nativeGammaFirstHighVariation,W,R]
    all_goals first
      | rfl
      | ring

end OAI.SKFluctuations.Cavity
