module

public import ComparisonActualHighWallSquarePairRetainedAlong
public import ComparisonActualGeneralWeightedClockTerminal
public import ComparisonActualHighWallUniformForestHighProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem actual_high_wall_weighted_terminal_abs_le_on_grid
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock saving cK Cmass A : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (u : PositiveMass) {as : List PositiveMass} (ho : MassOrdered 0 as)
    {i U : ℕ} (hi : i ≤ retainedMassPrefixIndex u.val as)
    (hs : retainedMassPrefixIndex u.val as < U) (hU : U ≤ as.length)
    (hcK : 0 < cK) (hstarK : cK*M.data.d ≤ nativeContinuumMixedClock n M.bf M.hf as
      (retainedMassPrefixIndex u.val as)) (hA : 1 ≤ A) (hsaving : 0 < saving)
    (hd1 : M.data.d ≤ 1) (depth : ℕ)
    (Hpair : ActualHighWallSquareResourcePairBudgetsOnGrid (1+depth) A saving Cmass M u as)
    (st : NativeActualResourceState (Spin n×Bool) as i (retainedMassPrefixIndex u.val as))
    {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i (retainedMassPrefixIndex u.val as) U
      seed st.generation st.tree st.term)
    (hseed : (seed=[] ∧ st.generation=1) ∨ (seed=[.initial] ∧ st.generation=0))
    (hmass : partitionPoint 0 as i ≤ Cmass*M.data.d) (hr : st.tree.leaves ≤ 3) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let weight:=fun parent tag=>nativeOriginalClockParentWeight M.data.d U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)
    let Cweight:=Bclock/(Real.exp (-4*Bclock)*cK)
    let Cenv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
      Cweight 3 3 depth*A^(1+depth)*(2*Bclock)*nativeActualGInsertionCost (3+6*depth)
    |((nativeActualWeightedFrontier (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
      nativeActualOriginalFourGCenteredBranches weight depth st).map
      (actualGeneralFourStateResponse M.bf M.hf U M.data.d)).sum| ≤
      |st.term.coefficient| *Cenv*(((n+1:ℕ):ℝ)^(-saving))^depth := by
  dsimp only
  let star:=retainedMassPrefixIndex u.val as
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Gamma:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (parent : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight M.data.d U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)
  let Cweight:=Bclock/(Real.exp (-4*Bclock)*cK)
  let eps:=((n+1:ℕ):ℝ)^(-saving)
  have hB : 0 ≤ Bclock:=M.data.hTpos.le.trans M.hT
  have hCweight : 0 ≤ Cweight:=by dsimp only [Cweight];positivity
  have heps : 0 < eps:=by dsimp only [eps];positivity
  have heps1 : eps ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (show 1 ≤ n+1 by omega)) (neg_nonpos.mpr hsaving.le)
  have hlen : ∀b∈nativeActualOriginalFourGCenteredBranches,b.2.length ≤ 3:=
    nativeActualOriginalFourGCenteredBranches_length
  have hcount : ∀b∈nativeActualOriginalFourGCenteredBranches,
      nativeActualExpansionMarkedCount b.2=1:=by
    simp [nativeActualOriginalFourGCenteredBranches_eq,nativeActualExpansionMarkedCount,
      NativeActualExpansionOp.markedIncrement]
  have hGamma (Q : NativeHighSwitchState (Spin n×Bool) as) (p : MarkedPlacement Q.tree)
      (_hp : p∈Q.tree.markedAttach 0) : |Gamma Q p| ≤ 1:=
    nativeOriginalHighRowGamma_abs_le_one ho U K Q p
  have hweight Q z (_hz : z∈nativeActualOriginalFourGCenteredBranches) :
      |weight Q z.1| ≤ Cweight:=
    M.fixed_four_parent_weight_bound ho hs hU M.data.hd hcK hstarK Q z.1
  have htotal : ∀v∈Icc (0:ℝ) 1,(M.hf v:ℝ)+(M.bf v:ℝ) ≤ Bclock:=
    fun v hv=>(M.data.total_clock_le M.alpha v hv).trans M.hT
  have hg : st.generation ≤ 1:=by rcases hseed with ⟨_,hg⟩|⟨_,hg⟩ <;> omega
  have hdegree : seed.length+st.generation=1:=by
    rcases hseed with ⟨hs,hg⟩|⟨hs,hg⟩ <;> simp [hs,hg]
  have hscale : nativeResourceScale M.data.d M.data.d eps seed ≤ 1:=by
    rcases hseed with ⟨rfl,_⟩|⟨rfl,_⟩
    · simp [nativeResourceScale]
    · simpa only [nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
        NativeResourceMark.savedScale,mul_one] using hd1
  have Hbudget (Q) (hQ : Q∈nativeActualWeightedFrontier Gamma hs (hs.le.trans hU)
      nativeActualOriginalFourGCenteredBranches weight depth st) :
      Q.term.PairMomentBudget (fullWeight n) (fullFeature n) 0 q
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.bf M.hf as) 0 A M.data.d M.data.d eps:=by
    have HG:=nativeActualWeightedFrontier_valid Gamma hs (hs.le.trans hU)
      nativeActualOriginalFourGCenteredBranches weight depth st hst Q hQ
    have HD:=nativeActualWeightedFrontier_generation Gamma hs (hs.le.trans hU)
      nativeActualOriginalFourGCenteredBranches weight 1 hcount depth st Q hQ
    simp only [mul_one] at HD
    rcases hseed with ⟨rfl,hg⟩|⟨rfl,hg⟩
    · exact Hpair.1 U i Q.generation Q.tree Q.term HG (by omega) 1 1 (by norm_num) (by norm_num)
    · exact Hpair.2 U i Q.generation Q.tree Q.term HG (by omega) (hi.trans (hs.le.trans hU))
        hmass 1 1 (by norm_num) (by norm_num)
  have HT:=actual_general_weighted_clock_frontier_terminal_abs_le_of_pair_budgets
    M.bf M.hf K (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hB htotal ho
    Gamma hGamma hi hs hU nativeActualOriginalFourGCenteredBranches weight hCweight hweight
    3 hlen 1 hcount depth st hst 3 hr 0 q 0 0 q 0 A M.data.d M.data.d eps
    (zero_lt_one.trans_le hA) M.data.hd M.data.hd heps Hbudget Hbudget
  dsimp only at HT
  have Hpow : eps^(st.generation+depth) ≤ eps^depth:=by
    rw [pow_add]
    exact mul_le_of_le_one_left (pow_nonneg heps.le _) (pow_le_one₀ heps.le heps1)
  have Hscale0 : 0 ≤ nativeResourceScale M.data.d M.data.d eps seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro a ha
    obtain ⟨mark,_,rfl⟩:=List.mem_map.mp ha
    exact (mark.savedScale_pos M.data.hd M.data.hd heps).le
  have HS : nativeResourceScale M.data.d M.data.d eps seed*eps^(st.generation+depth) ≤ eps^depth:=
    (mul_le_mul_of_nonneg_right hscale (pow_nonneg heps.le _)).trans (by simpa using Hpow)
  have HC : 0 ≤ nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cweight 3 3 depth:=
    nativeActualWeightedFrontierCost_nonneg _ hCweight _ _ _
  have Hsave:=mul_le_mul_of_nonneg_left HS
    (show 0 ≤ |st.term.coefficient| *nativeActualWeightedFrontierCost
      nativeActualOriginalFourGCenteredBranches Cweight 3 3 depth*A^(1+depth)*
      (2*Bclock)*nativeActualGInsertionCost (3+6*depth) by
        have HG:=nativeActualGInsertionCost_nonneg (3+6*depth);positivity)
  have Hd : seed.length+(st.generation+depth*1)=1+depth:=by omega
  rw [Hd] at HT
  simp only [mul_one] at HT
  change |((nativeActualWeightedFrontier Gamma hs (hs.le.trans hU)
    nativeActualOriginalFourGCenteredBranches weight depth st).map
    (actualGeneralFourStateResponse M.bf M.hf U M.data.d)).sum| ≤ _ at HT
  have Hidx : 3+2*depth*3=3+6*depth:=by omega
  rw [Hidx] at HT
  apply HT.trans
  convert Hsave using 1 <;> ring

end OAI.SKFluctuations.Cavity
