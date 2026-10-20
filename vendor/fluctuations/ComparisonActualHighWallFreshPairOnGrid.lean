module

public import ComparisonActualHighWallPairGridStarSecond
public import ComparisonActualGeneralFourFreshPairReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_high_wall_centered_fresh_pair_abs_le_on_grid
    {n degree : ℕ} {m delta cl cu Az C0 Ct D Bclock A saving Cmass : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {u : PositiveMass} {as : List PositiveMass}
    (H : ActualHighWallSquareResourcePairBudgetsOnGrid degree A saving Cmass M u as)
    (hd : 1 ≤ degree) (hA : 1 ≤ A) (ho : MassOrdered 0 as)
    {i U k : ℕ} {seed : List NativeResourceMark}
    (hseed : seed=[] ∨ seed=[.initial])
    (T : ClockTree (Spin n×Bool) as)
    (P : NativeResourceTerm i (retainedMassPrefixIndex u.val as) T)
    (hP : NativeActualResourceGenerated i (retainedMassPrefixIndex u.val as) U seed k T P)
    (hdegree : seed.length+k ≤ degree)
    (hi : i ≤ retainedMassPrefixIndex u.val as)
    (hs : retainedMassPrefixIndex u.val as < U) (hU : U ≤ as.length)
    (hmass : partitionPoint 0 as i ≤ Cmass*M.data.d) :
    let epsilon:=((n+1:ℕ):ℝ)^(-saving)
    |(M.data.d⁻¹)^k*actualGeneralOriginalCenteredResourceFreshPair M.bf M.hf U ⟨T,P,k⟩| ≤
      2*|P.coefficient| *A^(seed.length+k+1)*
        nativeResourceScale M.data.d M.data.d epsilon seed*epsilon^(k+1)*M.data.d := by
  dsimp only
  let star:=retainedMassPrefixIndex u.val as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let center:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=cutFullVariance n q U 1 1 b h K
  let epsilon:=((n+1:ℕ):ℝ)^(-saving)
  let B:=A*(epsilon*M.data.d)
  have hdpos : 0 < M.data.d:=M.data.hd
  have hApos : 0 < A:=zero_lt_one.trans_le hA
  have heps : 0 < epsilon:=by dsimp only [epsilon];positivity
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have HQ : qfull=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hget (V : ClockTree (Spin n×Bool) as) (Q : NativeResourceTerm i star V)
      (HG : NativeActualResourceGenerated i star U seed k V Q) :
      Q.PairMomentBudget (fullWeight n) (fullFeature n) 0 qfull
        (fun sigma tau=>deletedOverlap n (joinSpin sigma) (joinSpin tau)) center 0
        A M.data.d M.data.d epsilon:=by
    rw [HQ]
    rcases hseed with hzero | hone
    · subst seed
      exact H.1 U i k V Q HG (by simpa only [List.length_nil,zero_add] using hdegree)
        1 1 (by norm_num) (by norm_num)
    · subst seed
      exact H.2 U i k V Q HG (by simpa only [List.length_singleton] using hdegree)
        (hi.trans (hs.le.trans hU)) hmass 1 1 (by norm_num) (by norm_num)
  have HM:=Hget _ (P.retarget 0) hP.retarget
  have HMF:=Hget _ (P.retarget 0).freeze hP.retarget.freeze
  have HD : (nativeFreshAtSlot T 0 P.live.test.target star).tree.disorderExpect
      (fullWeight n) (fullFeature n) 0 qfull
      (fun sigma=>(deletedOverlap n
        (joinSpin (T.atSlot ((nativeFreshAtSlot T 0 P.live.test.target star).restrict sigma) P.live.test.target))
        (joinSpin ((nativeFreshAtSlot T 0 P.live.test.target star).spin sigma))-center star)^2) 0 ≤ B^2:=by
    rw [native_actual_fresh_star_endpoint_second_eq_pair n T ho _ star U (hs.le.trans hU)]
    exact ActualHighWallSquareResourcePairBudgetsOnGrid.star_second_moment H hd U hs hU 1 1 (by norm_num) (by norm_num)
  have HF:=normalized_actual_centered_fresh_pair_moment_abs_le q b h K center T P hP ho hi
    (hs.trans_le hU) A M.data.d M.data.d epsilon B hApos hdpos hdpos heps hB HM HMF HD
  change |(M.data.d⁻¹)^k*actualGeneralOriginalCenteredResourceFreshPair M.bf M.hf U ⟨T,P,k⟩| ≤ _ at HF
  convert HF using 1
  dsimp only [B,epsilon]
  rw [pow_succ,pow_succ]
  ring

 theorem actual_high_wall_four_fresh_pair_abs_le_on_grid
    {n degree : ℕ} {m delta cl cu Az C0 Ct D Bclock A saving Cmass : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {u : PositiveMass} {as : List PositiveMass}
    (H : ActualHighWallSquareResourcePairBudgetsOnGrid degree A saving Cmass M u as)
    (hd : 1 ≤ degree) (hA : 1 ≤ A) (ho : MassOrdered 0 as)
    {i U : ℕ} {seed : List NativeResourceMark}
    (hseed : seed=[] ∨ seed=[.initial])
    (st : NativeActualResourceState (Spin n×Bool) as i (retainedMassPrefixIndex u.val as))
    (hP : NativeActualResourceGenerated i (retainedMassPrefixIndex u.val as) U seed st.generation st.tree st.term)
    (hdegree : seed.length+st.generation ≤ degree)
    (hi : i ≤ retainedMassPrefixIndex u.val as)
    (hs : retainedMassPrefixIndex u.val as < U) (hU : U ≤ as.length)
    (hmass : partitionPoint 0 as i ≤ Cmass*M.data.d) :
    let epsilon:=((n+1:ℕ):ℝ)^(-saving)
    |(M.data.d⁻¹)^st.generation*actualGeneralFourPairContrast M.bf M.hf U st| ≤
      3*|st.term.coefficient| *A^(seed.length+st.generation+1)*
        nativeResourceScale M.data.d M.data.d epsilon seed*epsilon^(st.generation+1)*M.data.d := by
  dsimp only
  let epsilon:=((n+1:ℕ):ℝ)^(-saving)
  let B:=2*|st.term.coefficient| *A^(seed.length+st.generation+1)*
    nativeResourceScale M.data.d M.data.d epsilon seed*epsilon^(st.generation+1)*M.data.d
  have H0:=actual_high_wall_centered_fresh_pair_abs_le_on_grid H hd hA ho hseed st.tree st.term
    hP hdegree hi hs hU hmass
  have H1:=actual_high_wall_centered_fresh_pair_abs_le_on_grid H hd hA ho hseed st.retarget.tree st.retarget.term
    hP.retarget hdegree hi hs hU hmass
  have H1' : |(M.data.d⁻¹)^st.generation*actualGeneralOriginalCenteredResourceFreshPair M.bf M.hf U st.retarget| ≤ B:=by
    simpa only [NativeActualResourceState.retarget,NativeResourceTerm.retarget] using H1
  have HH:=actual_general_four_pair_contrast_abs_le M.bf M.hf U ho st M.data.d B H0 H1'
  convert HH using 1
  dsimp only [B,epsilon]
  ring

end OAI.SKFluctuations.Cavity
