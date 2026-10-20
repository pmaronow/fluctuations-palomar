module

public import ComparisonActualGeneralGammaHighSecondPairedSource
public import ComparisonActualHighWallGeneratedPairedGammaHighSecondRow
public import ComparisonSignedCavityPairedCurrentForkLedger

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_generated_Gamma_high_second_profile
    (a rBound : ℕ) (ha : 0 < a) (Bclock Cmass Rmacro F : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let W:=M.data.d
        ∀(T : ClockTree (Spin n×Bool) as) (i star U kGen : ℕ)
          (seed : List NativeResourceMark) (P₀ : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed kGen T P₀ → P₀.live.test.edges.length=a →
          i ≤ star → star < U → U ≤ as.length → T.leaves ≤ rBound →
          W ≤ Rmacro/2 → (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4 →
          partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
        let center:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
        let R:=M.data.highErrorEnvelope M.alpha as U
        |nativeGammaProjectedHighSecondRestoration T P₀.live.test.target star U q b h K A
          (nativeRestGeneratedTestValue T P₀.live.test A center)| ≤
          C*M.data.d^a*W^2*
            (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_generated_paired_gamma_high_second_row
    (D:=D) a (rBound+2) ha Bclock Cmass Rmacro F hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
  let Cfinal:=(C/2)*(4*((rBound:ℝ)+1)+1)+1
  have hCfinal : 0 < Cfinal:=by dsimp only [Cfinal];positivity
  refine ⟨Cfinal,hCfinal,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T i star U kGen seed P₀ hP hdegree hi hs hlen hT hmacroW hsmall hmi hms
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let W:=M.data.d
  let R:=M.data.highErrorEnvelope M.alpha as U
  let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  let center:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let P:=nativeRestGeneratedTestValue T P₀.live.test A center
  let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
  let E:=fun p : MarkedPlacement g.tree=>fullScalarCutGamma p.tree U K (p.embed (g.embed P₀.live.test.target)) p.mark*
    nativeRestPayloadHighSecondIntegral n q U b h K p.tree
      (nativeRestProjectedPairedTest T P₀.live.test.target star A P p)
  let B:=C*M.data.d^a*W^2
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hx:=M.hxs
  have hW:=M.data.hd
  have hB : 0 ≤ B:=by
    dsimp only [B]
    positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ M.data.hTpos.le)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hlo j (hj : j<U) : R j=0:=by
    simp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have HE p (hp : p∈g.tree.markedAttach 0) : |E p| ≤ B*(p.tree.forkCost R+edgeBudget 0 as R) := by
    have hcost:=mul_nonneg hB (add_nonneg (p.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR))
    by_cases hhigh : U ≤ p.tree.splitIndex (p.embed (g.embed P₀.live.test.target)) p.mark
    · by_cases hne : p.mark≠p.embed (g.embed P₀.live.test.target)
      · have HG:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P₀.live.test.target star)
        have HP:=g.tree.markedAttach_leaves 0 p hp
        exact hk T P₀.live.test i star U P₀.live.ancestry hdegree hi hs hlen
          hmacroW hsmall hmi hms p hp (by omega) hhigh hne
      · have hself:=not_ne_iff.mp hne
        dsimp only [E]
        rw [native_rest_projected_paired_self_zero T _ star A P p hself,
          actual_general_rest_payload_high_second_integral_zero M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) p.tree ho U,mul_zero,abs_zero]
        exact hcost
    · dsimp only [E]
      rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hlen (lt_of_not_ge hhigh),zero_mul,abs_zero]
      exact hcost
  have Hsum:=native_paired_current_rows_high_profile_le T ho P₀.live.test.target hs hT R hR hlo E hB HE
  rw [actual_general_generated_Gamma_high_second_eq_paired_source M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hP hi hs ho A P]
  have Hrow : |(1/2:ℝ)*((g.tree.markedAttach 0).map (fun p=>p.coeff*E p)).sum| ≤
      (C/2*(4*((rBound:ℝ)+1)+1))*
        M.data.d^a*W^2*
          (T.forkCost R+edgeBudget 0 as R) := by
    convert Hsum using 1
    dsimp only [B]
    ring
  have hscale : 0 ≤ M.data.d^a := by
    exact pow_nonneg M.data.hd.le _
  have Hprice : C/2*(4*((rBound:ℝ)+1)+1) ≤ Cfinal := by dsimp only [Cfinal];linarith
  have HC:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right Hprice hscale) (sq_nonneg W))
    (add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR))
  have Hfinal:=Hrow.trans HC
  simpa only [E,g,K,q,b,h,W,R,as,mul_assoc] using Hfinal

end OAI.SKFluctuations.Cavity
