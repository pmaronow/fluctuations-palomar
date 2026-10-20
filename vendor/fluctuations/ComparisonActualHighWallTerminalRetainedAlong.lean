module

public import ComparisonActualHighWallTerminalDepth
public import ComparisonActualHighWallTerminalOnGrid
public import ComparisonActualGeneralConstantChildrenTerminal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000

def ActualHighWallFourTerminalBudgetsOnGrid
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (depth : ℕ) (saving Cmass : ℝ)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (u : PositiveMass) (as : List PositiveMass) : Prop :=
  let star:=retainedMassPrefixIndex u.val as
  ∀(U i : ℕ) (_hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (seed : List NativeResourceMark),
    NativeActualResourceGenerated i star U seed st.generation st.tree st.term →
    ((seed=[] ∧ st.generation=1) ∨ (seed=[.initial] ∧ st.generation=0)) →
    partitionPoint 0 as i ≤ Cmass*M.data.d → st.tree.leaves ≤ 3 →
    |((actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth [st]).map
      (actualGeneralFourStateResponse M.bf M.hf U M.data.d)).sum| ≤
      2*|st.term.coefficient| *(((n+1:ℕ):ℝ)^(-saving)*M.data.d^3)

def ActualHighWallFourTerminalOnRetainedMasterAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (saving Cmass : ℝ)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,
    ∀L : ℕ,((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    ∀extra : List PositiveMass,(∀u∈extra,u.val ≤ 1) →
    ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ (∀u∈extra,u∈us) ∧
      (∀u∈uniformMasses L,u∈us) ∧ (w n).star∈us ∧
      ∀ᶠj : ℕ in atTop,
        ActualHighWallFourTerminalBudgetsOnGrid depth saving Cmass (M n) (w n).star
          (finiteCutMasses us j)

theorem exists_actual_high_wall_four_cubic_terminal_of_pair_budgets_along
    {m delta cl cu Az C0 Ct D Bclock gamma cK Cmass : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hgamma : 0 < gamma) (hcK : 0 < cK)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hWlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,cK*(M n).data.d ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val)
    (Hp : ∀degree : ℕ,0 < degree → ∃A : ℝ,1 ≤ A ∧
      ActualHighWallSquareResourcePairBudgetOnRetainedMasterAlong degree A gamma Cmass dim M w) :
    ∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
      ∀depth : ℕ,threshold ≤ depth →
        ActualHighWallFourTerminalOnRetainedMasterAlong depth saving Cmass dim M w := by
  obtain ⟨threshold,hth,saving,hsaving,Hrate⟩:=exists_actual_high_wall_cubic_terminal_depth
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hC0 hgamma
  refine ⟨threshold,hth,saving,hsaving,?_⟩
  intro depth hdepth
  obtain ⟨A,hA,HA⟩:=Hp (1+depth) (by omega)
  let Cweight:=Bclock/(Real.exp (-4*Bclock)*cK)
  have hB : 0 ≤ Bclock:=(M 0).data.hTpos.le.trans (M 0).hT
  have hCweight : 0 ≤ Cweight:=by dsimp only [Cweight];positivity
  let Cenv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
    Cweight 3 3 depth*A^(1+depth)*(2*Bclock)*nativeActualGInsertionCost (3+6*depth)
  have hCenv : 0 ≤ Cenv:=by
    have HC:=nativeActualWeightedFrontierCost_nonneg nativeActualOriginalFourGCenteredBranches hCweight 3 3 depth
    have HG:=nativeActualGInsertionCost_nonneg (3+6*depth)
    dsimp only [Cenv];positivity
  have Hd:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [HA,hw,Hd,hdim.eventually (Hrate Cenv hCenv)] with n hn hnw hnd hnrate
  intro L hmesh extra hextra
  obtain ⟨us,hus,hretain,hcoarse,hstar,Hgrid⟩:=hn L hmesh extra hextra
  refine ⟨us,hus,hretain,hcoarse,hstar,?_⟩
  filter_upwards [Hgrid] with j hj
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have hK : cK*(M n).data.d ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star:=by
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho
      (w n).star (finiteCutMasses_nodes us j hstar)]
    exact hnw
  change ActualHighWallFourTerminalBudgetsOnGrid depth saving Cmass (M n) (w n).star as
  dsimp only [ActualHighWallFourTerminalBudgetsOnGrid]
  intro U i hi hs hU st seed hst hseed hmass hr
  have Hraw:=actual_high_wall_weighted_terminal_abs_le_on_grid
    (M n) (w n).star ho hi hs hU hcK hK hA hgamma hnd depth hj st hst hseed hmass hr
  have Hfrozen:=actual_high_wall_weighted_terminal_abs_le_on_grid
    (M n) (w n).star ho hi hs hU hcK hK hA hgamma hnd depth hj st.freeze hst.freeze
    hseed hmass hr
  simp only [NativeActualResourceState.freeze,NativeResourceTerm.freeze,abs_neg] at Hfrozen
  have HR:=hnrate (M n) depth hdepth
  rw [hfixed n] at HR
  have Hraw' : _ ≤ |st.term.coefficient| *(((dim n+1:ℕ):ℝ)^(-saving)*(M n).data.d^3):=
    Hraw.trans (by
      change |st.term.coefficient| *Cenv*(((dim n+1:ℕ):ℝ)^(-gamma))^depth ≤ _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left HR (abs_nonneg st.term.coefficient))
  have Hfrozen' : _ ≤ |st.term.coefficient| *(((dim n+1:ℕ):ℝ)^(-saving)*(M n).data.d^3):=
    Hfrozen.trans (by
      change |st.term.coefficient| *Cenv*(((dim n+1:ℕ):ℝ)^(-gamma))^depth ≤ _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left HR (abs_nonneg st.term.coefficient))
  unfold actualGeneralFourCenteredForest
  rw [nativeActualFourCenteredForest_singleton_response]
  exact (abs_add_le _ _).trans ((add_le_add Hraw' Hfrozen').trans_eq (by ring))

end OAI.SKFluctuations.Cavity
