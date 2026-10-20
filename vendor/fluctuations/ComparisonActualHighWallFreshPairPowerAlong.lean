module

public import ComparisonActualHighWallFreshPairMasterAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

def ActualHighWallFreshPairPowerBudgetsOnGrid
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (depth : ℕ) (A saving Cmass cK : ℝ)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (u : PositiveMass) (as : List PositiveMass) : Prop :=
  ActualHighWallSquareResourcePairBudgetsOnGrid (1+depth) A saving Cmass M u as ∧
    ∀level : ℕ,level ≤ depth → ∀_ho : MassOrdered 0 as,
    ∀(U : ℕ) (hs : retainedMassPrefixIndex u.val as < U) (hU : U ≤ as.length),
      cK*M.data.d ≤ nativeContinuumMixedClock n M.bf M.hf as (retainedMassPrefixIndex u.val as) →
    (|actualGeneralFourPairSum M.bf M.hf U M.data.d
      (actualGeneralFourCenteredForest (n:=n) M.bf M.hf hs hU M.data.d level
        (actualGeneralConstantSourceChildren (n:=n) M.bf M.hf as
          (retainedMassPrefixIndex u.val as) U hs hU))| ≤ ((n+1:ℕ):ℝ)^(-saving/2)*M.data.d) ∧
    ∀(i : ℕ) (hi : i ≤ retainedMassPrefixIndex u.val as),
      partitionPoint 0 as i ≤ Cmass*M.data.d → ∀seedMass : ℝ,
    |actualGeneralFourPairSum M.bf M.hf U M.data.d
      (actualGeneralFourCenteredForest (n:=n) M.bf M.hf hs hU M.data.d level
        [nativeActualInitialState (S:=Spin n×Bool) as i (retainedMassPrefixIndex u.val as)
          seedMass (hi.trans (hs.le.trans hU))])| ≤ ((n+1:ℕ):ℝ)^(-saving/2)*M.data.d^2

theorem eventually_actual_high_wall_fresh_pair_power_budget_of_grid
    {depth : ℕ} {m delta cl cu Az C0 Ct D Bclock A saving Cmass cK : ℝ}
    (hB : 0 ≤ Bclock) (hA : 1 ≤ A) (hsaving : 0 < saving) (hcK : 0 < cK) :
    ∀ᶠn : ℕ in atTop,
    ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
    ∀(u : PositiveMass) (as : List PositiveMass),
      ActualHighWallFreshPairForestBudgetsOnGrid depth A saving Cmass cK M u as →
        ActualHighWallFreshPairPowerBudgetsOnGrid depth A saving Cmass cK M u as := by
  let CW:=Bclock/(Real.exp (-4*Bclock)*cK)
  let C3:=fun level=>36*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches CW 3 3 level*A^(level+2)
  let C2:=fun level=>6*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches CW 3 2 level*A^(level+2)
  let cost:=fun level=>C3 level+C2 level
  let Cenv:=1+∑level∈Finset.range (depth+1),cost level
  have hCW : 0 ≤ CW:=by dsimp only [CW];positivity
  have hC3 level : 0 ≤ C3 level:=by
    have HV:=nativeActualWeightedFrontierCost_nonneg nativeActualOriginalFourGCenteredBranches hCW 3 3 level
    dsimp only [C3];positivity
  have hC2 level : 0 ≤ C2 level:=by
    have HV:=nativeActualWeightedFrontierCost_nonneg nativeActualOriginalFourGCenteredBranches hCW 3 2 level
    dsimp only [C2];positivity
  have hcost level : 0 ≤ cost level:=add_nonneg (hC3 level) (hC2 level)
  have Hbound level (hlevel : level ≤ depth) : C3 level ≤ Cenv ∧ C2 level ≤ Cenv:=by
    have Hsum:=Finset.single_le_sum (fun l _=>hcost l)
      (Finset.mem_range.mpr (show level < depth+1 by omega))
    have Hsum' : cost level ≤ Cenv:=by dsimp only [Cenv];linarith only [Hsum]
    exact ⟨(by dsimp only [cost] at Hsum';linarith only [Hsum',hC2 level]),
      (by dsimp only [cost] at Hsum';linarith only [Hsum',hC3 level])⟩
  have HC:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=saving) (s:=saving/2) (by linarith) 0 Cenv)
  filter_upwards [HC] with n hn
  intro M u as H
  have Hsave : Cenv*((n+1:ℕ):ℝ)^(-saving) ≤ ((n+1:ℕ):ℝ)^(-saving/2):=by
    simpa only [Function.comp_apply,pow_zero,mul_one,neg_div] using hn
  let eps:=((n+1:ℕ):ℝ)^(-saving)
  have heps : 0 < eps:=by dsimp only [eps];positivity
  have heps1 : eps ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (show 1 ≤ n+1 by omega)) (neg_nonpos.mpr hsaving.le)
  have Hpow (k : ℕ) : eps^(k+1) ≤ eps:=by
    rw [pow_succ]
    exact mul_le_of_le_one_left heps.le (pow_le_one₀ heps.le heps1)
  refine ⟨H.1,?_⟩
  intro level hlevel ho U hs hU hK
  have HH:=H.2 level hlevel ho U hs hU hK
  dsimp only at HH ⊢
  have hb:=Hbound level hlevel
  have H3 : C3 level*eps^(level+2) ≤ ((n+1:ℕ):ℝ)^(-saving/2):=by
    calc
      _ ≤ C3 level*eps:=mul_le_mul_of_nonneg_left (Hpow (level+1)) (hC3 level)
      _ ≤ Cenv*eps:=mul_le_mul_of_nonneg_right hb.1 heps.le
      _ ≤ _:=Hsave
  have H2 : C2 level*eps^(level+1) ≤ ((n+1:ℕ):ℝ)^(-saving/2):=
    (mul_le_mul_of_nonneg_left (Hpow level) (hC2 level)).trans
      ((mul_le_mul_of_nonneg_right hb.2 heps.le).trans Hsave)
  refine ⟨HH.1.trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_right H3 M.data.hd.le
  · intro i hi hmass seedMass
    apply (HH.2 i hi hmass seedMass).trans
    exact mul_le_mul_of_nonneg_right H2 (sq_nonneg M.data.d)

theorem actual_high_wall_fresh_pair_power_master_at_calibrated_star_along
    {m delta cl cu Az C0 Ct D Bclock L cK : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hL : 0 < L) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hcK : 0 < cK)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) ((M n).data.d) L Cs (w n))
    (depth : ℕ) :
    ∃A : ℝ,1 ≤ A ∧ ∀ᶠn in atTop,
      ∀Lnet : ℕ,((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀extra : List PositiveMass,(∀u∈extra,u.val ≤ 1) →
      ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ (∀u∈extra,u∈us) ∧
        (∀u∈uniformMasses Lnet,u∈us) ∧ (w n).star∈us ∧
        ∀ᶠjGrid in atTop,ActualHighWallFreshPairPowerBudgetsOnGrid depth A
          (actualSlowWindowExponent m delta/128) Cmass cK (M n) (w n).star (finiteCutMasses us jGrid) := by
  obtain ⟨A,hA,HA⟩:=actual_high_wall_fresh_pair_master_at_calibrated_star_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hL Cmass hCm hcK dim hdim M hfixed hdlim Cs hCs w hw depth
  have Hrate:=eventually_actual_high_wall_fresh_pair_power_budget_of_grid (depth:=depth)
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D)
    (saving:=actualSlowWindowExponent m delta/128) (Cmass:=Cmass)
    ((M 0).data.hTpos.le.trans (M 0).hT) hA
    (div_pos (actualSlowWindowExponent_pos hm hdelta hroom) (by norm_num)) hcK
  refine ⟨A,hA,?_⟩
  filter_upwards [HA,hdim.eventually Hrate] with n hn hnr
  intro Lnet hmesh extra hextra
  obtain ⟨us,hus,hret,huniform,hstar,Hgrid⟩:=hn Lnet hmesh extra hextra
  refine ⟨us,hus,hret,huniform,hstar,?_⟩
  filter_upwards [Hgrid] with jGrid hj
  exact hnr (M n) (w n).star (finiteCutMasses us jGrid) hj

end OAI.SKFluctuations.Cavity
