module

public import ComparisonSignedCavityActualConstantSourceChildrenFrozenAlong
public import ComparisonActualHighOnlySquareConsumerActualConstantSourceChildrenLevelsAlong

@[expose] public section
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum (ActualSlowWindowChoice)
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

def ActualOriginalConstantSourceChildrenFrozenSavingAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (gamma : ℝ) {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val≤1)→(w n).star∈us→∀ᶠj in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U : ℕ) (hs : star < U) (hU : U≤ as.length),
      |((nativeActualConstantSourceChildren_high_only (M n) as star U hs hU).map
        (fun Q=>nativeActualMinimumFourStateResponse_high_only (M n) U (W n) Q.freeze)).sum| ≤
        ((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2*((dim n+1:ℕ):ℝ)^(-gamma)

theorem actual_inherited_constant_source_children_frozen_saving_of_pair_budget_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp gamma A : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hTemp : 0≤ Temp) (hA : 1≤ A)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤ W n)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤ Temp)
    (hroot : ∀ᶠn in atTop,(M n).h 0=0)
    (w : ℕ→ActualSlowWindowChoice)
    (Hp : ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong_high_only 1 A gamma M W w) :
    ActualOriginalConstantSourceChildrenFrozenSavingAlong_high_only gamma M W w := by
  have Hrate:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (native_mass_log_power_decay (q:=(1:ℝ)/3) (s:=(1:ℝ)/6) (by norm_num) 0 (6*A))
  have Hmean:=eventually_actual_inherited_clock_frozen_resource_correction_high_only
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    3 Bclock Temp hTemp hm hC0
  filter_upwards [Hp,htotal,hroot,hdim.eventually Hmean,Hrate] with n hnPair hnTotal hnRoot hnMean hnRate
  intro us hus hstar
  filter_upwards [hnPair us hus hstar,hnMean (M n) hnTotal hnRoot us hus] with j hjPair hjMean
  dsimp only at hjPair hjMean ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let eps:=((dim n+1:ℕ):ℝ)^(-gamma)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have heps : 0 < eps:=by dsimp only [eps];positivity
  intro U hs hU
  change star < U at hs
  change U≤ as.length at hU
  let children:=nativeActualConstantSourceChildren_high_only (M n) as star U hs hU
  let raw:=A*eps*(((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)*(M n).xs^2)
  have hraw : 0≤ raw:=by dsimp only [raw];have hA0:=zero_lt_one.trans_le hA;positivity
  have Hpoint (Q : NativeActualResourceState (Spin (dim n)×Bool) as 0 star) (hQ : Q∈children) :
      |nativeActualMinimumFourStateResponse_high_only (M n) U (W n) Q.freeze|≤|Q.term.coefficient| *raw:=by
    have HQ:=nativeActualConstantSourceChildren_valid_high_only (M n) hs hU Q hQ
    have HD:=nativeActualConstantSourceChildren_generation_high_only (M n) hs hU Q hQ
    have HL:=nativeActualConstantSourceChildren_leaves_high_only (M n) hs hU Q hQ
    have HP:=hjPair U 0 Q.generation Q.tree Q.term HQ (by omega)
      (M n).xs 1 1 (by norm_num) (by norm_num)
    have H:=hjMean K 0 star U Q.generation [] Q.tree Q.term HQ HL
      A (M n).xs (W n) eps (zero_lt_one.trans_le hA) (M n).hxs hW heps
      (Nat.zero_le _) (hs.trans_le hU) HP
    change |nativeActualMinimumFourStateResponse_high_only (M n) U (W n) Q.freeze|≤_ at H
    simpa only [HD,List.length_nil,zero_add,pow_one,nativeResourceScale,List.map_nil,
      List.prod_nil,mul_one,raw,mul_assoc] using H
  change |(children.map (fun Q=>nativeActualMinimumFourStateResponse_high_only (M n) U (W n) Q.freeze)).sum|≤_
  apply (native_abs_sum_map_le _ _).trans
  apply (List.sum_le_sum Hpoint).trans
  rw [List.sum_map_mul_right]
  have HC:=nativeActualConstantSourceChildren_coefficient_variation_high_only (M n) hnTotal ho hs hU
  change (children.map (fun Q=>|Q.term.coefficient|)).sum≤6 at HC
  apply (mul_le_mul_of_nonneg_right HC hraw).trans
  have Hab : (6*A)*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)≤((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6):=by
    simpa only [pow_zero,mul_one,neg_div,Function.comp_apply] using hnRate
  calc
    6*raw=((6*A)*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3))*(M n).xs^2*eps:=by
      dsimp only [raw]
      ring
    _≤((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2*eps:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right Hab (sq_nonneg _)) heps.le
    _=_:=rfl

theorem actual_inherited_constant_source_children_frozen_saving_of_star_moment_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp gamma : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hTemp : 0≤ Temp)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤ W n)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤ Temp)
    (hroot : ∀ᶠn in atTop,(M n).h 0=0)
    (w : ℕ→ActualSlowWindowChoice)
    (Hstar : ActualOriginalSquareStarMomentOnEveryFinalNetAlong_high_only 0 gamma M W w) :
    ActualOriginalConstantSourceChildrenFrozenSavingAlong_high_only gamma M W w :=
  actual_inherited_constant_source_children_frozen_saving_of_pair_budget_along_high_only
    hm hC0 hTemp (by norm_num) dim hdim M W hxs htotal hroot w
    (actual_square_constant_resource_pair_budget_of_actual_star_producer_along_high_only
      1 (by norm_num) M W hxs w Hstar)

end OAI.SKFluctuations.Cavity
