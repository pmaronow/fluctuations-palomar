module

public import ComparisonSignedCavityActualConstantSourceChildrenTerminalAlong
public import ComparisonSignedCavityActualFourPairForestAlong
public import ComparisonSignedCavityActualFourConstantFrozenLevelAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem actual_constant_source_children_forest_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp B : ℝ}
    {as : List PositiveMass} {star U : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U≤as.length)
    (W : ℝ) (depth : ℕ) (hB : 0≤B)
    (F : NativeActualResourceState (Spin n×Bool) as 0 star→ℝ)
    (H : ∀Q∈nativeActualConstantSourceChildren M as star U hs hU,
      |((nativeActualMinimumFourCenteredForest M hs hU W depth [Q]).map F).sum|
        ≤|Q.term.coefficient| *B) :
    |((nativeActualMinimumFourCenteredForest M hs hU W depth
      (nativeActualConstantSourceChildren M as star U hs hU)).map F).sum|≤6*B := by
  let xs:=nativeActualConstantSourceChildren M as star U hs hU
  have HD : nativeActualMinimumFourCenteredForest M hs hU W depth xs=
      xs.flatMap (fun Q=>nativeActualMinimumFourCenteredForest M hs hU W depth [Q]):=by
    unfold nativeActualMinimumFourCenteredForest
    exact nativeActualFourCenteredForest_eq_flatMap_singletons _ _ _ _ _ _
  change |((nativeActualMinimumFourCenteredForest M hs hU W depth xs).map F).sum|≤_
  rw [HD,List.map_flatMap,native_sum_flatMap]
  apply (native_abs_sum_map_le _ _).trans
  apply (List.sum_le_sum H).trans
  rw [List.sum_map_mul_right]
  exact mul_le_mul_of_nonneg_right
    (nativeActualConstantSourceChildren_coefficient_variation M htotal ho hs hU) hB

def ActualOriginalConstantSourceChildrenPairLevelSavingAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (gamma sharpSaving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val≤1)→(w n).star∈us→∀ᶠj in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U : ℕ) (hs : star<U) (hU : U≤as.length),
      |nativeActualFourPairSum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren (M n) as star U hs hU))|≤
        6*((((dim n+1:ℕ):ℝ)^(-sharpSaving/2))*
          ((((dim n+1:ℕ):ℝ)^(-gamma))^(1+depth))*((M n).xs^2/W n))

def ActualOriginalConstantSourceChildrenFrozenLevelSavingAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (gamma : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val≤1)→(w n).star∈us→∀ᶠj in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U : ℕ) (hs : star<U) (hU : U≤as.length),
      |nativeActualFourFrozenChildSum (M n) hs hU (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren (M n) as star U hs hU))|≤
        6*(((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2*
          ((((dim n+1:ℕ):ℝ)^(-gamma))^(1+depth+1)))

theorem ActualOriginalConstantFourPairForestSavingAlong.source_children
    {m delta cl cu Az C0 Ct D Bclock Temp gamma sharpSaving : ℝ} {depth : ℕ} {dim : ℕ→ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualOriginalConstantFourPairForestSavingAlong 1 depth 3 gamma sharpSaving M W w)
    (hxs : ∀n,(M n).xs≤W n)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤Temp) :
    ActualOriginalConstantSourceChildrenPairLevelSavingAlong depth gamma sharpSaving M W w := by
  filter_upwards [H,htotal] with n hn hnTotal
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  intro U hs hU
  have hW : 0<W n:=(M n).hxs.trans_le (hxs n)
  apply actual_constant_source_children_forest_abs_le (M n) hnTotal
    (finiteCutMasses_ordered us hus j) hs hU (W n) depth (by positivity)
  intro Q hQ
  have HG:=nativeActualConstantSourceChildren_generation (M n) hs hU Q hQ
  have HV:=nativeActualConstantSourceChildren_valid (M n) hs hU Q hQ
  have HL:=nativeActualConstantSourceChildren_leaves (M n) hs hU Q hQ
  rw [HG] at HV
  have HB:=hj U 0 (Nat.zero_le _) hs hU Q.tree Q.term HV HL
  cases Q with
  | mk tree term generation=>
    dsimp only at HG
    subst generation
    simpa only [nativeActualFourPairSum,mul_assoc] using HB

theorem ActualOriginalFourConstantFrozenChildLevelSavingAlong.source_children
    {m delta cl cu Az C0 Ct D Bclock Temp gamma : ℝ} {depth : ℕ} {dim : ℕ→ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualOriginalFourConstantFrozenChildLevelSavingAlong 1 depth 3 gamma M W w)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤Temp) :
    ActualOriginalConstantSourceChildrenFrozenLevelSavingAlong depth gamma M W w := by
  filter_upwards [H,htotal] with n hn hnTotal
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  intro U hs hU
  apply actual_constant_source_children_forest_abs_le (M n) hnTotal
    (finiteCutMasses_ordered us hus j) hs hU (W n) depth (by positivity)
  intro Q hQ
  have H:=hj U 0 (Nat.zero_le _) hs hU Q
    (nativeActualConstantSourceChildren_valid (M n) hs hU Q hQ)
    (nativeActualConstantSourceChildren_generation (M n) hs hU Q hQ)
    (nativeActualConstantSourceChildren_leaves (M n) hs hU Q hQ)
  simpa only [mul_assoc] using H

end OAI.SKFluctuations.Cavity
