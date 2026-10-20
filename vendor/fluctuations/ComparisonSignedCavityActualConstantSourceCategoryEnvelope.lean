module

public import ComparisonSignedCavityActualConstantSourceCategoryReduction
public import ComparisonSignedCavityActualConstantSourceCoarseEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 26000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {star U : ℕ}

def nativeActualConstantSourceRemainingCategoryEnvelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  ((List.range depth).map (fun j=>
    (nativeActualOtherSourceCategories.map (fun cat=>
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W j children) cat|)).sum/
      (Real.exp (-4*Temp)*cK*W))).sum

theorem actual_minimum_constant_source_category_envelope_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cKcut cK CK : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcKcut : 0 < cKcut) (hcK : 0 < cK)
    (ho : MassOrdered 0 as) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cKcut*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (hupper : nativeContinuumMixedClock n M.bf M.hf as star ≤ CK*W)
    (depth : ℕ) (BG BR BF : ℕ → ℝ)
    (HG : ∀j < depth,((nativeActualMinimumFourCenteredForest M hs hU W j
      (nativeActualConstantSourceChildren M as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourGaCurrentError M U W Q|)).sum ≤ BG j)
    (HR : ∀j < depth,((nativeActualMinimumFourCenteredForest M hs hU W j
      (nativeActualConstantSourceChildren M as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourGaRestorationError M U W Q|)).sum ≤ BR j)
    (HF : ∀j < depth,((nativeActualMinimumFourCenteredForest M hs hU W j
      (nativeActualConstantSourceChildren M as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum ≤ BF j) :
    nativeActualConstantSourceErrorEnvelope M hs hU W Temp cK depth ≤
      ((List.range depth).map (fun j=>(CK/(Real.exp (-4*Temp)*cK))*(BG j+BR j)+BF j)).sum+
        nativeActualConstantSourceRemainingCategoryEnvelope M hs hU W Temp cK depth := by
  unfold nativeActualConstantSourceErrorEnvelope nativeActualConstantSourceRemainingCategoryEnvelope
  dsimp only
  rw [←List.sum_map_add]
  apply List.sum_le_sum
  intro j hj
  have hj':=List.mem_range.mp hj
  exact actual_minimum_four_other_source_closed_categories_abs_le M htotal hW hcKcut hcK ho
    (Nat.zero_le _) hs hU hstarK hupper _
    (nativeActualFourCenteredForest_valid _ hs (hs.le.trans hU) _ j _
      (fun Q hQ=>nativeActualConstantSourceChildren_valid M hs hU Q hQ))
    (HG j hj') (HR j hj') (HF j hj')

theorem actual_source_dimension_power_le {eta rho : ℝ} (hrho : 0 ≤ rho) (hre : rho ≤ eta)
    (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)^(-eta) ≤ (1/2:ℝ)^(-rho)*((n+1:ℕ):ℝ)^(-rho) := by
  have hn1 : (1:ℝ) ≤ n:=by exact_mod_cast hn
  have hn0 : (0:ℝ) < n:=zero_lt_one.trans_le hn1
  have hN : (0:ℝ) < ((n+1:ℕ):ℝ):=by positivity
  have H1:=Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hre)
  have hhalf : (1/2:ℝ)*((n+1:ℕ):ℝ) ≤ (n:ℝ):=by push_cast;nlinarith
  have H2:=Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < (1/2:ℝ)*((n+1:ℕ):ℝ))
    hhalf (neg_nonpos.mpr hrho)
  rw [Real.mul_rpow (by norm_num) hN.le] at H2
  exact H1.trans H2

end OAI.SKFluctuations.Cavity
