module

public import SKProof.Port.ComparisonActualOriginalQCavityCategoryInterfaces
public import SKProof.Port.ComparisonActualOriginalQActualFourGaCurrent

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 26000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

theorem native_actual_four_other_source_eq_Ga_add_categories_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    nativeActualOriginalFourOtherSourceErrorContrast_original_q M U st=
      nativeActualOriginalFourGaContrast_original_q M U st+
      (nativeActualOtherSourceCategories.map
        (nativeActualOriginalFourOtherCategoryContrast_original_q M U st)).sum := by
  unfold nativeActualOriginalFourOtherSourceErrorContrast_original_q nativeActualOriginalFourGaContrast_original_q
    nativeActualOriginalFourOtherCategoryContrast_original_q
  dsimp only
  rw [native_actual_other_source_eq_Ga_add_categories,native_actual_other_source_eq_Ga_add_categories]
  simp only [nativeActualOtherSourceCategories,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

theorem native_actual_four_other_source_sum_eq_Ga_add_categories_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    nativeActualFourOtherSourceErrorSum_original_q M U W xs=
      (xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast_original_q M U Q)).sum+
      (nativeActualOtherSourceCategories.map (nativeActualFourOtherCategorySum_original_q M U W xs)).sum := by
  induction xs with
  | nil=>simp [nativeActualFourOtherSourceErrorSum_original_q,nativeActualFourOtherCategorySum_original_q,nativeActualOtherSourceCategories]
  | cons Q xs ih=>
    simp only [nativeActualFourOtherSourceErrorSum_original_q,List.map_cons,List.sum_cons] at ih ⊢
    rw [native_actual_four_other_source_eq_Ga_add_categories_original_q,ih]
    simp only [nativeActualFourOtherCategorySum_original_q,nativeActualOtherSourceCategories,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    ring

theorem actual_minimum_four_other_source_closed_categories_abs_le_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cKcut cK CK BG BR BF : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcKcut : 0 < cKcut) (hcK : 0 < cK)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cKcut*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (hupper : nativeContinuumMixedClock n M.sweepBf M.sweepHf as star ≤ CK*W)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (HG : (xs.map (fun Q=>|nativeActualOriginalFourGaCurrentError_original_q M U W Q|)).sum ≤ BG)
    (HR : (xs.map (fun Q=>|nativeActualOriginalFourGaRestorationError_original_q M U W Q|)).sum ≤ BR)
    (HF : (xs.map (fun Q=>|nativeActualOriginalFourFirstHighError_original_q M U W Q|)).sum ≤ BF) :
    |nativeActualFourOtherSourceErrorSum_original_q M U W xs|/(Real.exp (-4*Temp)*cK*W)+
      |nativeActualFourFirstHighErrorSum_original_q M U W xs| ≤
      (CK/(Real.exp (-4*Temp)*cK))*(BG+BR)+BF+
      (nativeActualOtherSourceCategories.map (fun cat=>|nativeActualFourOtherCategorySum_original_q M U W xs cat|)).sum/
        (Real.exp (-4*Temp)*cK*W) := by
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let den:=Real.exp (-4*Temp)*cK*W
  have hden : 0 < den:=by dsimp only [den];positivity
  obtain ⟨hD,hchi,_⟩:=actual_minimum_four_denominator_bounds_original_q M htotal hW hcKcut ho hs hU hstarK
  change 0 < chi*K star at hD
  change chi ≤ 1 at hchi
  have hK : 0 ≤ K star:=(mul_pos hcKcut hW).le.trans hstarK
  have hDK : chi*K star ≤ CK*W:=
    (calc chi*K star ≤ 1*K star:=mul_le_mul_of_nonneg_right hchi hK
          _ = K star:=one_mul _).trans hupper
  have Hrow Q (hQ : Q∈xs) :
      |W⁻¹^Q.generation*nativeActualOriginalFourGaContrast_original_q M U Q| ≤
        (chi*K star)*(|nativeActualOriginalFourGaCurrentError_original_q M U W Q|+
          |nativeActualOriginalFourGaRestorationError_original_q M U W Q|):=by
    have HE:=actual_minimum_four_Ga_error_eq_current_add_restoration_original_q M Q (hxs Q hQ) hi hs ho W
    have HI : W⁻¹^Q.generation*nativeActualOriginalFourGaContrast_original_q M U Q=
        -(chi*K star)*nativeActualOriginalFourGaError_original_q M U W Q:=by
      unfold nativeActualOriginalFourGaError_original_q
      dsimp only
      change _=-(chi*K star)*(-(W⁻¹^Q.generation/(chi*K star))*_)
      field_simp [(mul_ne_zero_iff.mp hD.ne').1,(mul_ne_zero_iff.mp hD.ne').2]
    rw [HI,abs_mul,abs_neg,abs_of_pos hD,HE]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hD.le
  have HGsum : |(xs.map (fun Q=>W⁻¹^Q.generation*nativeActualOriginalFourGaContrast_original_q M U Q)).sum| ≤
      (chi*K star)*(BG+BR):=by
    apply (native_abs_sum_map_le xs _).trans
    apply (List.sum_le_sum Hrow).trans
    rw [List.sum_map_mul_left,List.sum_map_add]
    exact mul_le_mul_of_nonneg_left (add_le_add HG HR) hD.le
  have Hcat:=native_abs_sum_map_le nativeActualOtherSourceCategories (nativeActualFourOtherCategorySum_original_q M U W xs)
  have HO : |nativeActualFourOtherSourceErrorSum_original_q M U W xs| ≤
      (chi*K star)*(BG+BR)+
        (nativeActualOtherSourceCategories.map (fun cat=>|nativeActualFourOtherCategorySum_original_q M U W xs cat|)).sum:=by
    rw [native_actual_four_other_source_sum_eq_Ga_add_categories_original_q]
    exact (abs_add_le _ _).trans (add_le_add HGsum (by simpa only [List.map_map] using Hcat))
  have HFsum : |nativeActualFourFirstHighErrorSum_original_q M U W xs| ≤ BF:=
    (native_abs_sum_map_le xs _).trans HF
  have hBG : 0 ≤ BG:=(List.sum_nonneg (by intro x hx; obtain ⟨Q,_,rfl⟩:=List.mem_map.mp hx;exact abs_nonneg _)).trans HG
  have hBR : 0 ≤ BR:=(List.sum_nonneg (by intro x hx; obtain ⟨Q,_,rfl⟩:=List.mem_map.mp hx;exact abs_nonneg _)).trans HR
  have Hratio : (chi*K star)/den ≤ CK/(Real.exp (-4*Temp)*cK):=by
    apply (div_le_div_of_nonneg_right hDK hden.le).trans_eq
    dsimp only [den]
    field_simp
  have Hscaled:=mul_le_mul_of_nonneg_right Hratio (add_nonneg hBG hBR)
  apply (add_le_add (div_le_div_of_nonneg_right HO hden.le) HFsum).trans
  change ((chi*K star)*(BG+BR)+_)/den+BF ≤ _
  rw [add_div,mul_div_right_comm]
  linarith

variable {dim : ℕ→ℕ}
def ActualConstantSourceFirstHighOnGivenCutsAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (C : ℝ)
    (M : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let star:=retainedMassPrefixIndex (w n).star.val as
    let U:=retainedMassPrefixIndex (high n).val as
    ∃hs : star < U,∃hU : U ≤ as.length,
    ((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
      (nativeActualConstantSourceChildren_original_q (M n) as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourFirstHighError_original_q (M n) U (W n) Q|)).sum ≤
      C*(M n).data.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^2

end OAI.SKFluctuations.Cavity
