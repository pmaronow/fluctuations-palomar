module

public import ComparisonSignedCavityActualConstantSourceKnownEnvelopeAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

def nativeActualConstantSourceErrorEnvelope
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {star U : ℕ} (hs : star<U) (hU : U≤as.length)
    (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  ((List.range depth).map (fun j=>
    |nativeActualFourOtherSourceErrorSum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W j children)|/(Real.exp (-4*Temp)*cK*W)+
    |nativeActualFourFirstHighErrorSum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W j children)|)).sum

theorem nativeActualConstantSourceKnownEnvelope_le_coarse
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp cK gamma sharpSaving terminalSaving W : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {star U : ℕ} (hs : star<U) (hU : U≤as.length)
    (hW : 0<W) (hcK : 0<cK) (hgamma : 0≤gamma) (hterminal : 0≤terminalSaving) (depth : ℕ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let bstar:=(M.bf (partitionPoint 0 as star):ℝ)
    nativeActualConstantSourceKnownEnvelope M hs hU W Temp cK gamma sharpSaving terminalSaving depth≤
      bstar*W*((depth:ℝ)*(|1-bstar*chi^2| *(6*((n+1:ℕ):ℝ)^(-sharpSaving/2)*(M.xs^2/W))/
          (Real.exp (-4*Temp)*cK*W))+(6*(depth:ℝ)+13)*M.xs^2+
        nativeActualConstantSourceErrorEnvelope M hs hU W Temp cK depth)+
      |nativeActualConstantSourceRemainder M as star U| := by
  dsimp only
  let N:=((n+1:ℕ):ℝ)
  let eps:=N^(-gamma)
  let den:=Real.exp (-4*Temp)*cK*W
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let bstar:=(M.bf (partitionPoint 0 as star):ℝ)
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  let other:=fun j=>|nativeActualFourOtherSourceErrorSum M U W
    (nativeActualMinimumFourCenteredForest M hs hU W j children)|/den+
    |nativeActualFourFirstHighErrorSum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W j children)|
  let pair:=|1-bstar*chi^2| *(6*N^(-sharpSaving/2)*(M.xs^2/W))/den
  have hN : 1≤N:=by dsimp only [N];exact_mod_cast (show 1≤n+1 by omega)
  have heps : 0≤eps:=Real.rpow_nonneg (zero_le_one.trans hN) _
  have heps1 : eps≤1:=Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hgamma)
  have hp d : eps^d≤1:=pow_le_one₀ heps heps1
  have hN6 : N^(-(1:ℝ)/6)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  have hNt : N^(-terminalSaving)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hden : 0<den:=by dsimp only [den];positivity
  have hNs : 0≤N^(-sharpSaving/2):=Real.rpow_nonneg (zero_le_one.trans hN) _
  have hNx : 0≤N^(-(1:ℝ)/6):=Real.rpow_nonneg (zero_le_one.trans hN) _
  have Hpair d : (|1-bstar*chi^2| *(6*(N^(-sharpSaving/2)*eps^(1+d)*(M.xs^2/W))))/den≤pair:=by
    apply div_le_div_of_nonneg_right _ hden.le
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have H:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hp (1+d)) hNs)
      (div_nonneg (sq_nonneg M.xs) hW.le)
    nlinarith
  have Hfrozen d : 6*(N^(-(1:ℝ)/6)*M.xs^2*eps^(1+d+1))≤6*M.xs^2:=by
    have H:=mul_le_mul_of_nonneg_left (hp (1+d+1)) (mul_nonneg hNx (sq_nonneg M.xs))
    have HN:=mul_le_mul_of_nonneg_right hN6 (sq_nonneg M.xs)
    nlinarith
  have Hinitial : N^(-(1:ℝ)/6)*M.xs^2*eps≤M.xs^2:=by
    have H:=mul_le_mul_of_nonneg_left heps1 (mul_nonneg hNx (sq_nonneg M.xs))
    have HN:=mul_le_mul_of_nonneg_right hN6 (sq_nonneg M.xs)
    nlinarith
  have Hterminal : 12*(N^(-terminalSaving)*M.xs^2)≤12*M.xs^2:=by
    nlinarith [mul_le_mul_of_nonneg_right hNt (sq_nonneg M.xs)]
  have Hsum : ((List.range depth).map (fun j=>
      (|1-bstar*chi^2| *(6*(N^(-sharpSaving/2)*eps^(1+j)*(M.xs^2/W)))+
        |nativeActualFourOtherSourceErrorSum M U W
          (nativeActualMinimumFourCenteredForest M hs hU W j children)|)/den+
      6*(N^(-(1:ℝ)/6)*M.xs^2*eps^(1+j+1))+
      |nativeActualFourFirstHighErrorSum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W j children)|)).sum≤
      (depth:ℝ)*(pair+6*M.xs^2)+((List.range depth).map other).sum:=by
    calc
      _≤((List.range depth).map (fun j=>(pair+6*M.xs^2)+other j)).sum:=by
        apply List.sum_le_sum
        intro j _
        rw [add_div]
        dsimp only [other]
        linarith [Hpair j,Hfrozen j]
      _=_:=by rw [List.sum_map_add];simp;ring
  unfold nativeActualConstantSourceKnownEnvelope
  dsimp only
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (NNReal.coe_nonneg _) hW.le)
  change _≤(depth:ℝ)*pair+(6*(depth:ℝ)+13)*M.xs^2+((List.range depth).map other).sum
  change _+12*(N^(-terminalSaving)*M.xs^2)+N^(-(1:ℝ)/6)*M.xs^2*eps≤_
  nlinarith

end OAI.SKFluctuations.Cavity
