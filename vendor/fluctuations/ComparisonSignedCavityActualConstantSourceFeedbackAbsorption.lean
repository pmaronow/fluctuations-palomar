module

public import ComparisonSignedCavityActualConstantSourceCoarseEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem constant_source_coarse_division_le
    {b T W x c D q J E R : ℝ} (depth : ℕ)
    (hb : 0≤b) (hbT : b≤T) (hW : 0<W) (hx : 0≤x) (hxW : x≤W)
    (hc : 0<c) (hD : 0<D) (hq : 0≤q) (hJ : 0≤J) (hE : 0≤E) :
    (b*W*((depth:ℝ)*(J*(6*q*(x^2/W))/(D*W))+(6*(depth:ℝ)+13)*x^2+E)+R)/(c*W)≤
      (T/c)*((6*(depth:ℝ)/D)*q*J+(6*(depth:ℝ)+13)*W^2+E)+R/(c*W) := by
  have hT : 0≤T:=hb.trans hbT
  have hx2 : x^2≤W^2:=sq_le_sq₀ hx hW.le |>.mpr hxW
  have hratio : x^2/W^2≤1:=(div_le_one (sq_pos_of_pos hW)).mpr hx2
  have hratio0 : 0≤x^2/W^2:=div_nonneg (sq_nonneg _) (sq_nonneg _)
  have HA : (6*(depth:ℝ)/D)*q*J*(x^2/W^2)+(6*(depth:ℝ)+13)*x^2+E≤
      (6*(depth:ℝ)/D)*q*J+(6*(depth:ℝ)+13)*W^2+E:=by
    have H1:=mul_le_mul_of_nonneg_left hratio
      (show 0≤(6*(depth:ℝ)/D)*q*J by positivity)
    have H2:=mul_le_mul_of_nonneg_left hx2 (show 0≤6*(depth:ℝ)+13 by positivity)
    nlinarith
  calc
    _=(b/c)*((6*(depth:ℝ)/D)*q*J*(x^2/W^2)+(6*(depth:ℝ)+13)*x^2+E)+R/(c*W):=by
      field_simp
    _≤(T/c)*((6*(depth:ℝ)/D)*q*J*(x^2/W^2)+(6*(depth:ℝ)+13)*x^2+E)+R/(c*W):=by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hbT hc.le) (by positivity)
    _≤_:=add_le_add (mul_le_mul_of_nonneg_left HA (div_nonneg hT hc.le)) le_rfl

theorem nativeActualConstantSourceErrorEnvelope_nonneg
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp cK W : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {star U : ℕ} (hs : star<U) (hU : U≤as.length)
    (hW : 0<W) (hcK : 0<cK) (depth : ℕ) :
    0≤nativeActualConstantSourceErrorEnvelope M hs hU W Temp cK depth := by
  unfold nativeActualConstantSourceErrorEnvelope
  exact List.sum_nonneg (by intro a ha;obtain ⟨j,_,rfl⟩:=List.mem_map.mp ha;positivity)

theorem actual_minimum_constant_source_susceptibility_feedback_absorption
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Tstar cK cS gamma sharpSaving terminalSaving W Cs Cbond : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {star U : ℕ} (hs : star<U) (hU : U≤as.length)
    (ho : MassOrdered 0 as) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (hW : 0<W) (hxW : M.xs≤W) (hcK : 0<cK) (hcS : 0<cS)
    (hgamma : 0≤gamma) (hterminal : 0≤terminalSaving) (depth : ℕ)
    (Hsource : |nativeActualMinimumConstantJointSource M as star U|≤
      nativeActualConstantSourceKnownEnvelope M hs hU W Temp cK gamma sharpSaving terminalSaving depth)
    (Hsusc :
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |Tstar*chi^2-1|≤Cs*W^2+|nativeActualMinimumConstantJointSource M as star U|/(cS*W))
    (Hbond :
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2|≤|Tstar*chi^2-1|+Cbond*W^2)
    (Hsmall : (Temp/cS)*(6*(depth:ℝ)/(Real.exp (-4*Temp)*cK))*
      ((n+1:ℕ):ℝ)^(-sharpSaving/2)≤1/2) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let feedback:=(Temp/cS)*(6*(depth:ℝ)/(Real.exp (-4*Temp)*cK))*((n+1:ℕ):ℝ)^(-sharpSaving/2)
    |Tstar*chi^2-1|≤
      2*(Cs+(Temp/cS)*(6*(depth:ℝ)+13)+feedback*Cbond)*W^2+
      2*((Temp/cS)*nativeActualConstantSourceErrorEnvelope M hs hU W Temp cK depth+
        |nativeActualConstantSourceRemainder M as star U|/(cS*W)) := by
  dsimp only at Hsusc Hbond ⊢
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let bstar:=(M.bf (partitionPoint 0 as star):ℝ)
  let N:=((n+1:ℕ):ℝ)
  let feedback:=(Temp/cS)*(6*(depth:ℝ)/(Real.exp (-4*Temp)*cK))*N^(-sharpSaving/2)
  let E:=nativeActualConstantSourceErrorEnvelope M hs hU W Temp cK depth
  let R:=|nativeActualConstantSourceRemainder M as star U|
  have hbT : bstar≤Temp:=by
    have H:=M.inherited_total_clock_le htotal _ (partitionPoint_mem as ho star)
    dsimp only [bstar]
    linarith [NNReal.coe_nonneg (M.hf (partitionPoint 0 as star))]
  have hTemp : 0≤Temp:=(NNReal.coe_nonneg _).trans hbT
  have hfeedback : 0≤feedback:=by dsimp only [feedback,N];positivity
  have Hcoarse:=Hsource.trans (nativeActualConstantSourceKnownEnvelope_le_coarse M hs hU
    hW hcK hgamma hterminal depth)
  have HD:=constant_source_coarse_division_le (b:=bstar) (T:=Temp) (c:=cS)
    (D:=Real.exp (-4*Temp)*cK) (q:=N^(-sharpSaving/2))
    (J:=|1-bstar*chi^2|) (E:=E) (R:=R) depth (NNReal.coe_nonneg _) hbT
    hW M.hxs.le hxW hcS (by positivity) (by dsimp only [N];positivity) (abs_nonneg _)
    (nativeActualConstantSourceErrorEnvelope_nonneg M hs hU hW hcK depth)
  have Hgap:=Hsusc.trans (add_le_add le_rfl
    ((div_le_div_of_nonneg_right Hcoarse (mul_pos hcS hW).le).trans HD))
  have HJ:=mul_le_mul_of_nonneg_left Hbond hfeedback
  have HE : |Tstar*chi^2-1|≤(Cs+(Temp/cS)*(6*(depth:ℝ)+13))*W^2+
      feedback*(|Tstar*chi^2-1|+Cbond*W^2)+(Temp/cS)*E+R/(cS*W):=by
    change _≤Cs*W^2+((Temp/cS)*((6*(depth:ℝ)/(Real.exp (-4*Temp)*cK))*
      N^(-sharpSaving/2)*|1-bstar*chi^2|+(6*(depth:ℝ)+13)*W^2+E)+R/(cS*W)) at Hgap
    dsimp only [feedback] at HJ
    nlinarith
  have HF:=susceptibility_absorption_with_literal_correction Hsmall
    (show |Tstar*chi^2-1|≤(Cs+(Temp/cS)*(6*(depth:ℝ)+13))*W^2+
      feedback*(|Tstar*chi^2-1|+Cbond*W^2)+((Temp/cS)*E+R/(cS*W)) by linarith [HE])
  exact HF

end OAI.SKFluctuations.Cavity
