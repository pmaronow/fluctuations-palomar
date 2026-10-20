module

public import ComparisonActualHighWallThetaZeroEq7BroadSmallScaleDiameterDraft
public import ComparisonActualHighWallThetaZeroEq7BroadConditionalPieceDraft
public import ComparisonActualHighWallThetaZeroEq7BroadTraceScalarDraft
public import ComparisonActualHighWallThetaZeroEq7InnerBroadReverseGateDraft
public import ComparisonActualHighWallThetaZeroEq7ScalarGeometryDraft
public import ComparisonActualHighWallThetaZeroEq7CutoffProjectionsDraft
public import ComparisonActualHighWallThetaZeroEq7FixedStrengthDraft
public import ComparisonActualHighWallThetaZeroEq7ExactBudgetJoinDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 18000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eq7_inner_regular_broad_exact_budget_rate_draft
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    (P : Q.Potential) (h : ℝ) (hhi : h ≤ 1)
    (ell : ℕ) (hell : 2 < ell) (qBroad eps C : ℝ)
    (hm : 0 ≤ m) (hdelta : 0 ≤ delta) (heps : 0 < eps)
    (horder : (14+3*delta)/((ell:ℝ)-1) ≤ eps)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hN : 1 ≤ Q.data.N) (hC0N : C0 ≤ Q.data.N)
    (hlog : 1 ≤ Real.log Q.data.N)
    (hdepth : 1/Q.data.N ≤ Q.data.d)
    (hcarrier : Q.xs = comparisonConditionalScale
      Q.data.N delta Q.data.E Q.lam)
    (hUA : comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs)
    (hlamFloor : Q.data.N^(-(10:ℝ)) ≤ Q.lam)
    (hC : 1 ≤ C) (hh : h ≤ C*Q.xs)
    (hYBN : 1+32*C ≤ Q.data.N)
    (hLcap : Q.data.N^(-(1:ℝ)) ≤
      comparisonConstraintLength Q.data.N Q.data.E Q.data.d)
    (hqBroad : 1 ≤ qBroad)
    (F : Finset (ordConnectedSection P.negativeSet))
    (b : Eq7InnerRelevantBroadSlice (P.capFamily F) h) :
    let beta := 30+10*delta
    let L := Real.log Q.data.N
    let B := 2*C
    let Y := 1+16*B
    let K := max 1 ((Az+1/cl)*Y)
    let Kloss := criticalBroadOriginLossFactor*
      (1025+25*(1+Real.log (1+D^2)))
    let Tbeta := comparisonEq7BroadTemperatureConstant beta
    let J := 9*(2+Real.log (1+D^2))
    Q.lam*eq7InnerBroadExactBudget (P.capFamily F) ell qBroad
        (beta*L) (Q.data.N^(-beta)) b ≤
      comparisonEq7BroadPieceConstant K Kloss beta Tbeta B J Y qBroad*
        L^5*Q.data.N^(2*delta+eps)*Q.data.E := by
  let beta := 30+10*delta
  let L := Real.log Q.data.N
  let B := 2*C
  let Y := 1+16*B
  let K := max 1 ((Az+1/cl)*Y)
  let Kloss := criticalBroadOriginLossFactor*
    (1025+25*(1+Real.log (1+D^2)))
  let Tbeta := comparisonEq7BroadTemperatureConstant beta
  let J := 9*(2+Real.log (1+D^2))
  let cut := Q.data.N^(-beta)
  let f := eq7InnerBroadSampler (P.capFamily F) b.val.1
  let i := b.val.2
  let v := f.scale i
  let width := ∫r in eq7InnerBroadSlice (P.capFamily F) b.val,
    deriv Q.alpha.val.val r
  let U := comparisonSmallMass Q.data.N Q.data.E
  let u := min (16*v) 1
  let y := Q.criticalBroadMassHeight v
  let power := Q.criticalBroadMassPower v
  let diam := Q.criticalBroadMassDiameter
  let rev := Q.criticalBroadMassReverse ell qBroad v
  let loss := (32:ℝ)^2+Q.criticalBroadTraceLoss 4 v
    (min (4*v) 1)+1
  have hNp : 0 < Q.data.N := Q.data.hN
  have hU : 0 < U := Q.data.hU
  have hB : 0 ≤ B := by dsimp only [B]; linarith only [hC]
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hbeta : 0 ≤ beta := by dsimp only [beta]; linarith only [hdelta]
  have hTbeta : 0 ≤ Tbeta := by
    dsimp only [Tbeta,comparisonEq7BroadTemperatureConstant]
    positivity
  have hDlog : 0 ≤ Real.log (1+D^2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg D])
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hKloss : 0 ≤ Kloss := by
    dsimp only [Kloss]
    exact mul_nonneg criticalBroadOriginLossFactor_pos.le (by positivity)
  have hgeom := Q.eq7_inner_relevant_broad_scale_bounds_draft
    (P.capFamily F) hhi b
  have hUv : U ≤ v := hgeom.1
  have hv : 0 < v := hU.trans_le hUv
  have hvA : v ≤ B*Q.xs := by
    dsimp only [B]
    nlinarith only [hgeom.2,hh]
  have hw := f.width_bounds i
  have hwidthLo : v ≤ width := by
    simpa only [width,f,i,eq7InnerBroadSlice] using hw.1
  have hwidthV : width ≤ 4*v := by
    simpa only [width,f,i,eq7InnerBroadSlice] using hw.2.1
  have hwidth1 : width ≤ 1 := by
    simpa only [width,f,i,eq7InnerBroadSlice] using hw.2.2
  have hwidth : 0 ≤ width := hv.le.trans hwidthLo
  have hwidthp : 0 < width := hv.trans_le hwidthLo
  have hv1 : v ≤ 1 := hwidthLo.trans hwidth1
  have hwidthA : width ≤ 8*B*Q.xs := by
    have H := mul_le_mul_of_nonneg_left hvA
      (by norm_num : (0:ℝ) ≤ 4)
    nlinarith only [hwidthV,H,Q.hxs,hB]
  have hu : u ∈ Icc (0:ℝ) 1 := by
    dsimp only [u]
    exact ⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have huA : u ≤ (16*B)*Q.xs := by
    have H := mul_le_mul_of_nonneg_left hvA
      (by norm_num : (0:ℝ) ≤ 16)
    dsimp only [u]
    nlinarith only [H,min_le_left (16*v) 1]
  have hy : 0 < y := by
    dsimp only [y,criticalBroadMassHeight]
    linarith only [Q.hxs,hu.1]
  have hyA : y ≤ Y*Q.xs := by
    dsimp only [y,Y,criticalBroadMassHeight,u]
    nlinarith only [huA]
  have hPower : 0 < power := by
    dsimp only [power,criticalBroadMassPower]
    exact mul_pos Q.data.hN
      (laplaceComparisonStrength_pos Q.data.d Q.hlam _)
  have hDiameter : 0 < diam := by
    dsimp only [diam,criticalBroadMassDiameter]
    exact mul_pos (by linarith only [hlog])
      (add_pos_of_pos_of_nonneg Q.data.hrbounds.1
        Q.cavityCapTravel_nonneg)
  have hDiameterU : diam ≤ J*L^2*U := by
    simpa only [diam,J,L,U] using
      Q.eq7_inner_broad_diameter_le_small_mass_draft hN hdelta hlog
  have hAupper : Q.xs ≤ Q.data.N^(5+delta) := by
    rw [hcarrier]
    exact comparison_eq7_conditional_scale_upper_of_floor_draft
      hN Q.data.hE Q.data.hd Q.data.hd1 Q.hlam Q.hupper hlamFloor
  have hyN : y ≤ Q.data.N^(6+delta) := by
    have H := mul_le_mul hYBN hAupper Q.hxs.le
      (zero_lt_one.trans_le hN).le
    have Hpow : Q.data.N*Q.data.N^(5+delta) =
        Q.data.N^(6+delta) := by
      calc
        _ = Q.data.N^(1:ℝ)*Q.data.N^(5+delta) := by rw [Real.rpow_one]
        _ = Q.data.N^((1:ℝ)+(5+delta)) :=
          (Real.rpow_add Q.data.hN 1 (5+delta)).symm
        _ = _ := by congr 1; ring
    dsimp only [Y,B] at hyA ⊢
    nlinarith only [hyA,H,Hpow]
  have hratio : y/diam ≤ Q.data.N^(7+2*delta) := by
    simpa only [y,diam] using
      Q.eq7_inner_broad_reverse_ratio_of_raw_gate
        hN hlog hLcap hv.le hyN
  have horderBroad : (7+2*delta)/((ell:ℝ)-1) ≤ eps := by
    have hellR : (2:ℝ) < ell := by exact_mod_cast hell
    have hden : 0 ≤ (ell:ℝ)-1 := by linarith only [hellR]
    exact (div_le_div_of_nonneg_right
      (show 7+2*delta ≤ 14+3*delta by linarith only [hdelta]) hden).trans horder
  have hrev : rev ≤ (2*qBroad)^4*diam*y*Q.data.N^eps := by
    simpa only [rev,diam,y,criticalBroadMassReverse,
      criticalBroadMassHeight,comparisonReverseMoment] using
      comparison_reverse_polynomial_loss hell hN hDiameter
        hqBroad hy hratio horderBroad
  have hcal : Q.lam*Q.xs^2*U =
      Q.data.N^(2*delta)*Q.data.E := by
    rw [hcarrier]
    exact comparison_conditional_small_mass_cost
      Q.data.hN Q.data.hE Q.hlam
  have he : 0 < laplaceComparisonStrength Q.data.d Q.lam
      (Q.shiftedNativeModel.R u) :=
    laplaceComparisonStrength_pos Q.data.d Q.hlam _
  have hstrengthN := Q.eq7_fixed_strength_at_mass_draft
    hcl hAz hN hdelta hcarrier hu
      (by positivity : (0:ℝ) ≤ 16*B) huA
  have hstrength : Q.data.N^(-delta)*Q.lam ≤
      K*laplaceComparisonStrength Q.data.d Q.lam
        (Q.shiftedNativeModel.R u) := by
    have H : Q.data.N*(Q.data.N^(-delta)*Q.lam) ≤
        Q.data.N*(K*laplaceComparisonStrength Q.data.d Q.lam
          (Q.shiftedNativeModel.R u)) := by
      change Q.data.N*(Q.data.N^(-delta)*Q.lam) ≤
        K*(Q.data.N*laplaceComparisonStrength Q.data.d Q.lam
          (Q.shiftedNativeModel.R u)) at hstrengthN
      calc
        _ ≤ K*(Q.data.N*laplaceComparisonStrength Q.data.d Q.lam
          (Q.shiftedNativeModel.R u)) := hstrengthN
        _ = _ := by
          rw [←mul_assoc,mul_comm K Q.data.N,mul_assoc]
    exact le_of_mul_le_mul_left H Q.data.hN
  have htraceRatio : Q.lam*(1+v/U)/(power*v) ≤
      2*K*Q.data.N^delta*Q.data.E := by
    simpa only [power,criticalBroadMassPower,U,u] using
      comparison_eq7_broad_trace_ratio_at_small_scales_draft
        Q.data.hN Q.data.hE Q.hlam he hK hstrength hUv
  have hlossBound : loss ≤ Kloss*L*(1+v/U) := by
    simpa only [loss,Kloss,L,U,mul_assoc] using
      Q.eq7_inner_broad_loss_le_log_shape_draft
        hv hv1 hUv hN hlog
  have hV : 0 ≤ min (4*v) 1 :=
    le_min (by positivity) zero_le_one
  have hMV : 0 < Q.data.M (min (4*v) 1) :=
    (comparisonCap_first_term Q.data.hN Q.data.hU Q.data.hL
      Q.data.hE Q.data.hd.le hV).1
  have hlogU0 : 0 ≤ Real.log ((1+U)/U) := by
    apply Real.log_nonneg
    exact (one_le_div hU).mpr (by linarith only [hU])
  have hloss : 0 ≤ loss := by
    have Hlog : 0 ≤ (4+1)^2*(1+v/U)*Real.log ((1+U)/U) :=
      mul_nonneg (by positivity) hlogU0
    have Horigin : 0 ≤ Q.data.M (min (4*v) 1)*Q.data.rmin/v :=
      div_nonneg (mul_nonneg hMV.le Q.data.hrbounds.1.le) hv.le
    dsimp only [loss,criticalBroadTraceLoss]
    change 0 ≤ (32:ℝ)^2+
      ((4+1)^2*(1+v/U)*Real.log ((1+U)/U)+
        Q.data.M (min (4*v) 1)*Q.data.rmin/v)+1
    exact add_nonneg
      (add_nonneg (sq_nonneg (32:ℝ)) (add_nonneg Hlog Horigin))
      zero_le_one
  have htraceLoss : Q.lam*loss/(power*v) ≤
      2*K*Kloss*L*Q.data.N^delta*Q.data.E := by
    exact comparison_eq7_broad_loss_trace_product_draft
      Q.data.hN Q.data.hE Q.hlam hPower hv hU
      hKloss hK0 (by linarith only [hlog])
      hlossBound htraceRatio
  have hcutPos : 0 < cut := by dsimp only [cut]; positivity
  have hlogCut : Real.log (width/cut) ≤ beta*L := by
    have Hdiv : width/cut ≤ 1/cut :=
      div_le_div_of_nonneg_right hwidth1 hcutPos.le
    have Hlog := Real.log_le_log (div_pos hwidthp hcutPos) Hdiv
    have Heq : Real.log (1/cut) = beta*L := by
      dsimp only [cut,L]
      rw [one_div,Real.log_inv,Real.log_rpow Q.data.hN]
      ring
    exact Hlog.trans_eq Heq
  have hEfloor : Q.data.N^(-(5:ℝ)) ≤ Q.data.E :=
    Q.eq7_ordinary_cutoff_energy_floor_draft
      hm hC0 hN hC0N hdepth
  have hlam1 : Q.lam ≤ 1 :=
    Q.hld.trans (pow_le_one₀ Q.data.hd.le Q.data.hd1)
  have hcut : Q.lam*cut ≤ Q.data.E := by
    have Hpow : cut ≤ Q.data.N^(-(5:ℝ)) := by
      dsimp only [cut]
      exact Real.rpow_le_rpow_of_exponent_le hN
        (by dsimp only [beta]; linarith only [hdelta])
    have Hlam := mul_le_mul_of_nonneg_right hlam1 hcutPos.le
    have Hpow := Hpow.trans hEfloor
    nlinarith only [Hlam,Hpow]
  have Hbudget := comparison_eq7_broad_piece_of_all_atoms_draft
    hN hdelta heps Q.data.hE Q.hlam Q.hxs hU hUA
    hPower hv hloss hK0 hKloss hlog hbeta hTbeta
    (show comparisonEq7BroadTemperatureConstant beta ≤ Tbeta from le_rfl)
    hB hJ hY hwidth hwidthV hwidthA
    hDiameter.le hDiameterU hy.le hyA hcal htraceLoss
    hlogCut hrev hcut
  change Q.lam*Q.criticalBroadMassBudget ell qBroad (beta*L)
      cut v width ≤
    comparisonEq7BroadPieceConstant K Kloss beta Tbeta B J Y qBroad*
      L^5*Q.data.N^(2*delta+eps)*Q.data.E
  rw [Q.eq7_inner_broad_budget_native_expansion_draft]
  simpa only [loss,power,diam,rev,L,mul_assoc] using Hbudget

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
