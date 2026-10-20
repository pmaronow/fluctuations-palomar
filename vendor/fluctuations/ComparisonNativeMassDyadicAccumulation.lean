module

public import ComparisonNativeActualIntermediateMassScale
public import ComparisonNativeMassDefectIntervalCauchy

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def nativeIntermediateDyadicRatio : ℝ := actualIntermediateMassEffectiveScale 1 2

theorem nativeIntermediateDyadicRatio_pos : 0 < nativeIntermediateDyadicRatio := by
  exact actualIntermediateMassEffectiveScale_pos (by norm_num) (by norm_num)

theorem nativeIntermediateDyadicRatio_cube : nativeIntermediateDyadicRatio^3=2 := by
  simpa [nativeIntermediateDyadicRatio] using
    actualIntermediateMassEffectiveScale_cube (W:=1) (v:=2) (by norm_num) (by norm_num)

theorem nativeIntermediateDyadicRatio_one_lt : 1 < nativeIntermediateDyadicRatio := by
  by_contra h
  have H := pow_le_pow_left₀ nativeIntermediateDyadicRatio_pos.le (not_lt.mp h) 3
  rw [nativeIntermediateDyadicRatio_cube] at H
  norm_num at H

def nativeIntermediateAccumulationConstant (C : ℝ) : ℝ :=
  nativeIntermediateDyadicRatio/(nativeIntermediateDyadicRatio-1)*max 1 C

theorem nativeIntermediateAccumulationConstant_pos (C : ℝ) :
    0 < nativeIntermediateAccumulationConstant C := by
  unfold nativeIntermediateAccumulationConstant
  exact mul_pos (div_pos nativeIntermediateDyadicRatio_pos
    (sub_pos.mpr nativeIntermediateDyadicRatio_one_lt))
    (zero_lt_one.trans_le (le_max_left _ _))

theorem actualIntermediateMassEffectiveScale_double {W v : ℝ}
    (hW : 0 < W) (hv : 0 < v) :
    actualIntermediateMassEffectiveScale W (2*v)=
      nativeIntermediateDyadicRatio*actualIntermediateMassEffectiveScale W v := by
  apply (pow_left_inj₀ (actualIntermediateMassEffectiveScale_pos hW (by positivity)).le
    (mul_pos nativeIntermediateDyadicRatio_pos (actualIntermediateMassEffectiveScale_pos hW hv)).le
    (by norm_num : (3:ℕ) ≠ 0)).mp
  rw [mul_pow,nativeIntermediateDyadicRatio_cube,
    actualIntermediateMassEffectiveScale_cube hW.le (by positivity),
    actualIntermediateMassEffectiveScale_cube hW.le hv.le]
  ring

theorem actualIntermediateMassEffectiveScale_inverse_square {W v : ℝ}
    (hW : 0 < W) (hv : 0 < v) :
    v/(actualIntermediateMassEffectiveScale W v)^2=
      actualIntermediateMassEffectiveScale W v/W^2 := by
  have hB := actualIntermediateMassEffectiveScale_pos hW hv
  have HB := actualIntermediateMassEffectiveScale_cube hW.le hv.le
  apply (div_eq_div_iff (pow_ne_zero 2 hB.ne') (pow_ne_zero 2 hW.ne')).mpr
  nlinarith only [HB]

theorem native_effective_dyadic_sum_le {W v C : ℝ} (hW : 0 < W) (hv : 0 < v)
    (K : ℕ) (hupper : (2:ℝ)^K*v ≤ C*W) :
    (∑j∈Finset.range (K+1),actualIntermediateMassEffectiveScale W ((2:ℝ)^j*v)) ≤
      nativeIntermediateAccumulationConstant C*W := by
  let q := nativeIntermediateDyadicRatio
  let B := actualIntermediateMassEffectiveScale W v
  have hq : 1 < q := nativeIntermediateDyadicRatio_one_lt
  have hB : 0 < B := actualIntermediateMassEffectiveScale_pos hW hv
  have hscale j : actualIntermediateMassEffectiveScale W ((2:ℝ)^j*v)=B*q^j := by
    induction j with
    | zero => simp [B]
    | succ j hj =>
      have hnext : (2:ℝ)^(j+1)*v=2*((2:ℝ)^j*v) := by rw [pow_succ]; ring
      rw [hnext,actualIntermediateMassEffectiveScale_double hW (by positivity),hj]
      dsimp [q]
      rw [pow_succ]
      ring
  have HBupper := (actualIntermediateMassEffectiveScale_upper hW
    (show 0 < (2:ℝ)^K*v by positivity) hupper).1
  rw [hscale] at HBupper
  have Hgeom := geom_sum_mul q (K+1)
  have Hsum : (∑j∈Finset.range (K+1),B*q^j)*(q-1)=B*q^(K+1)-B := by
    rw [←Finset.mul_sum]
    calc
      (B*(∑j∈Finset.range (K+1),q^j))*(q-1)=
          B*((∑j∈Finset.range (K+1),q^j)*(q-1)) := by ring
      _=B*q^(K+1)-B := by rw [Hgeom]; ring
  have Hbound : (∑j∈Finset.range (K+1),B*q^j) ≤ q/(q-1)*(max 1 C*W) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
    have HH := mul_le_mul_of_nonneg_left HBupper (zero_lt_one.trans hq).le
    rw [pow_succ] at Hsum
    nlinarith only [Hsum,HH,hB]
  simp_rw [hscale]
  convert Hbound using 1
  unfold nativeIntermediateAccumulationConstant
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization
