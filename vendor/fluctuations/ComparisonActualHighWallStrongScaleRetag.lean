module

public import ComparisonActualHighWallStarProjectionScalars

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000
set_option linter.unnecessarySeqFocus false
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem test_le_wall_scale_of_strength_lower
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {eta : ℝ} (heta : 0 < eta) (hstrong : eta ≤ M.data.g M.xs/M.xs^2) :
    M.xs ≤ M.data.d/Real.sqrt eta := by
  have H := (le_div_iff₀ (sq_pos_of_pos M.hxs)).mp hstrong
  have Hg := laplaceComparisonStrength_le M.data.d (sq_nonneg M.data.d) M.xs
  change M.data.g M.xs ≤ M.data.d^2 at Hg
  have Hsq : (Real.sqrt eta*M.xs)^2 ≤ M.data.d^2 := by
    rw [mul_pow,Real.sq_sqrt heta.le]
    exact H.trans Hg
  have Hroot := (sq_le_sq₀ (mul_pos (Real.sqrt_pos.mpr heta) M.hxs).le M.data.hd.le).mp Hsq
  exact (le_div_iff₀ (Real.sqrt_pos.mpr heta)).mpr (by simpa only [mul_comm] using Hroot)

def atWallScaleOfStrengthLower
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {eta : ℝ} (heta : 0 < eta) (hAz : 0 ≤ Az) (hsD : M.data.s ≤ M.data.d)
    (hstrong : eta ≤ M.data.g M.xs/M.xs^2) :
    ActualHighWallOverlapMinimum n m delta cl cu (Az/Real.sqrt eta) C0 1 D Bclock where
  data := M.data
  alpha := M.alpha
  minimum := M.minimum
  xs := M.data.d
  z := M.z
  hxs := M.data.hd
  hscale := by
    unfold comparisonLowerScale
    exact (div_le_iff₀ M.data.hd).mpr (by simpa only [pow_two] using M.hupper)
  hsxs := hsD
  hz := M.hz
  hzxs := by
    have H := mul_le_mul_of_nonneg_left (M.test_le_wall_scale_of_strength_lower heta hstrong) hAz
    exact M.hzxs.trans (H.trans_eq (by ring))
  hdD := M.hdD
  hupper := M.hupper
  hlower := M.hlower
  htest := by
    have H := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) M.data.hE.le) M.hupper 2
    rw [mul_pow,Real.sq_sqrt M.data.hN.le] at H
    rw [one_mul,M.data.strength_at_scale]
    convert H using 1 <;> ring
  regular := M.regular
  hT := M.hT

theorem atWallScaleOfStrengthLower_preserves
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {eta : ℝ} (heta : 0 < eta) (hAz : 0 ≤ Az) (hsD : M.data.s ≤ M.data.d)
    (hstrong : eta ≤ M.data.g M.xs/M.xs^2) :
    let Q := M.atWallScaleOfStrengthLower heta hAz hsD hstrong
    Q.data = M.data ∧ HEq Q.alpha M.alpha ∧ Q.xs = M.data.d ∧ Q.z = M.z := by
  exact ⟨rfl,HEq.rfl,rfl,rfl⟩

theorem exists_wall_scale_minimum_with_same_bad_strip
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {eta : ℝ} (heta : 0 < eta) (hAz : 0 ≤ Az) (hsD : M.data.s ≤ M.data.d)
    (hxsD : M.data.d ≤ M.xs) (hstrong : eta ≤ M.data.g M.xs/M.xs^2)
    (hbad : M.alpha.val.val M.xs < cl*M.xs ∨ cu*M.xs < M.alpha.val.val M.xs) :
    ∃ Q : ActualHighWallOverlapMinimum n m delta cl cu (Az/Real.sqrt eta) C0 1 D Bclock,
      Q.data = M.data ∧ HEq Q.alpha M.alpha ∧ Q.xs = Q.data.d ∧ Q.z = M.z ∧
      ∃ r ∈ Icc Q.data.d (Q.data.d/Real.sqrt eta),
        Q.alpha.val.val r < cl*r ∨ cu*r < Q.alpha.val.val r := by
  let Q := M.atWallScaleOfStrengthLower heta hAz hsD hstrong
  exact ⟨Q,rfl,HEq.rfl,rfl,rfl,M.xs,
    ⟨hxsD,M.test_le_wall_scale_of_strength_lower heta hstrong⟩,hbad⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
