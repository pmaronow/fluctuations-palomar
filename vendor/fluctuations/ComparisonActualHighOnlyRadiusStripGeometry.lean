module

public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonNativeActualRadiusStripGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def actualRadiusTargetStrip
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (c C : ℝ) : Set ℝ :=
  {r | r∈Icc (0:ℝ) (min (C*M.xs) 1) ∧
    c*M.xs ≤ M.alpha.val.val r ∧ M.alpha.val.val r ≤ C*M.xs}

def actualRadiusStripLower
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (c : ℝ) : ℝ :=
  M.R (c*M.xs)

def actualRadiusStripUpper
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (c C : ℝ) : ℝ :=
  max M.xs (max (M.actualRadiusStripLower c) (C*M.xs))

theorem actual_radius_target_strip_measurable
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (c C : ℝ) :
    MeasurableSet (M.actualRadiusTargetStrip c C) := by
  exact measurableSet_Icc.inter ((measurableSet_le measurable_const M.alpha.val.property.2.measurable).inter
    (measurableSet_le M.alpha.val.property.2.measurable measurable_const))

theorem actual_radius_target_strip_subset
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (c C : ℝ) :
    M.actualRadiusTargetStrip c C ⊆
      Icc (M.actualRadiusStripLower c) (M.actualRadiusStripUpper c C) := by
  intro r hr
  have hr1 : r∈Icc (0:ℝ) 1 := ⟨hr.1.1,hr.1.2.trans (min_le_right _ _)⟩
  have hinv := omittedSweepQuantile_inverse zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hr1
  have hmono := omittedSweepQuantile_monotone zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hr.2.1
  refine ⟨?_,?_⟩
  · exact hmono.trans_eq hinv
  · exact (hr.1.2.trans (min_le_left _ _)).trans
      ((le_max_right _ _).trans (le_max_right _ _))

theorem actual_radius_strip_geometry
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {c C : ℝ} (hc : 0 < c)
    (hcx : c*M.xs ≤ 1) (hsize : actualRadiusStripConstant cl Az c C*M.xs ≤ 1)
    (hhigh : M.data.s<c*M.xs) :
    0 < M.actualRadiusStripLower c ∧
    M.actualRadiusStripLower c ≤ M.actualRadiusStripUpper c C ∧
    M.actualRadiusStripUpper c C ≤ 1 ∧
    M.xs ≤ M.actualRadiusStripUpper c C ∧
    M.actualRadiusStripUpper c C ≤ actualRadiusStripConstant cl Az c C*M.xs ∧
    M.alpha.val.val (M.actualRadiusStripLower c)=c*M.xs ∧
    M.actualRadiusTargetStrip c C ⊆
      Icc (M.actualRadiusStripLower c) (M.actualRadiusStripUpper c C) := by
  have hu : c*M.xs∈Icc (0:ℝ) 1 := ⟨(mul_pos hc M.hxs).le,hcx⟩
  have ha : M.actualRadiusStripLower c ≤ ((Az+1/cl)*(1+c))*M.xs := by
    exact (M.inverse_radius_le_source_mass hcl hAz hu).trans_eq (by ring)
  have haC : M.actualRadiusStripLower c ≤ actualRadiusStripConstant cl Az c C*M.xs :=
    ha.trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) M.hxs.le)
  have hCC : C*M.xs ≤ actualRadiusStripConstant cl Az c C*M.xs :=
    mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) M.hxs.le
  have hxC : M.xs ≤ actualRadiusStripConstant cl Az c C*M.xs := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (actual_radius_strip_constant_ge_one cl Az c C) M.hxs.le
  have hzC : M.actualRadiusStripUpper c C ≤ actualRadiusStripConstant cl Az c C*M.xs :=
    max_le hxC (max_le haC hCC)
  have hspec:=omittedSweepQuantile_spec zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
    M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha
    (show c*M.xs∈Icc M.data.s 1 from ⟨hhigh.le,hcx⟩)
  change M.alpha.val.val (M.R (c*M.xs))=c*M.xs at hspec
  have hrpos:0<M.actualRadiusStripLower c:=by
    have hr0:=(omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
      M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha (c*M.xs)).1
    by_contra H
    have he:M.R (c*M.xs)=0:=le_antisymm (not_lt.mp H) hr0
    rw [he,M.alpha.property.1] at hspec
    exact hhigh.ne hspec
  exact ⟨hrpos,
    (le_max_left _ _).trans (le_max_right _ _),hzC.trans hsize,le_max_left _ _,hzC,
    omittedSweepQuantile_spec zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha (show c*M.xs∈Icc M.data.s 1 from ⟨hhigh.le,hcx⟩),M.actual_radius_target_strip_subset c C⟩

theorem actual_radius_strip_upper_mass_le
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 ≤ cu) (hAz : 0 ≤ Az) {c C : ℝ}
    (hz : M.actualRadiusStripUpper c C ≤ 1)
    (hsize : M.actualRadiusStripUpper c C ≤ actualRadiusStripConstant cl Az c C*M.xs) :
    M.alpha.val.val (M.actualRadiusStripUpper c C) ≤
      cu*(actualRadiusStripConstant cl Az c C+Az)*M.xs := by
  let t := max (M.actualRadiusStripUpper c C) M.z
  have ht : t∈Icc M.z 1 := ⟨le_max_right _ _,max_le hz M.hz.2⟩
  have hC : 0 ≤ actualRadiusStripConstant cl Az c C :=
    zero_le_one.trans (actual_radius_strip_constant_ge_one cl Az c C)
  have htbound : t ≤ (actualRadiusStripConstant cl Az c C+Az)*M.xs := by
    apply max_le
    · nlinarith only [hsize,mul_nonneg hAz M.hxs.le]
    · nlinarith only [M.hzxs,mul_nonneg hC M.hxs.le]
  have H := (M.alpha.val.property.2 (le_max_left (M.actualRadiusStripUpper c C) M.z)).trans
    (M.regular t ht).2
  exact H.trans ((mul_le_mul_of_nonneg_left htbound hcu).trans_eq (by ring))

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
