module

public import ComparisonActualHighWallVirtualControl

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_controlFactor_continuous
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) :
    Continuous M.controlFactor := by
  let U := comparisonSmallMass M.data.N M.data.E
  let L := comparisonConstraintLength M.data.N M.data.E M.data.d
  let A := comparisonVirtualControlDensity M.data.N delta U L
    M.data.E M.data.d M.alpha.val.val M.data.k
  have hAm : Measurable A :=
    (inverseControlWeight_measurable M.alpha.val.property.2.measurable
      (comparisonFloor_measurable M.data.N delta U)
      (comparisonCap_continuous M.data.N delta U L M.data.E M.data.d).measurable).mul
      ((comparisonCapSlope_continuous M.data.N delta U L
        M.data.E M.data.d).measurable.comp M.alpha.val.property.2.measurable)
  have hAbound r : |A r| ≤ comparisonCapSlope M.data.N delta U L
      M.data.E M.data.d 1 := by
    have hw := inverseControlWeight_mem M.alpha.val.val M.data.k M.data.M r
    change inverseControlWeight M.alpha.val.val M.data.k
      (comparisonCap M.data.N delta U L M.data.E M.data.d) r∈Icc (0:ℝ) 1 at hw
    have hb := comparisonCapSlope_bound (δ:=delta) M.data.hN M.data.hU.le
      M.data.hL M.data.hE M.data.hd.le (M.alpha.val.property.1 r)
    dsimp only [A,comparisonVirtualControlDensity]
    rw [abs_mul,abs_of_nonneg hw.1]
    exact (mul_le_mul_of_nonneg_right hw.2 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hb)
  have hi : ∀a b,IntervalIntegrable A volume a b := by
    intro a b
    rcases le_total a b with hab|hba
    · exact bounded_measurable_intervalIntegrable hab hAm
        (Eventually.of_forall (fun r _=>hAbound r))
    · exact (bounded_measurable_intervalIntegrable hba hAm
        (Eventually.of_forall (fun r _=>hAbound r))).symm
  exact Real.continuous_exp.comp (intervalIntegral.continuous_primitive hi M.data.rmin)

theorem actual_virtual_scaled_factor_data
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {a b ref c C : ℝ} (ha : M.data.rmin ≤ M.xs*a) (hab : a ≤ b)
    (hb : M.xs*b ≤ 1)
    (href : ref∈Icc (M.xs*a) (M.xs*b)) (hc : 0 < c) (hcC : c ≤ C)
    (hlower : c*M.xs ≤ M.alpha.val.val (M.xs*a))
    (hupper : M.alpha.val.val (M.xs*b) ≤ C*M.xs) :
    Continuous (M.actualVirtualScaledFactor ref) ∧
    MonotoneOn (M.actualVirtualScaledFactor ref) (Icc a b) ∧
    ∀t∈Icc a b,M.actualVirtualScaledFactor ref t∈Icc (1/(C/c)^2) ((C/c)^2) := by
  let U := comparisonSmallMass M.data.N M.data.E
  let L := comparisonConstraintLength M.data.N M.data.E M.data.d
  have hK : 1 ≤ C/c := (le_div_iff₀ hc).mpr (by simpa only [one_mul] using hcC)
  have hK0 : 0 ≤ C/c := zero_le_one.trans hK
  have hband : M.alpha.val.val (M.xs*b)+U ≤
      (C/c)*(M.alpha.val.val (M.xs*a)+U) := by
    calc
      _ ≤ C*M.xs+U := add_le_add hupper le_rfl
      _ = (C/c)*(c*M.xs)+U := by field_simp
      _ ≤ (C/c)*M.alpha.val.val (M.xs*a)+(C/c)*U :=
        add_le_add (mul_le_mul_of_nonneg_left hlower hK0)
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hK M.data.hU.le)
      _ = _ := by ring
  obtain ⟨_hi,hmono,hbound⟩ := comparison_virtual_shifted_native_factor_data
    M.data.hN M.data.hU M.data.hL M.data.hE M.data.hd.le
    M.data.hr M.data.hc M.data.hk M.data.hkc
    (comparisonFloor_measurable M.data.N delta U) M.alpha
    ha hb (mul_le_mul_of_nonneg_left hab M.hxs.le) href hK hband
  refine ⟨(M.actual_controlFactor_continuous.comp
    (continuous_const.mul continuous_id)).div_const _,?_,?_⟩
  · intro s hs t ht hst
    apply div_le_div_of_nonneg_right _ (M.actual_controlFactor_pos ref).le
    exact hmono ⟨ha.trans (mul_le_mul_of_nonneg_left hs.1 M.hxs.le),
      (mul_le_mul_of_nonneg_left hs.2 M.hxs.le).trans hb⟩
      ⟨ha.trans (mul_le_mul_of_nonneg_left ht.1 M.hxs.le),
      (mul_le_mul_of_nonneg_left ht.2 M.hxs.le).trans hb⟩
      (mul_le_mul_of_nonneg_left hst M.hxs.le)
  · intro t ht
    exact hbound (M.xs*t) ⟨mul_le_mul_of_nonneg_left ht.1 M.hxs.le,
      mul_le_mul_of_nonneg_left ht.2 M.hxs.le⟩

theorem actual_virtual_moving_factor_data
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 ≤ cu) (hAz : 0 ≤ Az) {B ref c : ℝ} (hB : 0 ≤ B)
    (hc : 0 < c) (href : ref∈Icc M.data.rmin (M.xs*B))
    (hphysical : M.xs*B ≤ 1)
    (hmass : c*M.xs ≤ M.alpha.val.val ref) :
    let K := (c+cu*(B+Az)+1)/c
    1 ≤ K ∧ Continuous (M.actualVirtualMovingFactor ref) ∧
      MonotoneOn (M.actualVirtualMovingFactor ref) (Iic B) ∧
      ∀t≤B,M.actualVirtualMovingFactor ref t∈Icc (1/K^2) (K^2) := by
  let C := c+cu*(B+Az)+1
  have hcC : c ≤ C := by dsimp only [C];linarith [mul_nonneg hcu (add_nonneg hB hAz)]
  have haB : ref/M.xs ≤ B := (div_le_iff₀ M.hxs).mpr
    (by simpa only [mul_comm] using href.2)
  have he : M.xs*(ref/M.xs)=ref := by field_simp [M.hxs.ne']
  have hupper : M.alpha.val.val (M.xs*B) ≤ C*M.xs := by
    let z := max (M.xs*B) M.z
    have hz : z∈Icc M.z 1 := ⟨le_max_right _ _,max_le hphysical M.hz.2⟩
    have hsize : z ≤ (B+Az)*M.xs := by
      apply max_le
      · nlinarith only [mul_nonneg hAz M.hxs.le]
      · nlinarith only [M.hzxs,mul_nonneg hB M.hxs.le]
    have H := (M.alpha.val.property.2 (le_max_left (M.xs*B) M.z)).trans
      (M.regular z hz).2
    have H' := mul_le_mul_of_nonneg_left hsize hcu
    have HC : cu*(B+Az) ≤ C := by dsimp only [C];linarith
    exact H.trans (H'.trans (by nlinarith only [mul_le_mul_of_nonneg_right HC M.hxs.le]))
  have Hdata := M.actual_virtual_scaled_factor_data
    (by simpa only [he] using href.1) haB hphysical
    (by simpa only [he] using (show ref∈Icc ref (M.xs*B) from ⟨le_rfl,href.2⟩))
    hc hcC (by simpa only [he] using hmass) hupper
  have hmax t (ht : t ≤ B) : max (ref/M.xs) t∈Icc (ref/M.xs) B :=
    ⟨le_max_left _ _,max_le haB ht⟩
  refine ⟨(le_div_iff₀ hc).mpr (by simpa only [one_mul] using hcC),
    Hdata.1.comp (continuous_const.max continuous_id),?_,?_⟩
  · intro s hs t ht hst
    exact Hdata.2.1 (hmax s hs) (hmax t ht) (max_le_max_left _ hst)
  · intro t ht
    exact Hdata.2.2 _ (hmax t ht)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
