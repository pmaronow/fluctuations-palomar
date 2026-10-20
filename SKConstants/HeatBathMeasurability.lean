module

public import SKConstants.ContinuousHeatBath
public import SKConstants.TypicalStart

public section
noncomputable section
open scoped Classical Matrix Matrix.Norms.Operator
open MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem continuous_heatBathKernel {n : ℕ} (beta : ℝ) :
    Continuous (heatBathKernel (n := n) beta) :=
  continuous_pi (fun x => continuous_pi (fun y => continuous_heatBathKernel_entry beta x y))

theorem measurable_heatBathKernel {n : ℕ} (beta : ℝ) :
    Measurable (heatBathKernel (n := n) beta) :=
  (continuous_heatBathKernel beta).measurable

theorem measurable_heatBathKernel_entry {n : ℕ} (beta : ℝ) (x y : Spin n) :
    Measurable (fun W : Matrix (Fin n) (Fin n) ℝ => heatBathKernel beta W x y) :=
  (continuous_heatBathKernel_entry beta x y).measurable

theorem continuous_continuousHeatBathSemigroup_joint {n : ℕ} (beta : ℝ) :
    Continuous (fun z : Matrix (Fin n) (Fin n) ℝ × ℝ =>
      continuousHeatBathSemigroup beta z.1 z.2) := by
  unfold continuousHeatBathSemigroup finiteChainSemigroup finiteChainGenerator
  apply NormedSpace.exp_continuous.comp
  exact (continuous_const.mul continuous_snd).smul
    (((continuous_heatBathKernel beta).comp continuous_fst).sub continuous_const)

theorem measurable_continuousHeatBathSemigroup_joint {n : ℕ} (beta : ℝ) :
    Measurable (fun z : Matrix (Fin n) (Fin n) ℝ × ℝ =>
      continuousHeatBathSemigroup beta z.1 z.2) :=
  (continuous_continuousHeatBathSemigroup_joint beta).measurable

/-- The actual total variation from the Gibbs law, starting from state `x`. -/
@[expose] def continuousHeatBathPointTV {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (x : Spin n) : ℝ :=
  finiteTotalVariation (continuousHeatBathSemigroup beta W T x) (gibbsProbability beta W)

theorem continuous_continuousHeatBathPointTV_joint {n : ℕ} (beta : ℝ) (x : Spin n) :
    Continuous (fun z : Matrix (Fin n) (Fin n) ℝ × ℝ =>
      continuousHeatBathPointTV beta z.1 z.2 x) := by
  unfold continuousHeatBathPointTV finiteTotalVariation
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro y _
  exact (((continuous_apply y).comp ((continuous_apply x).comp
    (continuous_continuousHeatBathSemigroup_joint beta))).sub
    ((continuous_gibbsProbability beta y).comp continuous_fst)).abs

theorem measurable_continuousHeatBathPointTV_joint {n : ℕ} (beta : ℝ) (x : Spin n) :
    Measurable (fun z : Matrix (Fin n) (Fin n) ℝ × ℝ =>
      continuousHeatBathPointTV beta z.1 z.2 x) :=
  (continuous_continuousHeatBathPointTV_joint beta x).measurable

theorem continuous_continuousHeatBathPointTV {n : ℕ} (beta T : ℝ) (x : Spin n) :
    Continuous (fun W : Matrix (Fin n) (Fin n) ℝ =>
      continuousHeatBathPointTV beta W T x) :=
  continuous_continuousHeatBathTV beta T x

theorem measurable_continuousHeatBathPointTV {n : ℕ} (beta T : ℝ) :
    Measurable (fun z : Matrix (Fin n) (Fin n) ℝ × Spin n =>
      continuousHeatBathPointTV beta z.1 T z.2) :=
  measurable_from_prod_countable_left (fun x => measurable_continuousHeatBathTV beta T x)

theorem continuousHeatBathPointTV_nonneg {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (x : Spin n) :
    0 ≤ continuousHeatBathPointTV beta W T x :=
  finiteTotalVariation_nonneg _ _

theorem continuousHeatBathPointTV_le_one {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (hT : 0 ≤ T) (x : Spin n) :
    continuousHeatBathPointTV beta W T x ≤ 1 :=
  continuousHeatBathTV_le_one hn beta W T hT x

theorem continuousHeatBathAverageMixing_eq_sum {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) :
    continuousHeatBathAverageMixing beta W T =
      ∑ x, gibbsProbability beta W x * continuousHeatBathPointTV beta W T x := rfl

theorem continuous_continuousHeatBathAverageMixing_joint {n : ℕ} (beta : ℝ) :
    Continuous (fun z : Matrix (Fin n) (Fin n) ℝ × ℝ =>
      continuousHeatBathAverageMixing beta z.1 z.2) := by
  simp only [continuousHeatBathAverageMixing_eq_sum]
  exact continuous_finsetSum _ (fun x _ =>
    ((continuous_gibbsProbability beta x).comp continuous_fst).mul
      (continuous_continuousHeatBathPointTV_joint beta x))

theorem measurable_continuousHeatBathAverageMixing_joint {n : ℕ} (beta : ℝ) :
    Measurable (fun z : Matrix (Fin n) (Fin n) ℝ × ℝ =>
      continuousHeatBathAverageMixing beta z.1 z.2) :=
  (continuous_continuousHeatBathAverageMixing_joint beta).measurable

@[expose] def continuousHeatBathGoodDisorder {n : ℕ} (beta T B : ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {W | continuousHeatBathAverageMixing beta W T ≤ B}

theorem measurableSet_continuousHeatBathGoodDisorder {n : ℕ} (beta T B : ℝ) :
    MeasurableSet (continuousHeatBathGoodDisorder (n := n) beta T B) :=
  measurableSet_le (measurable_continuousHeatBathAverageMixing beta T) measurable_const

@[expose] def continuousHeatBathBadStart {n : ℕ} (beta T delta : ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ × Spin n) :=
  {z | delta < continuousHeatBathPointTV beta z.1 T z.2}

theorem measurableSet_continuousHeatBathBadStart {n : ℕ} (beta T delta : ℝ) :
    MeasurableSet (continuousHeatBathBadStart (n := n) beta T delta) :=
  measurableSet_lt measurable_const (measurable_continuousHeatBathPointTV beta T)

theorem continuousHeatBath_typical_start_bound {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : 0 ≤ T)
    (good : Set (Matrix (Fin n) (Fin n) ℝ)) (hgood : MeasurableSet good)
    (B delta : ℝ) (hB : 0 ≤ B) (hdelta : 0 < delta)
    (haverage : ∀ W ∈ good, continuousHeatBathAverageMixing beta W T ≤ B) :
    (jointGibbsMeasure beta μ).real (continuousHeatBathBadStart beta T delta) ≤
      μ.real goodᶜ + B / delta := by
  apply jointGibbs_typical_start_bound beta μ good hgood
    (fun z => continuousHeatBathPointTV beta z.1 T z.2)
    (measurable_continuousHeatBathPointTV beta T)
    (fun z => continuousHeatBathPointTV_nonneg beta z.1 T z.2)
    (fun z => continuousHeatBathPointTV_le_one hn beta z.1 T hT z.2)
    B delta hB hdelta
  intro W hW
  simpa only [← continuousHeatBathAverageMixing_eq_sum] using haverage W hW

theorem continuousHeatBath_typical_start_bound_of_disorder_bound {n : ℕ}
    (hn : 0 < n) (beta : ℝ)
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : 0 ≤ T)
    (good : Set (Matrix (Fin n) (Fin n) ℝ)) (hgood : MeasurableSet good)
    (B delta eta : ℝ) (hB : 0 ≤ B) (hdelta : 0 < delta)
    (haverage : ∀ W ∈ good, continuousHeatBathAverageMixing beta W T ≤ B)
    (hdisorder : μ.real goodᶜ ≤ eta) :
    (jointGibbsMeasure beta μ).real (continuousHeatBathBadStart beta T delta) ≤
      eta + B / delta :=
  (continuousHeatBath_typical_start_bound hn beta μ T hT good hgood B delta hB hdelta
    haverage).trans (add_le_add hdisorder le_rfl)

theorem continuousHeatBath_typical_start_bound_from_average {n : ℕ} (hn : 0 < n)
    (beta : ℝ) (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : 0 ≤ T) (B delta : ℝ) (hB : 0 ≤ B) (hdelta : 0 < delta) :
    (jointGibbsMeasure beta μ).real (continuousHeatBathBadStart beta T delta) ≤
      μ.real (continuousHeatBathGoodDisorder beta T B)ᶜ + B / delta :=
  continuousHeatBath_typical_start_bound hn beta μ T hT
    (continuousHeatBathGoodDisorder beta T B)
    (measurableSet_continuousHeatBathGoodDisorder beta T B) B delta hB hdelta
    (fun _ hW => hW)

end SKConstants
