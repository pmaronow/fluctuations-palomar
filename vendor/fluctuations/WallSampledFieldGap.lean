module

public import WallFieldBandGap
public import SKFluctuationsOAI.Probability.SKFluctuations.CompletedFeatureKernel

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def sampleMassDurations : ℝ → List PositiveMass → List ℝ≥0
  | _, [] => []
  | a, b::bs => (b.val-a).toNNReal :: sampleMassDurations b.val bs

theorem sampleMassDurations_total {a : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) :
    ((sampleMassDurations a as).map fun (w : ℝ≥0) => (w : ℝ)).sum = partitionEnd a as-a := by
  induction as generalizing a with
  | nil => simp [sampleMassDurations, partitionEnd]
  | cons b bs ih =>
    simp only [sampleMassDurations, List.map_cons, List.sum_cons,
      Real.coe_toNNReal _ (sub_nonneg.mpr ho.2.1), partitionEnd]
    rw [ih ho.2.2]
    ring

theorem sampleMassDurations_mesh {a mesh : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) (hm : PartitionMesh mesh a as) :
    ∀ w ∈ sampleMassDurations a as, (w : ℝ) ≤ mesh := by
  induction as generalizing a with
  | nil => simp [sampleMassDurations]
  | cons b bs ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · rw [Real.coe_toNNReal _ (sub_nonneg.mpr ho.2.1)]
      exact hm.1
    · exact ih ho.2.2 hm.2 w hw

def wallBandSlope (T ε θ d rmin v : ℝ) (n : ℕ) : ℝ :=
  θ*wallLowStrength T ε*wallLowRadius d rmin ε/(22*v*Real.log (n : ℝ))

section
variable {rmin s c : ℝ} {k M : ℝ → ℝ}
variable (hr : rmin ≤ 1) (hs1 : s ≤ 1) (hc : 0 < c)
variable (hk : ContinuousOn k (Icc rmin 1))
variable (hkc : ∀ t ∈ Icc rmin 1, c ≤ k t)
variable (hm : MonotoneOn M (Icc (0 : ℝ) 1)) (hM : 0 ≤ M 1)
variable (g : ℝ → ℝ) (hg : Continuous g)

theorem wallSampledField_gap {T ε θ d v a : ℝ} {n : ℕ}
    (hs : 0 < s) (hn : 0 < n) (hlogn : 1 ≤ Real.log (n : ℝ))
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc (0 : ℝ) 1) (hrmin : 0 ≤ rmin)
    (hvτ : 4*(n : ℝ)^(-(10 : ℝ)) ≤ v) (hvs : v ≤ s)
    (as : List PositiveMass) (ho : MassOrdered a as)
    (ha : a ∈ Icc (s-v) (s-v/4))
    (has : ∀ b ∈ as, b.val ∈ Icc (s-v) (s-v/4))
    (α : inverseIntegralConstraints rmin s k M) :
    List.Forall₂ (fun (duration : ℝ≥0) (st : GaussianStep (FeatureIndex n)) => wallBandSlope T ε θ d rmin v n * (duration : ℝ) ≤
        (st.2 (Sum.inl ⟨0, hn⟩) : ℝ))
      (sampleMassDurations a as)
      (sampleClockSteps (completedPathClock n
        (fun u => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α u).toNNReal)
        (fun u => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ
          ((n : ℝ)^(-(10 : ℝ))) d α u).toNNReal)) a as) := by
  induction as generalizing a with
  | nil => exact List.Forall₂.nil
  | cons b bs ih =>
    apply List.Forall₂.cons
    · change wallBandSlope T ε θ d rmin v n * ((b.val-a).toNNReal : ℝ) ≤
        (((wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ
            ((n : ℝ)^(-(10 : ℝ))) d α b.val).toNNReal -
          (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ
            ((n : ℝ)^(-(10 : ℝ))) d α a).toNNReal : ℝ≥0) : ℝ)
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr ho.2.1), NNReal.coe_sub_def]
      have hh := wallChangedField_dyadic_toNNReal_gap hr hs1 hc hk hkc hm hM g hg
        (d := d) hs (by omega : 1 ≤ n) hlogn hε hθ hrmin hvτ hvs ha (has b (by simp)) ho.2.1 α
      apply le_trans _ (le_max_left _ _)
      convert hh using 1
      unfold wallBandSlope
      ring
    · exact ih ho.2.2 (has b (by simp)) (fun z hz => has z (List.mem_cons_of_mem b hz))

end

theorem wallBandSlope_pos {T ε θ d rmin v : ℝ} {n : ℕ}
    (hε : ε ∈ Ioo 0 T) (hθ : 0 < θ) (hd : d ≠ 0) (hrmin : 0 < rmin)
    (hv : 0 < v) (hlogn : 0 < Real.log (n : ℝ)) :
    0 < wallBandSlope T ε θ d rmin v n := by
  have hc : 0 < wallLowStrength T ε := by
    unfold wallLowStrength
    exact div_pos (lt_min hε.1 (sub_pos.mpr hε.2)) (by norm_num)
  have hr : 0 < wallLowRadius d rmin ε := by
    unfold wallLowRadius
    exact div_pos (mul_pos (sq_pos_of_ne_zero hd) hrmin) (by linarith [hε.1])
  unfold wallBandSlope
  positivity

end OAI.SKFluctuations.LaplaceWindowFormalization
