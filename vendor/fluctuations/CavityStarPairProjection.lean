module

public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalOverlapClockSchedule

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace

namespace OAI.SKFluctuations
open Hierarchy

def physicalOverlapProjectionError (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) (t : ℕ)
    (z : PhysicalPathState P n steps × PhysicalPathState P n steps) : ℝ :=
  orderedOverlap n (ForwardPath.spin steps.length z.1.2)
      (ForwardPath.spin steps.length z.2.2) -
    inner ℝ (actualSpinPath n steps x t z.1) (actualSpinPath n steps x t z.2)

def physicalOverlapProjectionErrorMoment (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (fork t : ℕ) : ℝ :=
  ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
    (fun z => |physicalOverlapProjectionError n steps x t z|^(2*l)) p
      ∂physicalPathLaw μ n steps x hx

theorem physicalOverlapProjectionError_eq_layers (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) (cs : List (ℝ × ℕ)) (t : ℕ)
    (hlast : lastLayerCut cs t = steps.length+1)
    (z : PhysicalPathState P n steps × PhysicalPathState P n steps) :
    physicalOverlapProjectionError n steps x t z =
      ∑ ij ∈ physicalOverlapResidualPairs cs, physicalOverlapLayerTerm n steps x cs t ij z := by
  unfold physicalOverlapProjectionError
  rw [physicalOverlap_core_add_residual n steps x cs t hlast z]
  ring

theorem physicalOverlapProjectionErrorMoment_le_layers (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ}
    (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (fork t : ℕ) (cs : List (ℝ × ℕ))
    (hlast : lastLayerCut cs t = steps.length+1) :
    physicalOverlapProjectionErrorMoment n l steps μ x hx fork t ≤
      ((physicalOverlapResidualPairs cs).card:ℝ)^(2*l-1) *
        ∑ ij ∈ physicalOverlapResidualPairs cs,
          physicalOverlapLayerMoment n l steps μ x hx cs fork t ij.1 ij.2 := by
  have H := fork_sum_power_le (uniformWeight_pos n) (finiteFeature n) steps hc μ x hx fork
    (physicalOverlapResidualPairs cs) (physicalOverlapLayerTerm n steps x cs t)
    (physicalOverlapLayerTerm_measurable n steps hc x hx cs t)
    (physicalOverlapLayerTerm_abs_le n steps hc x cs t) (2*l) (by omega)
  simpa only [physicalOverlapProjectionErrorMoment, physicalOverlapLayerMoment,
    physicalOverlapProjectionError_eq_layers n steps x cs t hlast, physicalPathLaw] using H

theorem eventually_physical_projection_error_clock_schedule (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (c D₀ xs H : ℝ),
      0 < D₀ → 0 < xs → 0 ≤ H → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cs : List (ℝ × ℕ))
      (fork t : ℕ) (a D : Fin cs.length → ℝ),
      t ≤ steps.length+1 → lastLayerCut cs t=steps.length+1 →
      (∀ j : Fin cs.length, cutPredecessor cs t j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1) →
      (∀ j, 0 < a j ∧ D₀ ≤ D j ∧ D j ≤ B ∧
        PhysicalProjectionClock n steps fork (cutPredecessor cs t j) (cs.get j).2 (a j) (D j)) →
      (∀ i j, i ≤ j.succ → xs+physicalCutMass c steps (overlapComponentEnd cs t i) ≤ H*(a j)^2) →
    physicalOverlapProjectionErrorMoment n (k+1) steps μ x hx fork t ≤
      ((physicalOverlapResidualPairs cs).card:ℝ)^(2*(k+1)) *
        (4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4 *
          (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀))^(k+1) := by
  filter_upwards [eventually_physical_overlap_layer_clock_moment k B,
    eventually_ge_atTop 1] with n hn hnpos
  intro P _ steps c D₀ xs H hD₀ hxs hH hs μ _ x hx cs fork t a D ht hlast hends hclock hscale
  have hnp : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let Q := physicalRawRatio n (k+1) steps c xs μ x hx
  let L := 4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*Q^2*H/((n:ℝ)*D₀)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hordered : ∀ (i j : Fin (cs.length+1)), i ≤ j → (i,j)≠(0,0) →
      (physicalOverlapLayerMoment n (k+1) steps μ x hx cs fork t i j)^(((k+1:ℕ):ℝ)⁻¹) ≤ L := by
    intro i j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij hne
      have hi : i=0 := le_antisymm hij (Fin.zero_le _)
      exact False.elim (hne (by simp only [hi]))
    · intro hij _
      obtain ⟨ha,hD,hDB,hclk⟩ := hclock j
      have hh := hn P steps (a j) c (D j) xs ha (hD₀.trans_le hD) hDB hxs hs μ x hx
        cs fork t i j ht hends hclk
      apply hh.trans
      have hm := projection_weight_scale_bound (C := projectionLpConstant k) (z := Real.log (n:ℝ))
        (Q := Q) hnp ha hD₀ hD (show (0:ℝ)≤1 by norm_num)
        (add_nonneg hxs.le (physicalCutMass_mem steps hs (overlapComponentEnd cs t i)).1) hH
        (by simpa only [one_mul] using hscale i j hij)
      simpa only [one_mul] using hm
  have hpairs : ∀ ij ∈ physicalOverlapResidualPairs cs,
      physicalOverlapLayerMoment n (k+1) steps μ x hx cs fork t ij.1 ij.2 ≤ L^(k+1) := by
    intro ij hij
    have hne : ij≠(0,0) := (Finset.mem_erase.mp hij).1
    have hr : (physicalOverlapLayerMoment n (k+1) steps μ x hx cs fork t ij.1 ij.2)^(((k+1:ℕ):ℝ)⁻¹) ≤ L := by
      rcases le_total ij.1 ij.2 with hij' | hji
      · exact hordered ij.1 ij.2 hij' hne
      · rw [physicalOverlapLayerMoment_swap n (k+1) steps hs μ x hx cs fork t ij.1 ij.2]
        apply hordered ij.2 ij.1 hji
        intro heq
        apply hne
        exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    have hp := pow_le_pow_left₀
      (Real.rpow_nonneg (physicalOverlapLayerMoment_nonneg n (k+1) steps μ x hx cs fork t ij.1 ij.2) _) hr (k+1)
    rwa [Real.rpow_inv_natCast_pow
      (physicalOverlapLayerMoment_nonneg n (k+1) steps μ x hx cs fork t ij.1 ij.2) (Nat.succ_ne_zero k)] at hp
  apply (physicalOverlapProjectionErrorMoment_le_layers n (k+1) (Nat.succ_pos k) steps hs μ x hx
    fork t cs hlast).trans
  calc
    _ ≤ ((physicalOverlapResidualPairs cs).card:ℝ)^(2*(k+1)-1) *
        (((physicalOverlapResidualPairs cs).card:ℝ)*L^(k+1)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hpairs
    _ = _ := by
      rw [← mul_assoc, ← pow_succ]
      congr 2

theorem eventually_log_polynomial_saving (d : ℕ) {kappa delta : ℝ}
    (hgap : 2*delta < kappa) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C*(Real.log (n:ℝ))^d*(n:ℝ)^(-kappa) ≤ (n:ℝ)^(-2*delta) := by
  have ht := (tendsto_raw_log_margin d (sub_pos.mpr hgap)).const_mul C
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1)),
    eventually_gt_atTop (0:ℕ)] with n hsmall hn
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have he : C*(Real.log (n:ℝ))^d*(n:ℝ)^(-kappa) =
      (C*((Real.log (n:ℝ))^d*(n:ℝ)^(-(kappa-2*delta))))*(n:ℝ)^(-2*delta) := by
    have hexp : -kappa = -(kappa-2*delta)+(-2*delta) := by ring
    rw [hexp,Real.rpow_add hn0]
    ring
  rw [he]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hsmall
    (Real.rpow_nonneg hn0.le _)

theorem eventually_physical_projection_error_polynomial (k d : ℕ) (B C : ℝ)
    {kappa delta : ℝ} (hgap : 2*delta < kappa) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (c D₀ xs H v : ℝ),
      0 < D₀ → 0 < xs → 0 ≤ H → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cs : List (ℝ × ℕ))
      (fork t : ℕ) (a D : Fin cs.length → ℝ),
      t ≤ steps.length+1 → lastLayerCut cs t=steps.length+1 →
      (∀ j : Fin cs.length, cutPredecessor cs t j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1) →
      (∀ j, 0 < a j ∧ D₀ ≤ D j ∧ D j ≤ B ∧
        PhysicalProjectionClock n steps fork (cutPredecessor cs t j) (cs.get j).2 (a j) (D j)) →
      (∀ i j, i ≤ j.succ → xs+physicalCutMass c steps (overlapComponentEnd cs t i) ≤ H*(a j)^2) →
      ((physicalOverlapResidualPairs cs).card:ℝ)^2 *
        (4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4 *
          (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀)) ≤
        C*(Real.log (n:ℝ))^d*(n:ℝ)^(-kappa)*v^2 →
    physicalOverlapProjectionErrorMoment n (k+1) steps μ x hx fork t ≤
      ((n:ℝ)^(-delta)*v)^(2*(k+1)) := by
  filter_upwards [eventually_physical_projection_error_clock_schedule k B,
    eventually_log_polynomial_saving d hgap C,
    eventually_gt_atTop (0:ℕ)] with n hclockMoment hsave hn
  intro P _ steps c D₀ xs H v hD₀ hxs hH hs μ _ x hx cs fork t a D
    ht hlast hends hclock hscale hbase
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hm := hclockMoment P steps c D₀ xs H hD₀ hxs hH hs μ x hx cs fork t a D
    ht hlast hends hclock hscale
  rw [show 2*(k+1)=2*(k+1) from rfl, pow_mul, ← mul_pow] at hm
  apply hm.trans
  have hsaved := hbase.trans (mul_le_mul_of_nonneg_right hsave (sq_nonneg v))
  have he : (n:ℝ)^(-2*delta)*v^2 = ((n:ℝ)^(-delta)*v)^2 := by
    have hp : ((n:ℝ)^(-delta))^2 = (n:ℝ)^(-2*delta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      norm_num
      ring
    rw [mul_pow,hp]
  rw [he] at hsaved
  convert pow_le_pow_left₀ (by positivity) hsaved (k+1) using 1
  rw [← pow_mul]

end OAI.SKFluctuations
