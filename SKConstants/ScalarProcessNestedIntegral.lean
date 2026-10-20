module

public import SKConstants.ScalarProcessRefiningIntegral
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

structure ScalarDyadicNestedGrid where
  time : ℕ → ℕ → ℝ≥0
  monotone : ∀ l,Monotone (time l)
  embed : ∀ l d i,time (l+d) (i*2^d)=time l i
  zero : ∀ l,time l 0=0

lemma ScalarDyadicNestedGrid.left_le (G : ScalarDyadicNestedGrid) (l d i : ℕ) :
    G.time l (i/2^d) ≤ G.time (l+d) i := by
  rw [← G.embed l d]
  exact G.monotone (l+d) (Nat.div_mul_le_self i _)

lemma ScalarDyadicNestedGrid.coarse_le (G : ScalarDyadicNestedGrid) (l i : ℕ) :
    G.time 0 (i/2^l) ≤ G.time l i := by
  simpa only [zero_add] using G.left_le 0 l i

lemma ScalarDyadicNestedGrid.duration (G : ScalarDyadicNestedGrid) (k l : ℕ) :
    G.time l (k*2^l)=G.time 0 k := by
  simpa only [zero_add] using G.embed 0 l k

lemma ScalarDyadicNestedGrid.le_duration (G : ScalarDyadicNestedGrid) {k l i : ℕ}
    (hi : i ≤ k*2^l) : G.time l i ≤ G.time 0 k :=
  (G.monotone l hi).trans_eq (G.duration k l)

lemma ScalarDyadicNestedGrid.variance_sum (G : ScalarDyadicNestedGrid) (k l : ℕ) :
    (∑ i∈Finset.range (k*2^l),(brownianMeshVariance (G.time l) i : ℝ)) =
      (G.time 0 k : ℝ) := by
  have he (i : ℕ) : (brownianMeshVariance (G.time l) i : ℝ) =
      (G.time l (i+1) : ℝ)-G.time l i := by
    rw [brownianMeshVariance,NNReal.coe_sub (G.monotone l (by omega))]
  simp_rw [he]
  rw [Finset.sum_range_sub (fun i => (G.time l i : ℝ)),G.duration,G.zero,NNReal.coe_zero,sub_zero]

def scalarNestedLagSum {Ω : Type*} (g : ℝ → ℝ) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (G : ScalarDyadicNestedGrid) (k l : ℕ) (u : Bool × Ω) : ℝ :=
  ∑ a ∈ Finset.range (k * 2 ^ l),
    g (G.time l a : ℝ) *
      (Real.tanh (scalarHiddenContinuousField z B (G.time l a) u) -
        Real.tanh (scalarHiddenContinuousField z B (G.time 0 (a / 2 ^ l)) u)) *
      (scalarContinuousInnovation z B (G.time l (a + 1)) u -
        scalarContinuousInnovation z B (G.time l a) u)

def scalarNestedLagCoefficient (g : ℝ → ℝ) (G : ScalarDyadicNestedGrid) (l d : ℕ) :
    ScalarObservationPredictableCoefficient (G.time (l + d)) := fun i w =>
  g (G.time l (i / 2 ^ d) : ℝ) *
    (Real.tanh (w ⟨G.time l (i / 2 ^ d), G.left_le l d i⟩) -
      Real.tanh (w ⟨G.time 0 (i / 2 ^ (l + d)),
        G.coarse_le (l + d) i⟩))

lemma measurable_scalarNestedLagCoefficient (g : ℝ → ℝ) (G : ScalarDyadicNestedGrid) (l d i : ℕ) :
    Measurable (scalarNestedLagCoefficient g G l d i) := by
  exact ((scalar_tanh_lipschitz.continuous.measurable.comp (measurable_pi_apply _)).sub
    (scalar_tanh_lipschitz.continuous.measurable.comp (measurable_pi_apply _))).const_mul _

lemma scalarNestedLagCoefficient_abs_le (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (G : ScalarDyadicNestedGrid) (l d i : ℕ)
    (w : Iic (G.time (l + d) i) → ℝ) :
    |scalarNestedLagCoefficient g G l d i w| ≤ 2 := by
  unfold scalarNestedLagCoefficient
  rw [abs_mul]
  have ht := hg (G.time l (i / 2 ^ d)) (NNReal.coe_nonneg _)
  have hdiff := norm_sub_le (Real.tanh (w ⟨_, G.left_le l d i⟩))
    (Real.tanh (w ⟨_, G.coarse_le (l+d) i⟩))
  simp only [Real.norm_eq_abs] at hdiff
  have h1 := scalar_tanh_abs_le_one (w ⟨_, G.left_le l d i⟩)
  have h2 := scalar_tanh_abs_le_one (w ⟨_, G.coarse_le (l+d) i⟩)
  have hd : |Real.tanh (w ⟨_, G.left_le l d i⟩) -
      Real.tanh (w ⟨_, G.coarse_le (l+d) i⟩)| ≤ 2 := by linarith
  exact (mul_le_mul ht hd (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

lemma scalarNestedLagSum_eq_finerPredictableSum {Ω : Type*} (g : ℝ → ℝ) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (G : ScalarDyadicNestedGrid) (k l d : ℕ) (u : Bool × Ω) :
    scalarNestedLagSum g z B G k l u =
      scalarObservationPredictableSum z B (G.time (l + d))
        (scalarNestedLagCoefficient g G l d) (k * 2 ^ (l + d)) u := by
  let H : ℕ → ℝ := fun a => g (G.time l a : ℝ) *
    (Real.tanh (scalarHiddenContinuousField z B (G.time l a) u) -
      Real.tanh (scalarHiddenContinuousField z B (G.time 0 (a / 2 ^ l)) u))
  let M : ℕ → ℝ := fun i => scalarContinuousInnovation z B (G.time (l+d) i) u
  calc
    scalarNestedLagSum g z B G k l u =
        ∑ a ∈ Finset.range (k * 2 ^ l), H a * (M ((a+1)*2^d) - M (a*2^d)) := by
      simp only [scalarNestedLagSum, H, M, ScalarDyadicNestedGrid.embed]
    _ = ∑ i ∈ Finset.range ((k * 2 ^ l) * 2 ^ d), H (i / 2 ^ d) * (M (i+1)-M i) :=
      sum_weighted_refinement H M _ _ (by positivity)
    _ = scalarObservationPredictableSum z B (G.time (l + d))
        (scalarNestedLagCoefficient g G l d) (k * 2 ^ (l + d)) u := by
      rw [scalarObservationPredictableSum, predictableGaussianSum_eq_range_sum]
      simp only [pow_add, ← Nat.mul_assoc]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [H, M, scalarObservationCoefficient, scalarNestedLagCoefficient,
        scalarActualObservationPast, brownianMeshIncrement, scalarRefining_coarse_div]

lemma memLp_scalarNestedLagSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (G : ScalarDyadicNestedGrid) (k l : ℕ) :
    MemLp (scalarNestedLagSum g z B G k l) 2 (scalarHiddenBrownianLaw z P) := by
  have he : scalarNestedLagSum g z B G k l =
      scalarObservationPredictableSum z B (G.time l)
        (scalarNestedLagCoefficient g G l 0) (k * 2 ^ l) := by
    funext u
    simpa only [Nat.add_zero] using scalarNestedLagSum_eq_finerPredictableSum g z B G k l 0 u
  rw [he]
  exact memLp_scalarObservationPredictableSum P z B hB _ (G.monotone l)
    _ (measurable_scalarNestedLagCoefficient g G l 0) 2
    (fun i w => by simpa only [Real.norm_eq_abs] using scalarNestedLagCoefficient_abs_le g hg G l 0 i w) _

def scalarNestedDifferenceCoefficient (g : ℝ → ℝ) (G : ScalarDyadicNestedGrid) (m l : ℕ) :
    ScalarObservationPredictableCoefficient (G.time (m+l)) := fun i w =>
  g (G.time m (i/2^l) : ℝ) *
    (Real.tanh (w ⟨G.time m (i/2^l), G.left_le m l i⟩) -
      Real.tanh (w ⟨G.time 0 (i/2^(m+l)), G.coarse_le (m+l) i⟩)) -
  g (G.time l (i/2^m) : ℝ) *
    (Real.tanh (w ⟨G.time l (i/2^m), by
        simpa only [Nat.add_comm l m, mem_Iic] using G.left_le l m i⟩) -
      Real.tanh (w ⟨G.time 0 (i/2^(m+l)), G.coarse_le (m+l) i⟩))

lemma measurable_scalarNestedDifferenceCoefficient (g : ℝ → ℝ) (G : ScalarDyadicNestedGrid) (m l i : ℕ) :
    Measurable (scalarNestedDifferenceCoefficient g G m l i) := by
  exact (((scalar_tanh_lipschitz.continuous.measurable.comp (measurable_pi_apply _)).sub
    (scalar_tanh_lipschitz.continuous.measurable.comp (measurable_pi_apply _))).const_mul _).sub
    (((scalar_tanh_lipschitz.continuous.measurable.comp (measurable_pi_apply _)).sub
    (scalar_tanh_lipschitz.continuous.measurable.comp (measurable_pi_apply _))).const_mul _)

lemma scalarNestedDifferenceCoefficient_abs_le (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (G : ScalarDyadicNestedGrid) (m l i : ℕ) (w) :
    |scalarNestedDifferenceCoefficient g G m l i w| ≤ 4 := by
  unfold scalarNestedDifferenceCoefficient
  have H := norm_sub_le
    (g (G.time m (i/2^l)) *
      (Real.tanh (w ⟨_,G.left_le m l i⟩) -
        Real.tanh (w ⟨_,G.coarse_le (m+l) i⟩)))
    (g (G.time l (i/2^m)) *
      (Real.tanh (w ⟨_, by simpa only [Nat.add_comm l m, mem_Iic] using G.left_le l m i⟩) -
        Real.tanh (w ⟨_,G.coarse_le (m+l) i⟩)))
  simp only [Real.norm_eq_abs] at H
  linarith [weighted_tanh_lag_abs_le_two (g (G.time m (i/2^l)))
      (w ⟨_,G.left_le m l i⟩)
      (w ⟨_,G.coarse_le (m+l) i⟩)
      (hg _ (NNReal.coe_nonneg _)),
    weighted_tanh_lag_abs_le_two (g (G.time l (i/2^m)))
      (w ⟨_,by simpa only [Nat.add_comm l m, mem_Iic] using G.left_le l m i⟩)
      (w ⟨_,G.coarse_le (m+l) i⟩)
      (hg _ (NNReal.coe_nonneg _))]

lemma scalarNestedLagSum_difference_eq {Ω : Type*} (g : ℝ → ℝ) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (G : ScalarDyadicNestedGrid) (k m l : ℕ) (u : Bool × Ω) :
    scalarNestedLagSum g z B G k m u - scalarNestedLagSum g z B G k l u =
      scalarObservationPredictableSum z B (G.time (m+l))
        (scalarNestedDifferenceCoefficient g G m l) (k * 2^(m+l)) u := by
  have hm := scalarNestedLagSum_eq_finerPredictableSum g z B G k m l u
  have hl := scalarNestedLagSum_eq_finerPredictableSum g z B G k l m u
  simp only [scalarObservationPredictableSum, predictableGaussianSum_eq_range_sum,
    scalarObservationCoefficient, scalarNestedLagCoefficient, scalarActualObservationPast,
    brownianMeshIncrement] at hm hl
  rw [Nat.add_comm l m] at hl
  rw [hm, hl, scalarObservationPredictableSum, predictableGaussianSum_eq_range_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [scalarObservationCoefficient, scalarNestedDifferenceCoefficient,
    scalarActualObservationPast, brownianMeshIncrement]
  ring

lemma scalarNestedDifferenceCoefficient_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (G : ScalarDyadicNestedGrid) (m l i : ℕ) :
    (∫ u, scalarObservationCoefficient z B (G.time (m+l))
      (scalarNestedDifferenceCoefficient g G m l) i u ^ 2 ∂scalarHiddenBrownianLaw z P) ≤
      8 * (g (G.time m (i/2^l)) - g (G.time l (i/2^m)))^2 +
      4 * |(G.time m (i/2^l) : ℝ) - G.time l (i/2^m)| +
      4 * ((G.time m (i/2^l) : ℝ) - G.time l (i/2^m))^2 := by
  exact integral_weighted_tanh_lag_difference_sq_le P g hg z B hB _ _ _

lemma scalarNestedLagSum_difference_L2_isometry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (G : ScalarDyadicNestedGrid) (k m l : ℕ) :
    (∫ u, (scalarNestedLagSum g z B G k m u -
      scalarNestedLagSum g z B G k l u)^2 ∂scalarHiddenBrownianLaw z P) =
    ∑ i : Fin (k * 2^(m+l)), (brownianMeshVariance (G.time (m+l)) i : ℝ) *
      ∫ u, scalarObservationCoefficient z B (G.time (m+l))
        (scalarNestedDifferenceCoefficient g G m l) i u ^ 2 ∂scalarHiddenBrownianLaw z P := by
  simp_rw [scalarNestedLagSum_difference_eq]
  exact scalarObservationPredictableSum_L2_isometry_sum P z B hB _
    (G.monotone (m+l)) _ (measurable_scalarNestedDifferenceCoefficient g G m l)
    (integrable_scalarObservationCoefficient_sq_of_bounded P z B hB _ _
      (measurable_scalarNestedDifferenceCoefficient g G m l) 4
      (fun i w => by simpa only [Real.norm_eq_abs] using
        scalarNestedDifferenceCoefficient_abs_le g hg G m l i w)) _

lemma scalarNestedLagSum_difference_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (G : ScalarDyadicNestedGrid) (k m l : ℕ) (C : ℝ)
    (hC : ∀ i < k * 2^(m+l),
      (∫ u, scalarObservationCoefficient z B (G.time (m+l))
        (scalarNestedDifferenceCoefficient g G m l) i u ^ 2 ∂scalarHiddenBrownianLaw z P) ≤ C) :
    (∫ u, (scalarNestedLagSum g z B G k m u -
      scalarNestedLagSum g z B G k l u)^2 ∂scalarHiddenBrownianLaw z P) ≤
      (G.time 0 k : ℝ) * C := by
  rw [scalarNestedLagSum_difference_L2_isometry P g hg z B hB G k m l]
  calc
    _ ≤ ∑ i : Fin (k*2^(m+l)), (brownianMeshVariance (G.time (m+l)) i : ℝ) * C :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hC i i.isLt) (NNReal.coe_nonneg _))
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Fin.sum_univ_eq_sum_range (fun i => (brownianMeshVariance (G.time (m+l)) i : ℝ))]
      exact G.variance_sum k (m+l)

lemma scalarNestedDifferenceCoefficient_uniform_energy_small {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (hc : Continuous g) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (G : ScalarDyadicNestedGrid) (k : ℕ)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hleft : ∀ l d i, i < k*2^(l+d) →
      |(G.time (l+d) i : ℝ)-G.time l (i/2^d)| ≤ δ l) (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ l ≥ N, ∀ i < k * 2^(m+l),
      (∫ u, scalarObservationCoefficient z B (G.time (m+l))
        (scalarNestedDifferenceCoefficient g G m l) i u ^ 2 ∂scalarHiddenBrownianLaw z P) ≤ eps := by
  let η := min (1:ℝ) (eps/32)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηeps : η ≤ eps/32 := min_le_right _ _
  have hu : UniformContinuousOn g (Icc 0 (G.time 0 k : ℝ)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨σ,hσ,hgσ⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  have hthreshold : 0 < min η σ / 2 := by positivity
  have hstep := hδ.eventually
    (eventually_lt_nhds hthreshold)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hstep
  refine ⟨N, fun m hm l hl i hi => ?_⟩
  let s := G.time m (i/2^l)
  let t := G.time l (i/2^m)
  let v := G.time (m+l) i
  have hsdist : |(v:ℝ)-s| ≤ δ m :=
    hleft m l i hi
  have htdist : |(v:ℝ)-t| ≤ δ l := by
    simpa only [Nat.add_comm l m] using hleft l m i (by simpa only [Nat.add_comm l m] using hi)
  have hsumη : δ m + δ l < η := by
    have hh1 := hN m hm
    have hh2 := hN l hl
    have hh := min_le_left η σ
    linarith
  have hsumδ : δ m + δ l < σ := by
    have hh1 := hN m hm
    have hh2 := hN l hl
    have hh := min_le_right η σ
    linarith
  have hdist : |(s:ℝ)-t| ≤ δ m + δ l := by
    have hh := abs_sub_le (s:ℝ) v t
    rw [abs_sub_comm (s:ℝ) v] at hh
    linarith
  have hs : s ≤ G.time 0 k :=
    (G.left_le m l i).trans (G.le_duration hi.le)
  have ht : t ≤ G.time 0 k := by
    have htv : t ≤ v := by simpa only [Nat.add_comm l m] using G.left_le l m i
    exact htv.trans (G.le_duration hi.le)
  have hs01 : (s:ℝ) ∈ Icc 0 (G.time 0 k : ℝ) :=
    ⟨s.coe_nonneg, by exact_mod_cast hs⟩
  have ht01 : (t:ℝ) ∈ Icc 0 (G.time 0 k : ℝ) :=
    ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  have hgd : |g s - g t| < η := by
    simpa only [Real.dist_eq] using hgσ s hs01 t ht01 (by
      simpa only [Real.dist_eq] using hdist.trans_lt hsumδ)
  have hgdsq : (g s - g t)^2 ≤ η^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hη.le).mpr hgd.le
  have hstd : |(s:ℝ)-t| ≤ η := (hdist.trans_lt hsumη).le
  have hstdsq : ((s:ℝ)-t)^2 ≤ η^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hη.le).mpr hstd
  have hηsq : η^2 ≤ η := by nlinarith
  have hmoment := scalarNestedDifferenceCoefficient_integral_sq_le P g hg z B hB.toIsPreBrownianReal G m l i
  change _ ≤ 8*(g s-g t)^2+4*|(s:ℝ)-t|+4*((s:ℝ)-t)^2 at hmoment
  exact hmoment.trans (by nlinarith)

lemma scalarNestedLagSum_L2_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (hc : Continuous g) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (G : ScalarDyadicNestedGrid) (k : ℕ)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hleft : ∀ l d i, i < k*2^(l+d) →
      |(G.time (l+d) i : ℝ)-G.time l (i/2^d)| ≤ δ l) :
    ∀ eps > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ l ≥ N,
      (∫ u, (scalarNestedLagSum g z B G k m u -
        scalarNestedLagSum g z B G k l u)^2 ∂scalarHiddenBrownianLaw z P) < eps := by
  intro eps heps
  let T := (G.time 0 k : ℝ)
  have hT : 0 ≤ T := NNReal.coe_nonneg _
  have hT1 : 0 < T+1 := by linarith
  obtain ⟨N,hN⟩ := scalarNestedDifferenceCoefficient_uniform_energy_small P g hg hc z B hB G k δ hδ hleft
    (eps/(T+1)) (div_pos heps hT1)
  refine ⟨N, fun m hm l hl => ?_⟩
  have h := scalarNestedLagSum_difference_integral_sq_le P g hg z B hB G k m l
    (eps/(T+1)) (hN m hm l hl)
  exact h.trans_lt (by
    change T*(eps/(T+1)) < eps
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hT1).mpr
    nlinarith)

theorem scalarNestedLagSum_exists_L2_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (hc : Continuous g) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (G : ScalarDyadicNestedGrid) (k : ℕ)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hleft : ∀ l d i, i < k*2^(l+d) →
      |(G.time (l+d) i : ℝ)-G.time l (i/2^d)| ≤ δ l) :
    ∃ I : Bool × Ω → ℝ, MemLp I 2 (scalarHiddenBrownianLaw z P) ∧
      (∀ l, Integrable (fun u => (scalarNestedLagSum g z B G k l u - I u)^2)
        (scalarHiddenBrownianLaw z P)) ∧
      Tendsto (fun l => ∫ u, (scalarNestedLagSum g z B G k l u - I u)^2
        ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) := by
  let F : ℕ → Lp ℝ 2 (scalarHiddenBrownianLaw z P) := fun l =>
    (memLp_scalarNestedLagSum P g hg z B hB G k l).toLp (scalarNestedLagSum g z B G k l)
  have hcauchy : CauchySeq F := by
    apply Metric.cauchySeq_iff.2
    intro eps heps
    obtain ⟨N,hN⟩ := scalarNestedLagSum_L2_cauchy P g hg hc z B hB G k δ hδ hleft (eps^2) (sq_pos_of_pos heps)
    refine ⟨N,fun m hm l hl => ?_⟩
    have he : dist (F m) (F l)^2 = ∫ u,
        (scalarNestedLagSum g z B G k m u - scalarNestedLagSum g z B G k l u)^2
        ∂scalarHiddenBrownianLaw z P := by
      rw [dist_eq_norm]
      exact norm_toLp_difference_sq_eq_integral
        (memLp_scalarNestedLagSum P g hg z B hB G k m)
        (memLp_scalarNestedLagSum P g hg z B hB G k l)
    have hh := hN m hm l hl
    rw [← he] at hh
    nlinarith [show 0 ≤ dist (F m) (F l) from dist_nonneg]
  obtain ⟨I,hI⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨I,Lp.memLp I,?_,?_⟩
  · intro l
    exact ((memLp_scalarNestedLagSum P g hg z B hB G k l).sub (Lp.memLp I)).integrable_sq
  · have hn : Tendsto (fun l => ‖F l-I‖^2) atTop (𝓝 0) := by
      simpa using ((hI.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => I) atTop (𝓝 I))).norm).pow 2
    have he : (fun l => ∫ u, (scalarNestedLagSum g z B G k l u - I u)^2
        ∂scalarHiddenBrownianLaw z P) = fun l => ‖F l-I‖^2 := by
      funext l
      exact (norm_toLp_sub_sq_eq_integral
        (memLp_scalarNestedLagSum P g hg z B hB G k l) I).symm
    rw [he]
    exact hn

end SKConstants
