module

public import CavityWeightedExteriorMoments
public import CavityTerminalResamplingTree
public import SKFluctuationsOAI.Probability.SKFluctuations.ComparisonMinimumRegularRawRatio

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

def physicalWeightedExteriorAnchor (n : ℕ) {steps : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) steps)
    (H : T.Assignment → ℝ) (s : T.Slot) (x : FeatureIndex n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  T.weightedExteriorVector (uniformWeight n) (finiteFeature n) H
    (fun σ=>WithLp.toLp 2 (normalizedSpin n (T.atSlot σ s))) x

theorem physicalWeightedExteriorAnchor_continuous (n : ℕ)
    {steps : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) steps)
    {a : ℝ} (hs : OrderedSteps a steps) (H : T.Assignment → ℝ) (s : T.Slot) :
    Continuous (physicalWeightedExteriorAnchor n T H s) := by
  unfold physicalWeightedExteriorAnchor ReplicaTree.weightedExteriorVector
  apply continuous_finset_sum
  intro σ _
  exact ((T.weight_smooth (uniformWeight_pos n) (finiteFeature n) hs 0 σ).continuous.mul
    continuous_const).smul continuous_const

theorem physicalWeightedExteriorAnchor_norm_le (n : ℕ)
    {steps : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) steps)
    {a : ℝ} (hs : OrderedSteps a steps) (H : T.Assignment → ℝ) (s : T.Slot)
    (x : FeatureIndex n → ℝ) :
    ‖physicalWeightedExteriorAnchor n T H s x‖≤
      ∑ σ, |H σ| * ‖WithLp.toLp 2 (normalizedSpin n (T.atSlot σ s))‖ := by
  unfold physicalWeightedExteriorAnchor ReplicaTree.weightedExteriorVector
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro σ hσ
  have hn := T.weight_nonneg (uniformWeight_pos n) (finiteFeature n) hs σ x
  have hb : T.weight (uniformWeight n) (finiteFeature n) σ x≤1 := by
    rw [←T.weight_sum (uniformWeight_pos n) (finiteFeature n) hs x]
    exact Finset.single_le_sum (fun τ _=>T.weight_nonneg (uniformWeight_pos n) (finiteFeature n) hs τ x) hσ
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hn]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (abs_nonneg (H σ))) (norm_nonneg _)

theorem physical_weighted_exterior_anchor_moment (n l : ℕ)
    {steps : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) steps)
    {a : ℝ} (hs : OrderedSteps a steps) (H : T.Assignment → ℝ) (s : T.Slot)
    (x : FeatureIndex n → ℝ) :
    ‖physicalWeightedExteriorAnchor n T H s x‖^(4*l)≤
      T.expect (uniformWeight n) (finiteFeature n) (fun σ=>|H σ|^(4*l)) x*
        levelPairMean (uniformWeight n) (finiteFeature n)
          (fun σ τ=>|orderedOverlap n σ τ|^(2*l)) steps 0 x := by
  have hp := T.weighted_exterior_vector_even (uniformWeight_pos n) (finiteFeature n) hs
    H (fun σ=>WithLp.toLp 2 (normalizedSpin n (T.atSlot σ s))) x l
  simp_rw [normalizedSpin_inner_eq_overlap] at hp
  have he : (T.fork T).expect (uniformWeight n) (finiteFeature n)
      (fun σ=>|orderedOverlap n (T.atSlot σ.1 s) (T.atSlot σ.2 s)|^(2*l)) x=
      levelPairMean (uniformWeight n) (finiteFeature n)
        (fun σ τ=>|orderedOverlap n σ τ|^(2*l)) steps 0 x := by
    rw [ReplicaTree.expect_fork]
    have hi := funext fun σ=>T.expect_atSlot (uniformWeight_pos n) (finiteFeature n) hs s
      (fun τ=>|orderedOverlap n (T.atSlot σ s) τ|^(2*l)) x
    rw [hi,T.expect_atSlot (uniformWeight_pos n) (finiteFeature n) hs s
      (fun σ=>gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
        (fun τ=>|orderedOverlap n σ τ|^(2*l)) steps x) x]
    rw [←hierarchyPairMean_eq_nested (uniformWeight_pos n) (finiteFeature n)
      (fun σ τ=>|orderedOverlap n σ τ|^(2*l)) steps hs]
    cases steps <;> rfl
  rw [he] at hp
  exact hp

theorem physical_weighted_target_pair_test (n : ℕ)
    {steps : List (GaussianStep (FeatureIndex n))}
    (E U : ReplicaTree (FeatureIndex n) (Spin n) steps)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (Z : U.Assignment → ℝ) (a c : U.Slot) (x : FeatureIndex n → ℝ) :
    (E.fork U).expect (uniformWeight n) (finiteFeature n) (fun σ=>Z σ.2*H σ.1*
      (orderedOverlap n (U.atSlot σ.2 a) (E.atSlot σ.1 s)-
        orderedOverlap n (U.atSlot σ.2 c) (E.atSlot σ.1 s))) x=
    U.expect (uniformWeight n) (finiteFeature n) (fun σ=>Z σ*
      inner ℝ (WithLp.toLp 2 (normalizedSpin n (U.atSlot σ a))-
        WithLp.toLp 2 (normalizedSpin n (U.atSlot σ c)))
        (physicalWeightedExteriorAnchor n E H s x)) x := by
  have he := E.weighted_exterior_average (uniformWeight n) (finiteFeature n) U H
    (fun σ=>WithLp.toLp 2 (normalizedSpin n (E.atSlot σ s))) Z
    (fun σ=>WithLp.toLp 2 (normalizedSpin n (U.atSlot σ a))-
      WithLp.toLp 2 (normalizedSpin n (U.atSlot σ c))) x
  simpa only [physicalWeightedExteriorAnchor,inner_sub_left,normalizedSpin_inner_eq_overlap] using he

private theorem smooth_comp_sqrt_memLp {ι P : Type*} [Fintype ι]
    [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) {A : (ι → ℝ) → ℝ}
    (hA : BddSmooth 0 A) (hAn : ∀ y, 0≤A y) :
    MemLp (fun p=>Real.sqrt (A (x p))) 2 μ := by
  obtain ⟨R,_,hR⟩ := hA.bound
  apply MemLp.of_bound ((hA.continuous.measurable.comp hx).sqrt).aestronglyMeasurable (Real.sqrt R)
  apply Eventually.of_forall
  intro p
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,Function.comp_apply] using hR (x p))

theorem physicalOverlapMoment_eq_root_pair (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (hs : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    physicalOverlapMoment n l steps μ x hx 0=
      ∫ p, levelPairMean (uniformWeight n) (finiteFeature n)
        (fun σ τ=>|orderedOverlap n σ τ|^(2*l)) steps 0 (x p) ∂μ := by
  exact integral_terminalFork_eq_levelPairMean (uniformWeight_pos n) (finiteFeature n)
    steps hs μ x hx 0 (Nat.zero_le _) (fun σ τ=>|orderedOverlap n σ τ|^(2*l))

theorem physical_weighted_exterior_anchor_integral_moment (n l : ℕ)
    {steps : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) steps)
    {a : ℝ} (hs : OrderedSteps a steps) (H : T.Assignment → ℝ) (s : T.Slot)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    (∫ p, ‖physicalWeightedExteriorAnchor n T H s (x p)‖^(4*l) ∂μ)≤
      Real.sqrt (∫ p, T.expect (uniformWeight n) (finiteFeature n)
        (fun σ=>|H σ|^(8*l)) (x p) ∂μ)*
      Real.sqrt (physicalOverlapMoment n (2*l) steps μ x hx 0) := by
  let A := T.expect (uniformWeight n) (finiteFeature n) (fun σ=>|H σ|^(8*l))
  let B := (T.fork T).expect (uniformWeight n) (finiteFeature n)
    (fun σ=>|orderedOverlap n (T.atSlot σ.1 s) (T.atSlot σ.2 s)|^(4*l))
  have hAn (y) : 0≤A y := T.expect_nonneg (uniformWeight_pos n) (finiteFeature n) hs
    (fun _=>pow_nonneg (abs_nonneg _) _) y
  have hBn (y) : 0≤B y := (T.fork T).expect_nonneg (uniformWeight_pos n) (finiteFeature n) hs
    (fun _=>pow_nonneg (abs_nonneg _) _) y
  have hAs := T.expect_smooth (uniformWeight_pos n) (finiteFeature n) hs (fun σ=>|H σ|^(8*l)) 0
  have hBs := (T.fork T).expect_smooth (uniformWeight_pos n) (finiteFeature n) hs
    (fun σ=>|orderedOverlap n (T.atSlot σ.1 s) (T.atSlot σ.2 s)|^(4*l)) 0
  have hAf := smooth_comp_sqrt_memLp μ x hx hAs hAn
  have hBf := smooth_comp_sqrt_memLp μ x hx hBs hBn
  have hprod : MemLp (fun p=>Real.sqrt (A (x p))*Real.sqrt (B (x p))) 1 μ := hAf.mul hBf
  have hpoint (p) : ‖physicalWeightedExteriorAnchor n T H s (x p)‖^(4*l)≤
      Real.sqrt (A (x p))*Real.sqrt (B (x p)) := by
    apply le_trans _ (Real.sqrt_mul (hAn _) _).le
    apply (Real.le_sqrt (by positivity) (mul_nonneg (hAn _) (hBn _))).mpr
    have hp := T.weighted_exterior_vector_even (uniformWeight_pos n) (finiteFeature n) hs
      H (fun σ=>WithLp.toLp 2 (normalizedSpin n (T.atSlot σ s))) (x p) (2*l)
    simp_rw [normalizedSpin_inner_eq_overlap] at hp
    simpa only [physicalWeightedExteriorAnchor,pow_mul,show 4*(2*l)=8*l by omega,
      show 2*(2*l)=4*l by omega,A,B,←pow_mul,show (4*l)*2=8*l by omega] using hp
  have hi := integral_mono_of_nonneg (Eventually.of_forall fun _=>by positivity)
    (memLp_one_iff_integrable.mp hprod) (Eventually.of_forall hpoint)
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun p=>Real.sqrt_nonneg (A (x p)))
    (Eventually.of_forall fun p=>Real.sqrt_nonneg (B (x p))) (by simpa using hAf) (by simpa using hBf)
  simp only [Real.rpow_two,Real.sq_sqrt (hAn _),Real.sq_sqrt (hBn _)] at hc
  rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow] at hc
  have hpair (y) : B y=levelPairMean (uniformWeight n) (finiteFeature n)
      (fun σ τ=>|orderedOverlap n σ τ|^(4*l)) steps 0 y := by
    dsimp only [B]
    rw [ReplicaTree.expect_fork]
    have hinner := funext fun σ=>T.expect_atSlot (uniformWeight_pos n) (finiteFeature n) hs s
      (fun τ=>|orderedOverlap n (T.atSlot σ s) τ|^(4*l)) y
    rw [hinner,T.expect_atSlot (uniformWeight_pos n) (finiteFeature n) hs s
      (fun σ=>gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
        (fun τ=>|orderedOverlap n σ τ|^(4*l)) steps y) y]
    rw [←hierarchyPairMean_eq_nested (uniformWeight_pos n) (finiteFeature n)
      (fun σ τ=>|orderedOverlap n σ τ|^(4*l)) steps hs]
    cases steps <;> rfl
  simp_rw [hpair] at hi hc
  rw [physicalOverlapMoment_eq_root_pair n (2*l) steps hs μ x hx]
  simpa only [A,show 2*(2*l)=4*l by omega] using hi.trans hc

end OAI.SKFluctuations

namespace OAI.SKFluctuations
open Hierarchy

theorem eventually_physical_weighted_exterior_terminal_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n)))
      (T : ReplicaTree (FeatureIndex n) (Spin n) steps)
      (H : T.Assignment → ℝ) (s : T.Slot)
      (tail pre skip : List (GaussianStep (FeatureIndex n))) (a a₀ aₑ D : ℝ),
      0<a → 0<D → D≤B → OrderedSteps a (pre++tail) →
      OrderedSteps a₀ ((skip++pre)++tail) → OrderedSteps aₑ steps →
    ∀ (μ : Measure P) [IsFiniteMeasure μ]
      (xₑ x : P → FeatureIndex n → ℝ) (hxₑ : Measurable xₑ) (hx : Measurable x)
      (d : Fin pre.length → ℝ), (∀ j, 0≤d j) → (∑ j, d j=D) →
      (∀ j i, (hierarchyClocks pre j (Sum.inl i):ℝ)=d j) →
    (∫ p, |∑ i, (physicalWeightedExteriorAnchor n T H s (xₑ p.1)) i*
      physicalTerminalIncrement n tail (skip++pre) x p i|^(4*(k+1))
      ∂physicalPathLaw μ n ((skip++pre)++tail) x hx)≤
      (projectionLpConstant (2*k+1)*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(4*(k+1))*
        Real.sqrt (∫ p, T.expect (uniformWeight n) (finiteFeature n)
          (fun σ=>|H σ|^(8*(k+1))) (xₑ p) ∂μ)*
        Real.sqrt (physicalOverlapMoment n (2*(k+1)) steps μ xₑ hxₑ 0) := by
  filter_upwards [eventually_physical_suffix_terminal_projection (2*k+1) B] with n hn
  intro P _ steps T H s tail pre skip a a₀ aₑ D ha hD hDB ho hs hₑ μ _ xₑ x hxₑ hx d hd hdD hc
  let V : P → Fin n → ℝ := fun p i=>physicalWeightedExteriorAnchor n T H s (xₑ p) i
  have hV : Measurable V := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i).comp
      ((WithLp.measurable_ofLp 2 (Fin n → ℝ)).comp
        ((physicalWeightedExteriorAnchor_continuous n T hₑ H s).measurable.comp hxₑ))
  let R := ∑ σ, |H σ| * ‖WithLp.toLp 2 (normalizedSpin n (T.atSlot σ s))‖
  have hI : Integrable (fun p=>(projectionEuclideanNorm n (V p))^(2*(2*k+1)+2)) μ := by
    apply Integrable.of_bound (((projectionEuclideanNorm_measurable n).comp hV).pow_const _).aestronglyMeasurable
      (R^(2*(2*k+1)+2))
    apply Eventually.of_forall
    intro p
    change ‖(projectionEuclideanNorm n (fun i=>physicalWeightedExteriorAnchor n T H s (xₑ p) i))^
      (2*(2*k+1)+2)‖≤R^(2*(2*k+1)+2)
    rw [projectionEuclideanNorm_coe,Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (physicalWeightedExteriorAnchor_norm_le n T hₑ H s _) _
  have hp := hn P tail pre skip a a₀ D ha hD hDB ho hs μ V hV x hx hI
    (fun p=>alignedFieldClock_of_physical n pre d hd D hdD hc (V p))
  have he : 2*(2*k+1)+2=4*(k+1) := by omega
  simp only [he,V,projectionEuclideanNorm_coe] at hp
  apply hp.trans
  have hcoef : 0≤(projectionLpConstant (2*k+1)*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(4*(k+1)) :=
    pow_nonneg (div_nonneg (mul_nonneg (projectionLpConstant_pos _).le (sq_nonneg _))
      (mul_nonneg ha.le (Real.sqrt_nonneg _))) _
  have hA := mul_le_mul_of_nonneg_left
    (physical_weighted_exterior_anchor_integral_moment n (k+1) T hₑ H s μ xₑ hxₑ)
    hcoef
  simpa only [mul_assoc] using hA

end OAI.SKFluctuations
