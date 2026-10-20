module
public import SKConstants.ParisiFullMixedRows

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d N : ℕ}
local instance ParisiFullMixedRowCovariance_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance ParisiFullMixedRowCovariance_localInstance2 (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

def actualParisiFullMixedRowsLaw (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (H : ℝ≥0) (N : ℕ) :
    Measure (Fin N → (Bool × Ω) × A) := Measure.pi (fun _ : Fin N => actualParisiFullQuerySpinLaw W Z β H)
instance actualParisiFullMixedRowsLaw_isProbability (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (H : ℝ≥0) (N : ℕ) : IsProbabilityMeasure (actualParisiFullMixedRowsLaw W Z β H N) := by
  dsimp [actualParisiFullMixedRowsLaw]
  infer_instance

def actualParisiFullMixedRows (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1<β)
    (t q : ℕ → ℝ≥0) (d : ℕ) (i : Fin N) (w : Fin N → (Bool × Ω) × A) :
    EuclideanSpace ℝ (Fin (d+(d+1))) := actualParisiFullMixedRow W Z β hβ t q d (w i)

lemma measurable_actualParisiFullMixedRows (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1<β)
    (t q : ℕ → ℝ≥0) (d : ℕ) (i : Fin N) : Measurable (actualParisiFullMixedRows W Z β hβ t q d i) :=
  (measurable_actualParisiFullMixedRow W Z β hβ t q d).comp (measurable_pi_apply i)

lemma actualParisiFullMixedRows_independent (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1<β)
    (t q : ℕ → ℝ≥0) (d : ℕ) (H : ℝ≥0) :
    iIndepFun (actualParisiFullMixedRows (N:=N) W Z β hβ t q d) (actualParisiFullMixedRowsLaw W Z β H N) :=
  iIndepFun_pi (μ:=fun _ : Fin N=>actualParisiFullQuerySpinLaw W Z β H)
    (X:=fun _ : Fin N=>actualParisiFullMixedRow W Z β hβ t q d)
    (fun _=>(measurable_actualParisiFullMixedRow W Z β hβ t q d).aemeasurable)

def actualParisiFullMixedRowMGFProxy (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) : ℝ≥0 :=
  4*actualParisiPosteriorRowMGFProxy W β V+8

theorem actualParisiFullMixedRows_covariance_operator_variance_tail
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1<β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (n : ℕ) (htn : t n=parisiEquilibriumPhysicalEndpoint β)
    (q : ℕ → ℝ≥0) (hq : StrictMono q) (hq0 : q 0=0) (m : ℕ)
    (g : ℕ → ℝ≥0) (hg : StrictMono g) (H : ℝ≥0) (hN : 0<N) (η : ℝ) (hη : 0<η) :
    (actualParisiFullMixedRowsLaw W Z β H N).real
      {w | 2*η < ‖Concentration.centeredEmpiricalCovariance (actualParisiFullMixedRowsLaw W Z β H N)
        (actualParisiFullMixedRows W Z β hβ (actualParisiJoinedGrid β t n q) g (n+m)) w‖} ≤
      2*(9:ℝ)^((n+m)+((n+m)+1))*Real.exp (-(N:ℝ)*min
        (η^2/(192*Concentration.squareVarianceScale
          (actualParisiFullMixedRowMGFProxy W β (parisiEquilibriumPhysicalEndpoint β+q m):ℝ) 3))
        (η/(8*Concentration.squareVarianceScale
          (actualParisiFullMixedRowMGFProxy W β (parisiEquilibriumPhysicalEndpoint β+q m):ℝ) 3))) := by
  let μ := actualParisiFullQuerySpinLaw W Z β H
  let u := actualParisiJoinedGrid β t n q
  let K := actualParisiFullMixedRowMGFProxy W β (parisiEquilibriumPhysicalEndpoint β+q m)
  have hMGF (i : Fin N) (a : EuclideanSpace ℝ (Fin ((n+m)+((n+m)+1)))) (ha : ‖a‖≤1) :
      HasSubgaussianMGF (fun w=>⟪actualParisiFullMixedRows W Z β hβ u g (n+m) i w,a⟫_ℝ) K
        (actualParisiFullMixedRowsLaw W Z β H N) := by
    apply HasSubgaussianMGF.of_map
      (X:=fun w=>⟪actualParisiFullMixedRow W Z β hβ u g (n+m) w,a⟫_ℝ) (measurable_pi_apply i).aemeasurable
    change HasSubgaussianMGF (fun w=>⟪actualParisiFullMixedRow W Z β hβ u g (n+m) w,a⟫_ℝ) K
      ((Measure.pi (fun _ : Fin N=>μ)).map (Function.eval i))
    rw [(measurePreserving_eval (fun _ : Fin N=>μ) i).map_eq]
    exact actualParisiFullMixedRow_unit_hasSubgaussianMGF W Z β hβ t ht n htn q hq hq0 m g hg H a ha
  have hSecond (i : Fin N) (a : EuclideanSpace ℝ (Fin ((n+m)+((n+m)+1)))) (ha : ‖a‖≤1) :
      (∫w,⟪actualParisiFullMixedRows W Z β hβ u g (n+m) i w,a⟫_ℝ^2
        ∂actualParisiFullMixedRowsLaw W Z β H N)≤3 := by
    have hm : Measurable (fun w=>⟪actualParisiFullMixedRow W Z β hβ u g (n+m) w,a⟫_ℝ^2) := by
      have hm := measurable_actualParisiFullMixedRow W Z β hβ u g (n+m)
      fun_prop
    have he := (measurePreserving_eval (fun _ : Fin N=>μ) i).hasLaw.integral_comp hm.aestronglyMeasurable
    change (∫w,⟪actualParisiFullMixedRows W Z β hβ u g (n+m) i w,a⟫_ℝ^2
        ∂actualParisiFullMixedRowsLaw W Z β H N)=
      ∫w,⟪actualParisiFullMixedRow W Z β hβ u g (n+m) w,a⟫_ℝ^2 ∂μ at he
    rw [he]
    have hB := actualParisiFullMixedRow_secondMoment_le W Z β hβ t ht n htn q hq hq0 m g hg H a
    exact hB.trans (by nlinarith [norm_nonneg a])
  simpa only [show (64:ℝ)*3=192 by norm_num] using
    Concentration.independent_empirical_covariance_operator_variance_tail hN
      (actualParisiFullMixedRows W Z β hβ u g (n+m))
      (actualParisiFullMixedRows_independent W Z β hβ u g (n+m) H)
      (measurable_actualParisiFullMixedRows W Z β hβ u g (n+m)) K
      (by dsimp [K,actualParisiFullMixedRowMGFProxy];positivity) hMGF 3 (by norm_num) hSecond η hη

end SKConstants
