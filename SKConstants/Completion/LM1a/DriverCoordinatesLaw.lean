module
public import SKConstants.Completion.LM1a.GrowingPrimitiveCells
public import SKConstants.Completion.LM1a.PrimitiveRecovery

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.M1
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev DriverCoordinateInput (δ : ℝ≥0) (n q : ℕ) :=
  (Fin n → ScalarContinuousPath (Horizon δ q)) ×
    ((Fin n → ScalarContinuousPath (growingQueryDuration δ 0)) ×
      ((Fin q → EuclideanSpace ℝ (Fin n)) ×
        ((e : Fin q) → Fin n → ScalarContinuousPath (growingQueryDuration δ (e.val+1)))))

def DriverCoordinates (δ : ℝ≥0) (n q : ℕ) (b : DriverRows δ n q) :
    DriverCoordinateInput δ n q :=
  (fun i => (b i).2,
    (fun i => (GrowingPrimitiveCoordinates δ q (b i).1).1,
      (fun e => WithLp.toLp 2 (fun i =>
        ((GrowingPrimitiveCoordinates δ q (b i).1).2 e).1),
       fun e i => ((GrowingPrimitiveCoordinates δ q (b i).1).2 e).2)))

def driverCoordinateLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    Measure (DriverCoordinateInput δ n q) :=
  (Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W (Horizon δ q))).prod
    ((Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W
        (growingQueryDuration δ 0))).prod
      ((Measure.pi (fun _ : Fin q => primitiveGaussian (Fin n))).prod
        (Measure.pi (fun e : Fin q => Measure.pi (fun _ : Fin n =>
          scalarPrimitiveBridgePathLaw W (growingQueryDuration δ (e.val+1)))))))

theorem measurable_DriverCoordinates (δ : ℝ≥0) (n q : ℕ) :
    Measurable (DriverCoordinates δ n q) := by
  have hm (i : Fin n) : Measurable (fun b : DriverRows δ n q =>
      GrowingPrimitiveCoordinates δ q (b i).1) :=
    (measurable_GrowingPrimitiveCoordinates δ q).comp (measurable_pi_apply i).fst
  exact (Measurable.of_eval (fun i => (measurable_pi_apply i).snd)).prodMk
    ((Measurable.of_eval (fun i => (hm i).fst)).prodMk
      ((Measurable.of_eval (fun e => (WithLp.measurable_toLp 2 _).comp
        (Measurable.of_eval (fun i => ((measurable_pi_apply e).comp (hm i).snd).fst)))).prodMk
       (Measurable.of_eval (fun e => Measurable.of_eval (fun i =>
         ((measurable_pi_apply e).comp (hm i).snd).snd)))))

theorem driverCoordinates_law (W : BrownianSystem Ω)
    (δ : ℝ≥0) (hδ : 0 < δ) (n q : ℕ) :
    (driverRowsLaw W δ n q).map (DriverCoordinates δ n q) = driverCoordinateLaw W δ n q := by
  let μ := scalarPrimitiveBrownianPathLaw W (Horizon δ q)
  let α := scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0)
  let γ := gaussianReal 0 1
  let ζ (e : Fin q) := scalarPrimitiveBridgePathLaw W (growingQueryDuration δ (e.val+1))
  have : IsProbabilityMeasure μ := scalarPrimitiveBrownianPathLaw_probability W _
  have : IsProbabilityMeasure α := scalarPrimitiveBrownianPathLaw_probability W _
  have : IsProbabilityMeasure γ := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
  have (e : Fin q) : IsProbabilityMeasure (ζ e) := scalarPrimitiveBridgePathLaw_probability W _
  let D := Measure.pi (fun _ : Fin n => μ)
  let A := Measure.pi (fun _ : Fin n => α)
  have h1 := (Measure.measurePreserving_swap (μ := D) (ν := D)).comp
    (dependentPiProd_law (fun _ : Fin n => μ) (fun _ : Fin n => μ))
  have h2 : MeasurePreserving (fun b : Fin n → ScalarContinuousPath (Horizon δ q) =>
      fun i => GrowingPrimitiveCoordinates δ q (b i)) D
      (Measure.pi (fun _ : Fin n => α.prod (Measure.pi (fun e : Fin q => γ.prod (ζ e))))) :=
    ⟨Measurable.of_eval (fun i => (measurable_GrowingPrimitiveCoordinates δ q).comp
        (measurable_pi_apply i)), growingPrimitiveRowsCoordinates_law W δ hδ q n⟩
  have h3 := dependentPiProd_law (fun _ : Fin n => α)
    (fun _ : Fin n => Measure.pi (fun e : Fin q => γ.prod (ζ e)))
  have h4 : MeasurePreserving
      (fun u : Fin n → (e : Fin q) → ℝ × ScalarContinuousPath
          (growingQueryDuration δ (e.val+1)) => fun e i => u i e)
      (Measure.pi (fun _ : Fin n => Measure.pi (fun e : Fin q => γ.prod (ζ e))))
      (Measure.pi (fun e : Fin q => Measure.pi (fun _ : Fin n => γ.prod (ζ e)))) :=
    ⟨by fun_prop, pi_transpose_law (fun _ : Fin n => fun e : Fin q => γ.prod (ζ e))⟩
  have h5 := measurePreserving_pi _ _ (fun e : Fin q =>
    dependentPiProd_law (fun _ : Fin n => γ) (fun _ : Fin n => ζ e))
  have h6 := dependentPiProd_law
    (fun _ : Fin q => Measure.pi (fun _ : Fin n => γ))
    (fun e : Fin q => Measure.pi (fun _ : Fin n => ζ e))
  have hLp : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      (Measure.pi (fun _ : Fin n => γ)) (primitiveGaussian (Fin n)) :=
    ⟨WithLp.measurable_toLp 2 _, map_pi_eq_stdGaussian⟩
  have h7 := (measurePreserving_pi _ _ (fun _ : Fin q => hLp)).prod
    (MeasurePreserving.id (Measure.pi (fun e : Fin q => Measure.pi (fun _ : Fin n => ζ e))))
  have h4567 := h7.comp (h6.comp (h5.comp h4))
  have hInner := ((MeasurePreserving.id A).prod h4567).comp h3
  have hStart := ((MeasurePreserving.id D).prod h2).comp h1
  have h := ((MeasurePreserving.id D).prod hInner).comp hStart
  exact h.map_eq

end SKConstants.M1
