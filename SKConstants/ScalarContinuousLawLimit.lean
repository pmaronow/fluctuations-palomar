module
public import SKConstants.ScalarWeightedGaussianFamilies

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SKConstants

theorem scalarLaw_eq_of_ae_tendsto_comparison
    {Ω A E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (Xn : ℕ → Ω → E) (Yn : ℕ → A → E) (X : Ω → E) (Y : A → E)
    (hXn : ∀ n,AEMeasurable (Xn n) P) (hYn : ∀ n,AEMeasurable (Yn n) Q)
    (hlaw : ∀ n,P.map (Xn n)=Q.map (Yn n))
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (hx : ∀ᵐ w ∂P,Tendsto (fun n => Xn n w) atTop (𝓝 (X w)))
    (hy : ∀ᵐ w ∂Q,Tendsto (fun n => Yn n w) atTop (𝓝 (Y w))) :
    P.map X=Q.map Y := by
  have : IsProbabilityMeasure (P.map X) := (Measure.isProbabilityMeasure_map_iff hX).mpr inferInstance
  have : IsProbabilityMeasure (Q.map Y) := (Measure.isProbabilityMeasure_map_iff hY).mpr inferInstance
  have he : (⟨P.map X,inferInstance⟩ : FiniteMeasure E)=⟨Q.map Y,inferInstance⟩ := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    have hxl : Tendsto (fun n => ∫ w,f (Xn n w) ∂P) atTop (𝓝 (∫ w,f (X w) ∂P)) :=
      tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun n => (f.continuous.measurable.comp_aemeasurable (hXn n)).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ (fun w => f.norm_coe_le_norm _))
        (hx.mono (fun w hw => f.continuous.continuousAt.tendsto.comp hw))
    have hyl : Tendsto (fun n => ∫ w,f (Yn n w) ∂Q) atTop (𝓝 (∫ w,f (Y w) ∂Q)) :=
      tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun n => (f.continuous.measurable.comp_aemeasurable (hYn n)).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ (fun w => f.norm_coe_le_norm _))
        (hy.mono (fun w hw => f.continuous.continuousAt.tendsto.comp hw))
    have hei (n : ℕ) : (∫ w,f (Xn n w) ∂P)=∫ w,f (Yn n w) ∂Q := by
      rw [←integral_map (hXn n) f.continuous.measurable.aestronglyMeasurable,
        hlaw n,integral_map (hYn n) f.continuous.measurable.aestronglyMeasurable]
    change (∫ x,f x ∂P.map X)=(∫ x,f x ∂Q.map Y)
    rw [integral_map hX f.continuous.measurable.aestronglyMeasurable,
      integral_map hY f.continuous.measurable.aestronglyMeasurable]
    exact tendsto_nhds_unique hxl (by simpa only [hei] using hyl)
  exact congrArg (fun μ : FiniteMeasure E => (μ:Measure E)) he

end SKConstants
