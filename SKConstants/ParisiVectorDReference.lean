module
public import SKConstants.BrownianVectorContinuousReference
public import SKConstants.ParisiSpinLinkCoefficient

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

abbrev BrownianVectorPastField (A ι : Type*) :=
  (s : ℝ≥0) → A × (Iic s → ι → ℝ) → ι → ℝ

def actualParisiVectorDCoefficient {A ι : Type*} (β : ℝ) (x : A → ι → Bool)
    (g : ℝ≥0 → ℝ) (Y : BrownianVectorPastField A ι) :
    BrownianVectorContinuousPastCoefficient A ι := fun s u i =>
  g s * actualParisiSpinLinkCoefficient β (x u.1 i) s (Y s u i)

lemma measurable_actualParisiVectorDCoefficient {A ι : Type*} [MeasurableSpace A]
    (β : ℝ) (x : A → ι → Bool) (hx : Measurable x) (g : ℝ≥0 → ℝ)
    (Y : BrownianVectorPastField A ι) (hY : ∀ s, Measurable (Y s)) (s : ℝ≥0) :
    Measurable (actualParisiVectorDCoefficient β x g Y s) := by
  apply Measurable.of_eval
  intro i
  have hy : Measurable (fun u => Y s u i) := (measurable_pi_apply i).comp (hY s)
  have hb : Measurable (fun u : A × (Iic s → ι → ℝ) => scalarHiddenSign (x u.1 i)) :=
    (measurable_of_finite scalarHiddenSign).comp
      (((measurable_pi_apply i).comp hx).comp measurable_fst)
  have hm : Measurable (fun u => actualParisiFullMagnetization β s (Y s u i)) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp hy
  have ha : Measurable (fun u => actualParisiFullCurvature β s (Y s u i)) :=
    ((continuous_actualParisiFullCurvature β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp hy
  exact ((hb.mul ha).div (measurable_const.add (hb.mul hm))).const_mul _

lemma actualParisiVectorDCoefficient_bound {A ι : Type*}
    (β : ℝ) (x : A → ι → Bool) (g : ℝ≥0 → ℝ) (hg : ∀ s, ‖g s‖ ≤ 1)
    (Y : BrownianVectorPastField A ι) (s : ℝ≥0) (u : A × (Iic s → ι → ℝ)) (i : ι) :
    ‖actualParisiVectorDCoefficient β x g Y s u i‖ ≤ 2 := by
  rw [actualParisiVectorDCoefficient,norm_mul]
  have hξ : ‖actualParisiSpinLinkCoefficient β (x u.1 i) s (Y s u i)‖ ≤ 2 :=
    actualParisiSpinLinkCoefficient_bound _ _ _ _
  exact (mul_le_mul (hg s) hξ (norm_nonneg _) (by norm_num)).trans_eq (by ring)

lemma continuous_actualParisiVectorDCoefficient_path {A ι Ω : Type*}
    (D : ℝ≥0 → Ω → ℝ) (β : ℝ) (x : A → ι → Bool) (g : ℝ≥0 → ℝ)
    (hg : Continuous g) (Y : BrownianVectorPastField A ι)
    (u : A × (ι → Ω)) (i : ι)
    (hY : Continuous (fun s => Y s (u.1,brownianVectorFullPast D s u.2) i)) :
    Continuous (fun s => brownianVectorContinuousCoefficient D
      (actualParisiVectorDCoefficient β x g Y) s u i) := by
  change Continuous (fun s => g s * actualParisiSpinLinkCoefficient β (x u.1 i)
    s (Y s (u.1,brownianVectorFullPast D s u.2) i))
  have hp : Continuous (fun s : ℝ≥0 => ((s : ℝ),
      Y s (u.1,brownianVectorFullPast D s u.2) i)) := NNReal.continuous_coe.prodMk hY
  have hξ := (continuous_actualParisiSpinLinkCoefficient β (x u.1 i)).comp hp
  convert hg.mul hξ using 1
  funext s
  rfl

theorem actualParisiVectorDReference_exists {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (β : ℝ) (x : A → ι → Bool) (hx : Measurable x)
    (g : ℝ≥0 → ℝ) (hg : Continuous g) (hgB : ∀ s, ‖g s‖ ≤ 1)
    (Y : BrownianVectorPastField A ι) (hY : ∀ s, Measurable (Y s))
    (hYc : ∀ i, ∀ᵐ u ∂P.prod (Measure.pi (fun _ : ι => Q)),
      Continuous (fun s => Y s (u.1,brownianVectorFullPast D s u.2) i))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hleft : ∀ l d i, i < k*2^(l+d) →
      |(G.time (l+d) i : ℝ)-G.time l (i/2^d)| ≤ δ l)
    (hwidth : ∀ l i, i < k*2^l → (G.time l (i+1) : ℝ)-G.time l i ≤ δ l) :
    ∃ I : A × (ι → Ω) → ℝ, MemLp I 2 (P.prod (Measure.pi (fun _ : ι => Q))) ∧
      Tendsto (fun l => ∫ u, (brownianVectorContinuousLeftSum D
        (actualParisiVectorDCoefficient β x g Y) G k l u-I u)^2
          ∂P.prod (Measure.pi (fun _ : ι => Q))) atTop (𝓝 0) ∧
      Integrable (brownianVectorContinuousExponential D (actualParisiVectorDCoefficient β x g Y)
        (G.time 0 k) I) (P.prod (Measure.pi (fun _ : ι => Q))) ∧
      (∫ u, brownianVectorContinuousExponential D (actualParisiVectorDCoefficient β x g Y)
        (G.time 0 k) I u ∂P.prod (Measure.pi (fun _ : ι => Q))) = 1 ∧
      IsProbabilityMeasure ((P.prod (Measure.pi (fun _ : ι => Q))).withDensity (fun u =>
        ENNReal.ofReal (brownianVectorContinuousExponential D (actualParisiVectorDCoefficient β x g Y)
          (G.time 0 k) I u))) ∧
      (((P.prod (Measure.pi (fun _ : ι => Q))).withDensity (fun u =>
        ENNReal.ofReal (brownianVectorContinuousExponential D (actualParisiVectorDCoefficient β x g Y)
          (G.time 0 k) I u))).map Prod.fst = P) := by
  have hc : ∀ i, ∀ᵐ u ∂P.prod (Measure.pi (fun _ : ι => Q)), Continuous (fun s =>
      brownianVectorContinuousCoefficient D (actualParisiVectorDCoefficient β x g Y) s u i) := by
    intro i
    filter_upwards [hYc i] with u hu
    exact continuous_actualParisiVectorDCoefficient_path D β x g hg Y u i hu
  obtain ⟨I,hI,hIlim,hEi,hEmean,hEprob,hEmarg,hEL1⟩ :=
    brownianVectorContinuousReference_exists P Q D hD hmD
      (actualParisiVectorDCoefficient β x g Y)
      (measurable_actualParisiVectorDCoefficient β x hx g Y hY) 2
      (actualParisiVectorDCoefficient_bound β x g hgB Y) hc G k δ hδ hleft hwidth
  exact ⟨I,hI,hIlim,hEi,hEmean,hEprob,hEmarg⟩

end SKConstants
