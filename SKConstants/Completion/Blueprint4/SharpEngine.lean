module

public import SKConstants.Completion.Blueprint4.NodesSharp

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Blueprint4
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint SKConstants.Completion

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem measurable_actualFiniteRow (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ)
    (hβ : 1 < β) (t : ℕ → ℝ≥0) (K : ℕ) : Measurable (LJ.actualFiniteRow W Z β hβ t K) := by
  have hs : Measurable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1) :=
    (measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)
  unfold LJ.actualFiniteRow
  refine ((Finset.measurable_fun_sum _ fun j _ => ?_).add
    (Finset.measurable_fun_sum _ fun j _ => ?_)).sub measurable_const
  · exact (((LJ.measurable_actualRowPotential W β _).comp measurable_fst).sub
      ((LJ.measurable_actualRowPotential W β _).comp measurable_fst)).const_mul _
  · exact ((hs.sub ((measurable_actualParisiFullPosteriorMean W β _).comp
      (measurable_snd.comp measurable_fst))).mul
        (LJ.measurable_gridQuery W Z β hβ t K j)).const_mul _

theorem measurable_growingResidual (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ)
    (hβ : 1 < β) (δ : ℝ≥0) (K : ℕ) {Zv : (Bool × Ω) × A → ℝ} (hZv : Measurable Zv) :
    Measurable (growingResidual W Z β hβ δ K Zv) :=
  hZv.sub ((measurable_actualFiniteRow W Z β hβ _ K).add measurable_const)

theorem measureReal_mono_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {s t : Set α} (h : s ≤ᵐ[μ] t) : μ.real s ≤ μ.real t :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae h)

theorem localQuadraticMGF_mono {X : Ω → ℝ} {μ : Measure Ω} {v v' r : ℝ}
    (h : Concentration.LocalQuadraticMGF X μ v r) (hv : v ≤ v') :
    Concentration.LocalQuadraticMGF X μ v' r where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t ht := (h.mgf_le t ht).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hv (sq_nonneg t)))

theorem localQuadraticMGF_pi_eval {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    {X : Ω → ℝ} (hX : Measurable X) {v r : ℝ} (h : Concentration.LocalQuadraticMGF X μ v r)
    (i : Fin n) :
    Concentration.LocalQuadraticMGF (fun ω : Fin n → Ω => X (ω i))
      (Measure.pi fun _ => μ) v r := by
  have hmp : MeasurePreserving (fun ω : Fin n → Ω => ω i) (Measure.pi fun _ => μ) μ :=
    measurePreserving_eval (fun _ => μ) i
  constructor
  · intro t ht
    exact hmp.integrable_comp_of_integrable (h.integrable_exp_mul t ht)
  · intro t ht
    have hg : AEStronglyMeasurable (fun x => Real.exp (t * X x))
        (Measure.map (fun ω : Fin n → Ω => ω i) (Measure.pi fun _ => μ)) :=
      ((hX.const_mul t).exp).aestronglyMeasurable
    have heq : mgf (fun ω : Fin n → Ω => X (ω i)) (Measure.pi fun _ => μ) t = mgf X μ t := by
      calc mgf (fun ω : Fin n → Ω => X (ω i)) (Measure.pi fun _ => μ) t
          = ∫ x, Real.exp (t * X x)
              ∂(Measure.map (fun ω : Fin n → Ω => ω i) (Measure.pi fun _ => μ)) :=
            (integral_map hmp.measurable.aemeasurable hg).symm
        _ = mgf X μ t := by rw [hmp.map_eq]; rfl
    rw [heq]
    exact h.mgf_le t ht

theorem growingResidualConcentration_of_mgf (h7 : GrowingResidualMGFStatement) :
    GrowingResidualConcentrationStatement := by
  intro Ω A _ _ W Z β hβ
  obtain ⟨C, c, hC, hc, hmain⟩ := h7 W Z β hβ
  set C' := max C (1 / (2 * c)) with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le hC (le_max_left _ _)
  refine ⟨1 / (4 * C'), by positivity, ?_⟩
  intro δ K hmesh Zv hZv n hn η hη hη1
  obtain ⟨-, -, hmgf⟩ := hmain δ K hmesh Zv hZv
  have hδ : (0 : ℝ) < δ := by exact_mod_cast hmesh.1
  set ν := actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1)) with hν
  set Y : (Bool × Ω) × A → ℝ := fun u => growingResidual W Z β hβ δ K Zv u -
    ∫ u', growingResidual W Z β hβ δ K Zv u' ∂ν with hY
  have hYm : Measurable Y := (measurable_growingResidual W Z β hβ δ K hZv.1).sub measurable_const
  have hmgf' : Concentration.LocalQuadraticMGF Y ν (C' * δ) (c / δ) :=
    localQuadraticMGF_mono hmgf (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le)
  have hInd := iIndepFun_pi (μ := fun _ : Fin n => ν) (X := fun _ => Y)
    (fun _ => hYm.aemeasurable)
  have hrows : ∀ i : Fin n, Concentration.LocalQuadraticMGF (fun ω : Fin n → _ => Y (ω i))
      (Measure.pi fun _ => ν) (C' * δ) (c / δ) := fun i => localQuadraticMGF_pi_eval hYm hmgf' i
  have hsmall : η ≤ 2 * C' * c := by
    have h1 : 1 / (2 * c) ≤ C' := le_max_right _ _
    have h2 : 1 ≤ C' * (2 * c) := (div_le_iff₀ (by positivity)).mp h1
    linarith
  have key := Concentration.independent_mesh_average (X := fun i (ω : Fin n → _) => Y (ω i))
    hn hInd (fun i => hYm.comp (measurable_pi_apply i)) hrows hC'pos hc hδ hη hsmall
  refine key.trans_eq ?_
  congr 2
  field_simp

theorem sharpRowConcentration_of_engine (h3 : JointEndpointIdentityStatement)
    (h7 : GrowingResidualMGFStatement) : SharpRowConcentrationStatement := by
  intro Ω A _ _ W Z β hβ
  obtain ⟨c, hc, h8⟩ := growingResidualConcentration_of_mgf h7 W Z β hβ
  obtain ⟨C₇, c₇, -, -, hmain⟩ := h7 W Z β hβ
  set Cq : ℝ := 1 / β ^ 2 + 33 * Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2)
    with hCq
  have hβ0 : 0 < β := by linarith
  have hCq0 : 0 ≤ Cq := by positivity
  refine ⟨β * Cq, c / β ^ 2, by positivity, by positivity, ?_⟩
  intro δ K hmesh J hJ n hn η hη hη1
  set V := growingQueryTime δ (K + 1) with hV
  set ν := actualParisiFullQuerySpinLaw W Z β V with hν
  obtain ⟨⟨Zv, hZv⟩, hid⟩ := h3 W Z β hβ V hmesh.2.2.2
  obtain ⟨-, hmean, -⟩ := hmain δ K hmesh Zv hZv
  have hδ : (0 : ℝ) < δ := by exact_mod_cast hmesh.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set p := actualParisiFullSusceptibilityExpected W β V with hp
  have hp0 : 0 ≤ p := actualParisiFullSusceptibilityExpected_nonneg W β _
  set e := actualParisiEnergyReference W β V with he
  set eh := LJ.gridEnergy W β (growingQueryTime δ) K with heh
  have hq : |eh - e| ≤ Cq * δ := by
    rw [heh, LJ.gridEnergy_growing_eq]
    exact LQ.actual_growing_energy_error W β hβ δ hmesh.1 K
      (fun i hi => hmesh.2.2.1 i (by omega))
  have hq' : e - eh ≤ Cq * δ := by
    have := neg_abs_le (eh - e)
    linarith
  set ER := ∫ u, growingResidual W Z β hβ δ K Zv u ∂ν with hER
  have hae := hid J Zv hJ hZv
  have hpi : ∀ᵐ ω ∂(Measure.pi fun _ : Fin n => ν), ∀ i,
      rowInformationV W β V J (ω i) - β * (Zv (ω i) - e / 2) =
        Real.log 2 - parisiPressure β - β ^ 2 * p ^ 2 / 4 +
          (β ^ 2 * p / 2) * actualParisiPinningError W β V (ω i).1 := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => ν) i).ae hae
  have hbound := h8 δ K hmesh Zv hZv n hn (η / β) (by positivity)
    ((div_le_one hβ0).mpr (by linarith))
  refine le_trans (measureReal_mono_of_ae ?_) (hbound.trans_eq ?_)
  · filter_upwards [hpi] with ω hω hmem
    change _ < _ at hmem
    have hrow : ∀ i, rowInformationV W β V J (ω i) -
        β * LJ.actualFiniteRow W Z β hβ (growingQueryTime δ) K (ω i) ≤
        (Real.log 2 - parisiPressure β + 2 * β ^ 2 * p + β * Cq * δ) +
          β * (growingResidual W Z β hβ δ K Zv (ω i) - ER) := by
      intro i
      have hR : growingResidual W Z β hβ δ K Zv (ω i) =
          Zv (ω i) - (LJ.actualFiniteRow W Z β hβ (growingQueryTime δ) K (ω i) + eh / 2) := rfl
      have hpin0 : 0 ≤ actualParisiPinningError W β V (ω i).1 := sq_nonneg _
      have hpin4 : actualParisiPinningError W β V (ω i).1 ≤ 4 := by
        have hm := abs_actualParisiFullPosteriorMean_le W β V (ω i).1.2
        have hx : |scalarHiddenSign (ω i).1.1| ≤ 1 := by
          cases (ω i).1.1 <;> simp [scalarHiddenSign]
        have habs : |scalarHiddenSign (ω i).1.1 -
            actualParisiFullPosteriorMean W β V (ω i).1.2| ≤ 2 :=
          (abs_sub _ _).trans (by linarith)
        unfold actualParisiPinningError
        nlinarith [sq_abs (scalarHiddenSign (ω i).1.1 -
          actualParisiFullPosteriorMean W β V (ω i).1.2),
          abs_nonneg (scalarHiddenSign (ω i).1.1 -
          actualParisiFullPosteriorMean W β V (ω i).1.2)]
      have key : rowInformationV W β V J (ω i) -
          β * LJ.actualFiniteRow W Z β hβ (growingQueryTime δ) K (ω i) -
          ((Real.log 2 - parisiPressure β + 2 * β ^ 2 * p + β * Cq * δ) +
            β * (growingResidual W Z β hβ δ K Zv (ω i) - ER)) =
          -(β ^ 2 * p ^ 2 / 4) +
            ((β ^ 2 * p / 2) * actualParisiPinningError W β V (ω i).1 - 2 * β ^ 2 * p) +
            (β * (e - eh) - β * (Cq * δ)) := by
        linear_combination (hω i) - β * hR + β * hmean
      have k1 : (β ^ 2 * p / 2) * actualParisiPinningError W β V (ω i).1 ≤ 2 * β ^ 2 * p := by
        have := mul_le_mul_of_nonneg_left hpin4 (by positivity : (0 : ℝ) ≤ β ^ 2 * p / 2)
        linarith
      have k2 : 0 ≤ β ^ 2 * p ^ 2 / 4 := by positivity
      have k3 : β * (e - eh) ≤ β * (Cq * δ) := mul_le_mul_of_nonneg_left hq' hβ0.le
      linarith
    have hsum : ∑ i, (rowInformationV W β V J (ω i) -
        β * LJ.actualFiniteRow W Z β hβ (growingQueryTime δ) K (ω i)) ≤
        (n : ℝ) * (Real.log 2 - parisiPressure β + 2 * β ^ 2 * p + β * Cq * δ) +
          β * ∑ i, (growingResidual W Z β hβ δ K Zv (ω i) - ER) := by
      calc _ ≤ ∑ i : Fin n, ((Real.log 2 - parisiPressure β + 2 * β ^ 2 * p + β * Cq * δ) +
            β * (growingResidual W Z β hβ δ K Zv (ω i) - ER)) :=
            Finset.sum_le_sum (fun i _ => hrow i)
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum]
    set S := ∑ i, (growingResidual W Z β hβ δ K Zv (ω i) - ER) with hS
    have hlt : η < β * (S / n) := by
      have h1 := (lt_div_iff₀ hnR).mp hmem
      have h2 : β * (S / n) * n = β * S := by field_simp
      nlinarith
    have : η / β < S / n := by
      rw [div_lt_iff₀ hβ0]
      linarith
    exact (this.trans_le (le_abs_self _)).le
  · congr 2
    field_simp

end SKConstants.Blueprint4
