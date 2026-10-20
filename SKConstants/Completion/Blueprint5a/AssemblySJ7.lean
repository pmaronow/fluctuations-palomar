module

public import SKConstants.Completion.Blueprint5a.Statements
public import SKConstants.ScalarProcessLagMGFLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Blueprint5a
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint SKConstants.Blueprint4 SKConstants.Completion

section Generic
variable {B : Type*} [MeasurableSpace B] {μ : Measure B}

theorem localQuadraticMGF_mono {X : B → ℝ} {v v' r r' : ℝ}
    (h : Concentration.LocalQuadraticMGF X μ v r) (hv : v ≤ v') (hr : r' ≤ r) :
    Concentration.LocalQuadraticMGF X μ v' r' :=
  ⟨fun t ht => h.integrable_exp_mul t (ht.trans hr),
    fun t ht => (h.mgf_le t (ht.trans hr)).trans
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hv (sq_nonneg t)))⟩

theorem localQuadraticMGF_of_hasSubgaussianMGF {X : B → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (r : ℝ) :
    Concentration.LocalQuadraticMGF X μ ((c : ℝ) / 2) r :=
  ⟨fun t _ => h.integrable_exp_mul t,
    fun t _ => (h.mgf_le t).trans_eq (by congr 1; ring)⟩

theorem centered_sq_tendsto [IsProbabilityMeasure μ] {F : ℕ → B → ℝ} {G : B → ℝ}
    (hF : ∀ l, Integrable (F l) μ) (hG : Integrable G μ)
    (hi : ∀ l, Integrable (fun u => (F l u - G u) ^ 2) μ)
    (hlim : Tendsto (fun l => ∫ u, (F l u - G u) ^ 2 ∂μ) atTop (𝓝 0)) :
    (∀ l, Integrable (fun u => ((F l u - ∫ w, F l w ∂μ) - (G u - ∫ w, G w ∂μ)) ^ 2) μ) ∧
    Tendsto (fun l => ∫ u, ((F l u - ∫ w, F l w ∂μ) - (G u - ∫ w, G w ∂μ)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hD (l : ℕ) : MemLp (fun u => F l u - G u) 2 μ :=
    (memLp_two_iff_integrable_sq ((hF l).sub hG).aestronglyMeasurable).2 (hi l)
  have hpt (l : ℕ) : (fun u => (F l u - ∫ w, F l w ∂μ) - (G u - ∫ w, G w ∂μ)) =
      fun u => (F l u - G u) - ∫ w, (F l w - G w) ∂μ := by
    funext u
    rw [integral_sub (hF l) hG]
    ring
  have hval (l : ℕ) : ∫ u, ((F l u - ∫ w, F l w ∂μ) - (G u - ∫ w, G w ∂μ)) ^ 2 ∂μ =
      variance (fun u => F l u - G u) μ := by
    rw [variance_eq_integral (X := fun u => F l u - G u) ((hF l).sub hG).aemeasurable]
    refine integral_congr_ae (ae_of_all _ (fun u => ?_))
    simp only [integral_sub (hF l) hG]
    ring
  refine ⟨fun l => ?_, ?_⟩
  · refine (((hD l).sub (memLp_const (∫ w, (F l w - G w) ∂μ))).integrable_sq).congr
      (ae_of_all _ (fun u => ?_))
    simp only [Pi.sub_apply, integral_sub (hF l) hG]
    ring
  · simp_rw [hval]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun l => variance_nonneg _ _) (fun l => ?_)
    exact (variance_le_expectation_sq ((hF l).sub hG).aestronglyMeasurable).trans_eq rfl

theorem sub_sq_tendsto {F H : ℕ → B → ℝ} {G K : B → ℝ}
    (hFm : ∀ l, AEStronglyMeasurable (fun u => (F l u - H l u) - (G u - K u)) μ)
    (hi : ∀ l, Integrable (fun u => (F l u - G u) ^ 2) μ)
    (hj : ∀ l, Integrable (fun u => (H l u - K u) ^ 2) μ)
    (hlim : Tendsto (fun l => ∫ u, (F l u - G u) ^ 2 ∂μ) atTop (𝓝 0))
    (hlim' : Tendsto (fun l => ∫ u, (H l u - K u) ^ 2 ∂μ) atTop (𝓝 0)) :
    (∀ l, Integrable (fun u => ((F l u - H l u) - (G u - K u)) ^ 2) μ) ∧
    Tendsto (fun l => ∫ u, ((F l u - H l u) - (G u - K u)) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hb (l : ℕ) (u : B) : ((F l u - H l u) - (G u - K u)) ^ 2 ≤
      2 * (F l u - G u) ^ 2 + 2 * (H l u - K u) ^ 2 := by
    nlinarith [sq_nonneg ((F l u - G u) + (H l u - K u))]
  have hint (l : ℕ) : Integrable (fun u => ((F l u - H l u) - (G u - K u)) ^ 2) μ :=
    Integrable.mono' (((hi l).const_mul 2).add ((hj l).const_mul 2))
      ((hFm l).pow 2) (ae_of_all _ (fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hb l u))
  refine ⟨hint, ?_⟩
  have hup : Tendsto (fun l => 2 * ∫ u, (F l u - G u) ^ 2 ∂μ + 2 * ∫ u, (H l u - K u) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    simpa using (hlim.const_mul 2).add (hlim'.const_mul 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun l => integral_nonneg (fun u => sq_nonneg _)) (fun l => ?_)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hi l).const_mul 2)
    ((hj l).const_mul 2)]
  exact integral_mono (hint l) (((hi l).const_mul 2).add ((hj l).const_mul 2)) (hb l)

end Generic

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem refinedResidual_eq (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (K l : ℕ) (u : (Bool × Ω) × A) :
    refinedResidual W Z β hβ δ K l u =
      scalarHiddenSign u.1.1 * linearGroup W Z β hβ δ K l u + predictableGroup W Z β hβ δ K l u +
        quadraticGroup W β δ K l u - lagGroup W Z β hβ δ K l u :=
  LJ.actualRefinedResidual_decomposition W Z β hβ (mesh δ) (refinedGrid δ l) K (2 ^ l)
    (fun j _ => LJ3.growingLagDyadicTime_zero δ l j)
    (fun j _ => LJ3.growingLagDyadicTime_end δ l j) u

theorem abs_scalarHiddenSign_mul (b : Bool) (y : ℝ) : |scalarHiddenSign b * y| = |y| := by
  cases b <;> simp [scalarHiddenSign]

theorem measurable_hiddenSign_fst :
    Measurable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1) :=
  (measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)

theorem signed_tail_le {μ : Measure ((Bool × Ω) × A)} [IsFiniteMeasure μ] {L : (Bool × Ω) × A → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF L c μ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {w | ε ≤ |scalarHiddenSign w.1.1 * L w|} ≤ 2 * Real.exp (-(ε ^ 2) / (2 * c)) := by
  have hsub : {w : (Bool × Ω) × A | ε ≤ |scalarHiddenSign w.1.1 * L w|} ⊆
      {w | ε ≤ L w} ∪ {w | ε ≤ (-L) w} := by
    intro w hw
    simp only [mem_ofPred_eq, abs_scalarHiddenSign_mul] at hw
    simp only [mem_union, mem_ofPred_eq, Pi.neg_apply]
    rcases le_abs'.1 hw with h' | h'
    · right; linarith
    · left; exact h'
  have h1 := h.measure_ge_le hε
  have h2 := h.neg.measure_ge_le hε
  calc μ.real {w | ε ≤ |scalarHiddenSign w.1.1 * L w|}
      ≤ μ.real ({w | ε ≤ L w} ∪ {w | ε ≤ (-L) w}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real {w | ε ≤ L w} + μ.real {w | ε ≤ (-L) w} := measureReal_union_le _ _
    _ ≤ _ := by linarith

theorem growingResidualMGF_of_subnodes (h1 : RefinedResidualLimitStatement)
    (h3 : QuadraticGroupLimitStatement) (h4a : SignSymmetrizationStatement)
    (h4b : LinearGroupSubgaussianStatement) (h5 : PredictableGroupMGFStatement)
    (h6 : LagGroupMGFStatement) : GrowingResidualMGFStatement := by
  intro Ω A _ _ W Z β hβ
  obtain ⟨C3, hC3, H3⟩ := h3 W Z β hβ
  obtain ⟨C4, hC4, H4⟩ := h4b W Z β hβ
  obtain ⟨C5, c5, hC5, hc5, H5⟩ := h5 W Z β hβ
  obtain ⟨C6, c6, hC6, hc6, H6⟩ := h6 W Z β hβ
  have hC4' : (0 : ℝ) < C4 := hC4
  refine ⟨8 * (32 * (C4 : ℝ) + C5) + 4 * C6 + C3 ^ 2 + 1, min c5 c6 / 8, by positivity,
    by have := lt_min hc5 hc6; positivity, ?_⟩
  intro δ K hmesh Zv hZv
  obtain ⟨hint, hmean⟩ := SJ7.growingResidual_integrable_mean W Z β hβ δ K hmesh Zv hZv
  refine ⟨hint, hmean, ?_⟩
  have hδ : (0 : ℝ) < δ := hmesh.1
  have hδ1 : (δ : ℝ) ≤ 1 := hmesh.2.1
  set ν := meshLaw W Z β δ K with hν
  set c := min c5 c6 with hcdef
  have hc : 0 < c := lt_min hc5 hc6
  set X : ℕ → (Bool × Ω) × A → ℝ :=
    fun l u => scalarHiddenSign u.1.1 * linearGroup W Z β hβ δ K l u with hX
  set P : ℕ → (Bool × Ω) × A → ℝ := fun l => predictableGroup W Z β hβ δ K l with hP
  set Lg : ℕ → (Bool × Ω) × A → ℝ := fun l => lagGroup W Z β hβ δ K l with hLg
  set S : ℕ → (Bool × Ω) × A → ℝ := fun l u => X l u + P l u - Lg l u with hS
  have hXm (l : ℕ) : Measurable (X l) := measurable_hiddenSign_fst.mul (H4 δ K hmesh l).1
  have hPm (l : ℕ) : Measurable (P l) := (H5 δ K hmesh l).1
  have hLm (l : ℕ) : Measurable (Lg l) := (H6 δ K hmesh l).1
  have hSm (l : ℕ) : Measurable (S l) := ((hXm l).add (hPm l)).sub (hLm l)
  have hXi (l : ℕ) : Integrable (X l) ν :=
    (H4 δ K hmesh l).2.integrable.mono (hXm l).aestronglyMeasurable
      (ae_of_all _ (fun u => le_of_eq (by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, hX, abs_scalarHiddenSign_mul])))
  have hPi (l : ℕ) : Integrable (P l) ν := (H5 δ K hmesh l).2.1
  have hLi (l : ℕ) : Integrable (Lg l) ν := (H6 δ K hmesh l).2.1
  have hSi (l : ℕ) : Integrable (S l) ν := ((hXi l).add (hPi l)).sub (hLi l)
  have hrad5 : c / δ ≤ c5 / δ := div_le_div_of_nonneg_right (min_le_left _ _) hδ.le
  have hrad6 : c / δ ≤ c6 / δ := div_le_div_of_nonneg_right (min_le_right _ _) hδ.le
  have hXmgf (l : ℕ) : Concentration.LocalQuadraticMGF (fun u => X l u - ∫ w, X l w ∂ν) ν
      (32 * ((C4 : ℝ) * δ)) (c / δ) :=
    h4a ν (X l) ((C4 : ℝ) * δ) (by positivity) (hXm l) (fun ε hε => by
      have := signed_tail_le (H4 δ K hmesh l).2 ε hε
      simpa only [NNReal.coe_mul] using this) (c / δ)
  have hPmgf (l : ℕ) : Concentration.LocalQuadraticMGF (fun u => P l u - ∫ w, P l w ∂ν) ν
      (C5 * δ) (c / δ) := localQuadraticMGF_mono (H5 δ K hmesh l).2.2 le_rfl hrad5
  have hLmgf (l : ℕ) : Concentration.LocalQuadraticMGF (fun u => -(Lg l u - ∫ w, Lg l w ∂ν)) ν
      (C6 * δ) (c / δ / 2) :=
    (localQuadraticMGF_mono (H6 δ K hmesh l).2.2 le_rfl
      ((half_le_self (by positivity)).trans hrad6)).neg
  have hSmgf (l : ℕ) : Concentration.LocalQuadraticMGF (fun u => S l u - ∫ w, S l w ∂ν) ν
      (2 * (2 * (32 * ((C4 : ℝ) * δ) + C5 * δ) + C6 * δ)) (c / δ / 2 / 2) := by
    have h12 := SJ7.localQuadraticMGF_add ((hXm l).sub measurable_const)
      ((hPm l).sub measurable_const) (hXmgf l) (hPmgf l)
    have h123 := SJ7.localQuadraticMGF_add
      (((hXm l).sub measurable_const).add ((hPm l).sub measurable_const))
      ((hLm l).sub measurable_const).neg h12 (hLmgf l)
    refine h123.congr_ae (ae_of_all _ (fun u => ?_))
    have hint : ∫ w, S l w ∂ν = ∫ w, X l w ∂ν + ∫ w, P l w ∂ν - ∫ w, Lg l w ∂ν := by
      show ∫ w, (X l w + P l w - Lg l w) ∂ν = _
      rw [integral_sub (f := fun w => X l w + P l w) ((hXi l).add (hPi l)) (hLi l),
        integral_add (hXi l) (hPi l)]
    rw [hint]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, hS]
    ring
  obtain ⟨hQm, hQb, hQi, hQlim⟩ := H3 δ K hmesh
  obtain ⟨hRi, hRlim⟩ := h1 W Z β hβ δ K hmesh Zv hZv
  have hpt (l : ℕ) (u : (Bool × Ω) × A) :
      S l u = refinedResidual W Z β hβ δ K l u - quadraticGroup W β δ K l u := by
    rw [refinedResidual_eq]
    simp only [hS, hX, hP, hLg]
    ring
  have hQint : Integrable (quadraticLimit (A := A) W β δ K) ν :=
    Integrable.of_bound hQm.aestronglyMeasurable (C3 * δ)
      (ae_of_all _ (fun u => by rw [Real.norm_eq_abs]; exact hQb u))
  set R := growingResidual W Z β hβ δ K Zv with hR
  set Y : (Bool × Ω) × A → ℝ := fun u => R u - quadraticLimit W β δ K u with hY
  have hYi : Integrable Y ν := hint.sub hQint
  have hdiff := sub_sq_tendsto (μ := ν)
    (F := fun l => refinedResidual W Z β hβ δ K l) (H := fun l => quadraticGroup W β δ K l)
    (G := R) (K := quadraticLimit W β δ K)
    (fun l => ((hSm l).aestronglyMeasurable.sub hYi.aestronglyMeasurable).congr
      (ae_of_all _ (fun u => by simp only [Pi.sub_apply, hpt l u, hY])))
    hRi hQi hRlim hQlim
  have hSY_i (l : ℕ) : Integrable (fun u => (S l u - Y u) ^ 2) ν :=
    (hdiff.1 l).congr (ae_of_all _ (fun u => by simp only [hpt l u, hY]))
  have hSY_lim : Tendsto (fun l => ∫ u, (S l u - Y u) ^ 2 ∂ν) atTop (𝓝 0) :=
    hdiff.2.congr (fun l => integral_congr_ae (ae_of_all _ (fun u => by
      simp only [hpt l u, hY])))
  have hcen := centered_sq_tendsto hSi hYi hSY_i hSY_lim
  have hYmgf : Concentration.LocalQuadraticMGF (fun u => Y u - ∫ w, Y w ∂ν) ν
      (2 * (2 * (32 * ((C4 : ℝ) * δ) + C5 * δ) + C6 * δ)) (c / δ / 2 / 2) :=
    SJ7.localQuadraticMGF_of_L2 (X := fun l u => S l u - ∫ w, S l w ∂ν) hSmgf
      (fun l => (hSm l).sub measurable_const) hcen.1 hcen.2
  have hQh := hasSubgaussianMGF_of_mem_Icc (μ := ν) (a := -((C3 : ℝ) * δ)) (b := C3 * δ)
    hQm.aemeasurable (ae_of_all _ (fun u => abs_le.1 (hQb u)))
  have hQmgf := localQuadraticMGF_of_hasSubgaussianMGF hQh (c / δ / 2 / 2)
  have hQval : ((((‖(C3 : ℝ) * δ - -((C3 : ℝ) * δ)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)) = (C3 * δ) ^ 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
    rw [abs_of_nonneg (by have := mul_pos hC3 hδ; linarith)]
    ring
  rw [hQval] at hQmgf
  have hYa : AEStronglyMeasurable (fun u => Y u - ∫ w, Y w ∂ν) ν :=
    hYi.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hYmk := hYmgf.congr_ae hYa.ae_eq_mk.symm
  have hfin := SJ7.localQuadraticMGF_add hYa.stronglyMeasurable_mk.measurable
    (hQm.sub measurable_const) hYmk hQmgf
  have hfin' := hfin.congr_ae (Y := fun u => R u - ∫ w, R w ∂ν) (by
    filter_upwards [hYa.ae_eq_mk] with u hu
    simp only [Pi.sub_apply]
    rw [← hu]
    simp only [hY]
    rw [integral_sub (f := R) (g := quadraticLimit W β δ K) hint hQint]
    ring)
  refine localQuadraticMGF_mono hfin' ?_ ?_
  · have h1' : (C3 : ℝ) ^ 2 * (δ : ℝ) ^ 2 ≤ C3 ^ 2 * δ := by
      have : (δ : ℝ) ^ 2 ≤ δ := by nlinarith
      exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
    nlinarith
  · apply le_of_eq
    rw [hcdef]
    field_simp
    ring

end SKConstants.Blueprint5a
