module

public import SKConstants.Completion.Blueprint.NodesLower
public import SKConstants.Completion.Blueprint.AssemblySequence

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology unitInterval BigOperators
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Blueprint
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal

variable {Ω : Type*} [MeasurableSpace Ω]

attribute [local irreducible] runMag

section Kernel

variable (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)

def restrictedKernel (E : Set (RunInput p n)) (g : Prim n) (x : Spin n) : ℝ :=
  ((fineAuxLaw W p n).prod (thresholdLaw n)).real
    {u | (g, u) ∈ E ∧ coarseSpin W β hβ p n g u.1 u.2 = x}

theorem measurableSet_coarseSpin_eq (x : Spin n) :
    MeasurableSet {y : RunInput p n | coarseSpin W β hβ p n y.1 y.2.1 y.2.2 = x} :=
  (measurable_runSpin W β hβ p n (readoutTime p.a p.b n)) (measurableSet_singleton x)

theorem measurable_restrictedKernel (E : Set (RunInput p n)) (hE : MeasurableSet E)
    (x : Spin n) : Measurable (fun g => restrictedKernel W β hβ p n E g x) := by
  have hS : MeasurableSet {y : RunInput p n | y ∈ E ∧ coarseSpin W β hβ p n y.1 y.2.1 y.2.2 = x} :=
    hE.inter (measurableSet_coarseSpin_eq W β hβ p n x)
  exact (measurable_measure_prodMk_left hS).ennreal_toReal

theorem restrictedKernel_nonneg (E : Set (RunInput p n)) (g : Prim n) (x : Spin n) :
    0 ≤ restrictedKernel W β hβ p n E g x := measureReal_nonneg

theorem restrictedKernel_le_one (E : Set (RunInput p n)) (g : Prim n) (x : Spin n) :
    restrictedKernel W β hβ p n E g x ≤ 1 := measureReal_le_one

def dominationBound (L : ℝ) (g : Prim n) (x : Spin n) : ℝ :=
  Real.exp (-(n : ℝ) * parisiPressure β + L +
    β * goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) x g)

theorem measurable_dominationBound (L : ℝ) (x : Spin n) :
    Measurable (fun g => dominationBound β n L g x) := by
  unfold dominationBound goeSpinHamiltonian
  have hc : Continuous (fun g : Prim n =>
      quadraticHamiltonian (goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) g) x) := by
    unfold quadraticHamiltonian
    have := continuous_goeMatrix (V := Fin n) (1 / Real.sqrt (2 * (n : ℝ)))
    fun_prop
  exact (continuous_const.add (continuous_const.mul hc)).rexp.measurable

def cappedKernel (E : Set (RunInput p n)) (L : ℝ) (g : Prim n) (x : Spin n) : ℝ :=
  min (restrictedKernel W β hβ p n E g x) (dominationBound β n L g x)

end Kernel

theorem regression_coeff_sq (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    (1 - δ) ^ 2 + Real.sqrt (δ * (2 - δ)) ^ 2 = 1 := by
  rw [Real.sq_sqrt (by nlinarith)]
  ring

theorem smoothing_le_one (p : Parameters) (n : ℕ) (hn : 1 ≤ n) (hD : 0 < p.D) :
    (smoothing p n : ℝ) ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold smoothing
  rw [Real.coe_toNNReal _ (Real.rpow_nonneg (by linarith) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith)

theorem angleLaw_map_run (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (angleLaw W p n).map (fun y => (c • y.1.1 + s • y.1.2, y.2)) = runLaw W p n := by
  have hrot : ((primLaw n).prod (primLaw n)).map (fun w : Prim n × Prim n => c • w.1 + s • w.2) =
      primLaw n := stdGaussian_rotation_marginal c s hcs
  have h := Measure.map_prod_map ((primLaw n).prod (primLaw n))
    ((fineAuxLaw W p n).prod (thresholdLaw n))
    (f := fun w : Prim n × Prim n => c • w.1 + s • w.2) (g := id) (by fun_prop) measurable_id
  rw [Measure.map_id, hrot] at h
  exact h.symm

theorem hit_le_regression (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (hn : 1 ≤ n) (hD : 0 < p.D) (E : Set (RunInput p n)) (hE : MeasurableSet E) :
    ((angleLaw W p n).map (regressionInput p n)).real (coarseHitEvent W β hβ p n) ≤
      (runLaw W p n).real Eᶜ +
        ∫ G, gaussianRegressionSetMass (1 - (smoothing p n : ℝ))
          (Real.sqrt ((smoothing p n : ℝ) * (2 - (smoothing p n : ℝ))))
          (restrictedKernel W β hβ p n E) (excludedSet β p n) G ∂primLaw n := by
  set c := 1 - (smoothing p n : ℝ) with hc
  set s := Real.sqrt ((smoothing p n : ℝ) * (2 - (smoothing p n : ℝ))) with hs
  have hδ0 : (0 : ℝ) ≤ smoothing p n := NNReal.coe_nonneg _
  have hcs : c ^ 2 + s ^ 2 = 1 := regression_coeff_sq _ hδ0 (smoothing_le_one p n hn hD)
  set μ := angleLaw W p n
  set ν := (fineAuxLaw W p n).prod (thresholdLaw n)
  set k := restrictedKernel W β hβ p n E
  set D := excludedSet β p n
  have hreg : Measurable (regressionInput p n) := by
    unfold regressionInput
    fun_prop
  have hrun : Measurable (fun y : AngleSpace p n => ((c • y.1.1 + s • y.1.2, y.2) : RunInput p n)) := by
    fun_prop
  let T1 : Set (AngleSpace p n) := {y | ((c • y.1.1 + s • y.1.2, y.2) : RunInput p n) ∈ Eᶜ}
  let T2 : Set (AngleSpace p n) := {y | ((c • y.1.1 + s • y.1.2, y.2) : RunInput p n) ∈ E ∧
    coarseSpin W β hβ p n (c • y.1.1 + s • y.1.2) y.2.1 y.2.2 ∈ D y.1.1}
  have hT2 : MeasurableSet T2 := by
    refine (hE.preimage hrun).inter ?_
    have h := (measurableSet_not_mem_excludedSet β p n
      ((measurable_runSpin W β hβ p n (readoutTime p.a p.b n)).comp hrun)
      (measurable_fst.fst : Measurable fun y : AngleSpace p n => y.1.1)).compl
    convert h using 1
    ext y
    simp only [Set.mem_compl_iff]
    exact not_not.symm
  have hsub : regressionInput p n ⁻¹' coarseHitEvent W β hβ p n ⊆ T1 ∪ T2 := by
    intro y hy
    by_cases hyE : ((c • y.1.1 + s • y.1.2, y.2) : RunInput p n) ∈ E
    · exact Or.inr ⟨hyE, hy⟩
    · exact Or.inl hyE
  have hT1 : μ.real T1 = (runLaw W p n).real Eᶜ := by
    rw [← angleLaw_map_run W p n c s hcs, measureReal_def, measureReal_def,
      Measure.map_apply hrun hE.compl]
    rfl
  let F : Prim n × Prim n → ℝ := fun w => ∑ x ∈ D w.1, k (c • w.1 + s • w.2) x
  have hk : ∀ x, Measurable (fun g => k g x) := measurable_restrictedKernel W β hβ p n E hE
  have hFm : Measurable F := by
    have he : F = fun w => ∑ x : Spin n, if x ∈ D w.1 then k (c • w.1 + s • w.2) x else 0 := by
      funext w
      exact finiteSpin_sum_eq_univ_ite _ _
    rw [he]
    apply Finset.measurable_sum
    intro x _
    exact Measurable.ite ((measurableSet_excludedSet_mem β p n x).preimage measurable_fst)
      ((hk x).comp (by fun_prop)) measurable_const
  have hF0 : ∀ w, 0 ≤ F w := fun w => Finset.sum_nonneg (fun x _ =>
    restrictedKernel_nonneg W β hβ p n E _ x)
  have hFle : ∀ w, F w ≤ Fintype.card (Spin n) := by
    intro w
    calc F w ≤ ∑ _x ∈ D w.1, (1 : ℝ) := Finset.sum_le_sum (fun x _ =>
          restrictedKernel_le_one W β hβ p n E _ x)
      _ = (D w.1).card := by simp
      _ ≤ Fintype.card (Spin n) := by exact_mod_cast Finset.card_le_univ _
  have hFi : Integrable F ((primLaw n).prod (primLaw n)) := by
    apply (integrable_const (Fintype.card (Spin n) : ℝ)).mono' hFm.aestronglyMeasurable
    exact Eventually.of_forall (fun w => by rw [Real.norm_eq_abs, abs_of_nonneg (hF0 w)]; exact hFle w)
  have hsection : ∀ w : Prim n × Prim n, ν (Prod.mk w ⁻¹' T2) = ENNReal.ofReal (F w) := by
    intro w
    have hset : Prod.mk w ⁻¹' T2 = ⋃ x ∈ D w.1,
        {u | ((c • w.1 + s • w.2, u) : RunInput p n) ∈ E ∧
          coarseSpin W β hβ p n (c • w.1 + s • w.2) u.1 u.2 = x} := by
      ext u
      simp [T2]
    rw [hset, measure_biUnion_finset]
    · rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => restrictedKernel_nonneg W β hβ p n E _ x)]
      apply Finset.sum_congr rfl
      intro x _
      unfold restrictedKernel
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    · intro x _ y _ hxy
      exact Set.disjoint_left.mpr (fun u hu hv => hxy (hu.2.symm.trans hv.2))
    · intro x _
      exact (measurable_prodMk_left (hE.inter (measurableSet_coarseSpin_eq W β hβ p n x)))
  have hT2eq : μ.real T2 = ∫ w, F w ∂((primLaw n).prod (primLaw n)) := by
    have h1 : μ T2 = ∫⁻ w, ENNReal.ofReal (F w) ∂((primLaw n).prod (primLaw n)) := by
      rw [Measure.prod_apply hT2]
      exact lintegral_congr (fun w => hsection w)
    rw [measureReal_def, h1, ← ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall hF0),
      ENNReal.toReal_ofReal (integral_nonneg hF0)]
  have hFG : ∫ w, F w ∂((primLaw n).prod (primLaw n)) =
      ∫ G, gaussianRegressionSetMass c s k D G ∂primLaw n := by
    rw [integral_prod F hFi]
    rfl
  calc ((angleLaw W p n).map (regressionInput p n)).real (coarseHitEvent W β hβ p n)
      = μ.real (regressionInput p n ⁻¹' coarseHitEvent W β hβ p n) := by
        rw [measureReal_def, measureReal_def,
          Measure.map_apply hreg (measurableSet_coarseHitEvent W β hβ p n)]
    _ ≤ μ.real (T1 ∪ T2) := measureReal_mono hsub
    _ ≤ μ.real T1 + μ.real T2 := measureReal_union_le _ _
    _ = _ := by rw [hT1, hT2eq, hFG]

theorem regressionMass_integral_congr_ae (n : ℕ) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (k k' : Prim n → Spin n → ℝ) (hk : ∀ᵐ g ∂primLaw n, ∀ x, k g x = k' g x)
    (D : Prim n → Finset (Spin n)) :
    ∫ G, gaussianRegressionSetMass c s k D G ∂primLaw n =
      ∫ G, gaussianRegressionSetMass c s k' D G ∂primLaw n := by
  have hrot : ((primLaw n).prod (primLaw n)).map (fun w : Prim n × Prim n => c • w.1 + s • w.2) =
      primLaw n := stdGaussian_rotation_marginal c s hcs
  have hpair : ∀ᵐ w ∂((primLaw n).prod (primLaw n)),
      ∀ x, k (c • w.1 + s • w.2) x = k' (c • w.1 + s • w.2) x := by
    rw [← hrot] at hk
    exact ae_of_ae_map (by fun_prop) hk
  have hiter := Measure.ae_ae_of_ae_prod hpair
  apply integral_congr_ae
  filter_upwards [hiter] with G hG
  unfold gaussianRegressionSetMass
  apply integral_congr_ae
  filter_upwards [hG] with Z hZ
  exact Finset.sum_congr rfl (fun x _ => hZ x)

theorem transfer_exponent_eventually (β kb zP D s' s₂ : ℝ) (hβ : 0 ≤ β) (h1 : s' < kb)
    (h2 : s' < zP) (h3 : s' < D) (h4 : s' < s₂) (h5 : s' < 1) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 - kb) + (n : ℝ) ^ (1 - zP) +
      (6 * β + β ^ 2 / 2) * (n : ℝ) ^ (1 - D) + Real.log 2 - (n : ℝ) ^ (1 - s') ≤
        -((n : ℝ) ^ (1 - s₂)) := by
  filter_upwards [constant_rpow_le_small_rpow (1 - kb) (1 - s') 1 (1 / 5) (by linarith)
      (by norm_num) (by norm_num),
    constant_rpow_le_small_rpow (1 - zP) (1 - s') 1 (1 / 5) (by linarith) (by norm_num)
      (by norm_num),
    constant_rpow_le_small_rpow (1 - D) (1 - s') (6 * β + β ^ 2 / 2) (1 / 5) (by linarith)
      (by positivity) (by norm_num),
    constant_rpow_le_small_rpow 0 (1 - s') (Real.log 2) (1 / 5) (by linarith)
      (Real.log_nonneg (by norm_num)) (by norm_num),
    constant_rpow_le_small_rpow (1 - s₂) (1 - s') 1 (1 / 5) (by linarith) (by norm_num)
      (by norm_num)] with n e1 e2 e3 e4 e5
  rw [Real.rpow_zero, mul_one] at e4
  linarith

theorem coarseHit_of_domination (hDom : CoarseDominationStatement) : CoarseHitStatement := by
  intro p s₂ hfe hce hbe hqs hskb hszP hsD Ω _ W β hβ
  have hbe' := hbe
  obtain ⟨hq0, hqu, hur, hr1, hfield, hqhalf⟩ := hbe'
  have hce' := hce
  obtain ⟨hb0, hbf, hz0, hγ0, hkb0, hkbz, hkbγ, hkba, hkbb, hzsb, hγsb, hasb⟩ := hce'
  have hD : 0 < p.D := by linarith
  have hr0 : 0 < p.r := by linarith
  set s' := (p.q + s₂) / 2 with hs'
  have hβ0 : 0 ≤ β := by linarith
  have hDn := hDom p hfe hce W β hβ
  have hf := primitiveJointGibbs_sparseFieldBadSet_stretched_tail β p.r p.uField s' hr0 hr1 hur
    (by linarith)
  have hb := sparseBoundaryMassBound_stretched_decay β p.r p.uField p.q s' hr0 hr1 hur hqu hqhalf
    (by linarith)
  have hx := transfer_exponent_eventually β p.kb p.zP p.D s' s₂ hβ0 (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)
  filter_upwards [hDn, hf, hb, hx, eventually_ge_atTop 1] with n hEn hfn hbn hxn hn
  obtain ⟨E, hE, hEc, hdom⟩ := hEn
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set δ : ℝ := (smoothing p n : ℝ) with hδdef
  have hδ0 : 0 ≤ δ := NNReal.coe_nonneg _
  have hδ1 : δ ≤ 1 := smoothing_le_one p n hn hD
  have hδval : δ = (n : ℝ) ^ (-p.D) := by
    rw [hδdef]
    unfold smoothing
    exact Real.coe_toNNReal _ (Real.rpow_nonneg (by linarith) _)
  set c := 1 - δ with hc
  set s := Real.sqrt (δ * (2 - δ)) with hs
  have hcs : c ^ 2 + s ^ 2 = 1 := regression_coeff_sq δ hδ0 hδ1
  set L : ℝ := (n : ℝ) ^ (1 - p.kb)
  set Perr : ℝ := (n : ℝ) ^ (1 - p.zP)
  set k := restrictedKernel W β hβ p n E
  set k' := cappedKernel W β hβ p n E L
  have hkk' : ∀ᵐ g ∂primLaw n, ∀ x, k g x = k' g x := by
    filter_upwards [hdom] with g hg x
    exact (min_eq_left (hg x)).symm
  have hk'm : ∀ x, Measurable (fun z => k' z x) := fun x =>
    (measurable_restrictedKernel W β hβ p n E hE x).min (measurable_dominationBound β n L x)
  have hk'0 : ∀ z x, 0 ≤ k' z x := fun z x =>
    le_min (restrictedKernel_nonneg W β hβ p n E z x) (Real.exp_pos _).le
  have hk'1 : ∀ z x, k' z x ≤ 1 := fun z x =>
    (min_le_left _ _).trans (restrictedKernel_le_one W β hβ p n E z x)
  have hk'dom : ∀ z x, k' z x ≤ Real.exp (-(n : ℝ) * parisiPressure β + L +
      β * goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) x z) := fun z x => min_le_right _ _
  have hreg := gaussianRegression_intrinsic_annealed_boundary_mass_le hn0 β c s (parisiPressure β)
    L Perr 12 ((n : ℝ) ^ (-p.d)) (Real.exp (-((n : ℝ) ^ (1 - p.q)))) (by linarith)
    (hammingRadius p n) ((n : ℝ) ^ (1 - p.uField)) k' hk'm hk'0 hk'1 hk'dom
  have hsel := primitiveJointGibbs_pressureSelectedSparseBoundary_probability_le (n := n) β
    ((n : ℝ) ^ (-p.d)) (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12 (hammingRadius p n)
    ((n : ℝ) ^ (1 - p.uField)) (parisiPressure β) Perr
  have hsp := primitiveJointGibbs_selectedSparseBoundary_probability_le (r := hammingRadius p n)
    hn0 β ((n : ℝ) ^ (-p.d)) (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12 ((n : ℝ) ^ (1 - p.uField))
    (Real.exp_pos _).le
  have hJ : (primitiveJointGibbsLaw n β (1 / Real.sqrt (2 * (n : ℝ)))).real
      {q | q.2 ∈ pressureSelectedSparseBoundary β ((n : ℝ) ^ (-p.d))
        (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12 (hammingRadius p n) ((n : ℝ) ^ (1 - p.uField))
        (parisiPressure β) Perr q.1} ≤ 2 * Real.exp (-((n : ℝ) ^ (1 - s'))) := by
    have h1 : sparseBoundaryMassBound n β (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12
        (hammingRadius p n) ((n : ℝ) ^ (1 - p.uField)) ≤ Real.exp (-((n : ℝ) ^ (1 - s'))) := hbn
    have h2 : (primitiveJointGibbsLaw n β (1 / Real.sqrt (2 * (n : ℝ)))).real
        (annealedSparseFieldBadSet n (hammingRadius p n) ((n : ℝ) ^ (1 - p.uField))) ≤
        Real.exp (-((n : ℝ) ^ (1 - s'))) := hfn
    linarith
  have hcost : L + Perr + (1 - c) * |β| * (n : ℝ) * 12 / 2 + β ^ 2 * s ^ 2 * (n : ℝ) / 4 ≤
      (n : ℝ) ^ (1 - p.kb) + (n : ℝ) ^ (1 - p.zP) +
        (6 * β + β ^ 2 / 2) * (n : ℝ) ^ (1 - p.D) := by
    have hnD : δ * (n : ℝ) = (n : ℝ) ^ (1 - p.D) := by
      rw [hδval, show (1 : ℝ) - p.D = -p.D + 1 by ring, Real.rpow_add (by linarith),
        Real.rpow_one]
    have hs2 : s ^ 2 ≤ 2 * δ := by
      rw [hs, Real.sq_sqrt (mul_nonneg hδ0 (by linarith))]
      have e : δ * (2 - δ) = 2 * δ - δ ^ 2 := by ring
      rw [e]
      linarith [sq_nonneg δ]
    rw [abs_of_nonneg hβ0, show 1 - c = δ by rw [hc]; ring]
    have hb2 : β ^ 2 * s ^ 2 * (n : ℝ) / 4 ≤ β ^ 2 * (2 * δ) * (n : ℝ) / 4 := by
      have := sq_nonneg β
      have : (0 : ℝ) ≤ n := by linarith
      gcongr
    rw [← hnD]
    linarith [hb2, show δ * β * (n : ℝ) * 12 / 2 = 6 * β * (δ * n) by ring,
      show β ^ 2 * (2 * δ) * (n : ℝ) / 4 = β ^ 2 / 2 * (δ * n) by ring,
      show (6 * β + β ^ 2 / 2) * (δ * n) = 6 * β * (δ * n) + β ^ 2 / 2 * (δ * n) by ring]
  set X := L + Perr + (1 - c) * |β| * (n : ℝ) * 12 / 2 + β ^ 2 * s ^ 2 * (n : ℝ) / 4 with hX
  have hcostX : X ≤ (n : ℝ) ^ (1 - p.kb) + (n : ℝ) ^ (1 - p.zP) +
      (6 * β + β ^ 2 / 2) * (n : ℝ) ^ (1 - p.D) := hcost
  clear_value X
  have hfinal : Real.exp X * (2 * Real.exp (-((n : ℝ) ^ (1 - s')))) ≤
      Real.exp (-((n : ℝ) ^ (1 - s₂))) := by
    have he : Real.exp X * (2 * Real.exp (-((n : ℝ) ^ (1 - s')))) =
        Real.exp (X + Real.log 2 - (n : ℝ) ^ (1 - s')) := by
      rw [show X + Real.log 2 - (n : ℝ) ^ (1 - s') = X + Real.log 2 + -((n : ℝ) ^ (1 - s')) by ring,
        Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
      ring
    rw [he]
    apply Real.exp_le_exp.mpr
    linarith
  have hsplit := hit_le_regression W β hβ p n hn hD E hE
  rw [regressionMass_integral_congr_ae n c s hcs k k' hkk'] at hsplit
  calc ((angleLaw W p n).map (regressionInput p n)).real (coarseHitEvent W β hβ p n)
      ≤ (runLaw W p n).real Eᶜ + ∫ G, gaussianRegressionSetMass c s k' (excludedSet β p n) G
          ∂primLaw n := hsplit
    _ ≤ Real.exp (-((n : ℝ) ^ (1 - p.sb))) + Real.exp (-((n : ℝ) ^ (1 - s₂))) := by
        gcongr
        refine hreg.trans ?_
        refine (mul_le_mul_of_nonneg_left (hJ) (Real.exp_pos _).le).trans hfinal

end SKConstants.Blueprint
