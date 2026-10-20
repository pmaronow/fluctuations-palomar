module

public import SKConstants.Completion.Blueprint.Assembly
public import SKConstants.Completion.Blueprint4.NodesAt

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped NNReal ENNReal Topology unitInterval BigOperators

set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Blueprint4
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal SKConstants.Blueprint

attribute [local irreducible] runMag

theorem coarseHitAt_of_dominationAt (p : Parameters) (s₂ : ℝ) (hfe : FineExponents p)
    (hce : CoarseCommon p) (hbe : BoundaryExponents p) (hqs : p.q < s₂) (hskb : s₂ < p.kb)
    (hszP : s₂ < p.zP) (hsD : s₂ < p.D) (hDom : CoarseDominationAt p) : CoarseHitAt p s₂ := by
  intro Ω _ W β hβ
  have hfe' := hfe
  obtain ⟨hfa, haf, hkf0, hkfa, hkff, hkf1⟩ := hfe'
  have hbe' := hbe
  obtain ⟨hq0, hqu, hur, hr1, hfield, hqhalf⟩ := hbe'
  have hce' := hce
  obtain ⟨hb0, hbf, hz0, hγ0, hkb0, hkbz, hkbγ, hkba, hkbb, hγsb, hbsb, hasb⟩ := hce'
  have hD : 0 < p.D := by linarith
  have hr0 : 0 < p.r := by linarith
  set s' := (p.q + s₂) / 2 with hs'
  have hβ0 : 0 ≤ β := by linarith
  have hDn := hDom W β hβ
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

theorem sequenceGoodAt_of_nodes (p : Parameters) (sseq : ℝ) (hfe : FineExponents p)
    (hce : CoarseCommon p) (hbe : BoundaryExponents p) (hse : SequenceExponents p sseq)
    (hAngle : PerAngleLawNonnegativeExponentStatement)
    (hHit : ∀ s₂ : ℝ, p.q < s₂ → s₂ < p.kb → s₂ < p.zP → s₂ < p.D → CoarseHitAt p s₂)
    (hCont : CoarseContinuityAt p) (hPin : PinningAt p) : SequenceGoodAt p sseq := by
  intro Ω _ W β hβ
  have hse' := hse
  have hbe' := hbe
  have hfe' := hfe
  have hce' := hce
  obtain ⟨hr_sb, hq_sb, ha_g, hg_sb, hsb_s, hr_b, hq_kb, hq_D, hq_zP, hzP0, hzP, hD⟩ := hse'
  obtain ⟨hq0, hqu, hur, hr1, hfield, hqhalf⟩ := hbe'
  obtain ⟨hfa, haf, hkf0, hkfa, hkff, hkf1⟩ := hfe'
  obtain ⟨hb0, hbf, hz0, hγ0, hkb0, hkbz, hkbγ, hkba, hkbb, hγsb, hbsb, hasb⟩ := hce'
  have hr0 : 0 < p.r := by linarith
  set μ₂ := min (min p.kb p.zP) (min p.D p.sb) with hμ₂
  have hqμ : p.q < μ₂ := lt_min (lt_min hq_kb hq_zP) (lt_min hq_D hq_sb)
  set s₂ := (p.q + μ₂) / 2 with hs₂
  have hs₂q : p.q < s₂ := by linarith
  have hs₂μ : s₂ < μ₂ := by linarith
  have hs₂kb : s₂ < p.kb := lt_of_lt_of_le hs₂μ ((min_le_left _ _).trans (min_le_left _ _))
  have hs₂zP : s₂ < p.zP := lt_of_lt_of_le hs₂μ ((min_le_left _ _).trans (min_le_right _ _))
  have hs₂D : s₂ < p.D := lt_of_lt_of_le hs₂μ ((min_le_right _ _).trans (min_le_left _ _))
  have hs₂sb : s₂ < p.sb := lt_of_lt_of_le hs₂μ ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨c, hc, hC⟩ := hCont W β hβ
  have hH := hHit s₂ hs₂q hs₂kb hs₂zP hs₂D W β hβ
  have hP := hPin W β hβ
  have hA := hAngle p hD.le W
  have a1 := grid_absorb p.grid (1 - p.r) (1 - sseq) (1 / 64) 20 (by linarith) (by linarith)
    (by linarith) (by norm_num) (by norm_num)
  have a2 := grid_absorb p.grid 1 (1 - sseq) c 5 (by linarith) (by linarith) one_pos hc
    (by norm_num)
  have a3 := grid_absorb p.grid (1 - p.sb) (1 - sseq) 1 15 (by linarith) (by linarith)
    (by linarith) one_pos (by norm_num)
  have a4 := grid_absorb p.grid (1 - s₂) (1 - sseq) 1 5 (by linarith) (by linarith)
    (by linarith) one_pos (by norm_num)
  filter_upwards [hC, hH, hP, hA, a1, a2, a3, a4] with n hCn hHn hPn hAn h1 h2 h3 h4
  set R := hammingRadius p n with hR
  set ePin := 2 * Real.exp (-((R : ℝ) / 64)) with hePin
  set eHit := Real.exp (-((n : ℝ) ^ (1 - p.sb))) + Real.exp (-((n : ℝ) ^ (1 - s₂))) with heHit
  set eCont := Real.exp (-(c * n)) + 2 * Real.exp (-((n : ℝ) ^ (1 - p.sb))) with heCont
  have hpinC : ∀ θ k, (experimentLaw W p n).real (pinCoarseEvent W β hβ p n θ k R) ≤ ePin := by
    intro θ k
    have h := experiment_real_of_run W p n θ k (hAn θ k).2 _
      (measurableSet_pinGap W β hβ p n (readoutTime p.a p.b n) ((R : ℝ) / 4))
    exact (le_of_eq h).trans hPn.1
  have hpinF : ∀ θ k, (experimentLaw W p n).real (pinFineEvent W β hβ p n θ k R) ≤ ePin := by
    intro θ k
    have h := experiment_real_of_run W p n θ k (hAn θ k).2 _
      (measurableSet_pinGap W β hβ p n (readoutTime p.a p.f n) ((R : ℝ) / 4))
    exact (le_of_eq h).trans hPn.2
  have hhit : ∀ j ≤ gridSize p n, (experimentLaw W p n).real (hitEvent W β hβ p n j) ≤ eHit := by
    intro j hj
    rw [hitEvent_eq W β hβ p n j hj, experiment_real_of_regression W p n _ _ (hAn _ _).1 _
      (measurableSet_coarseHitEvent W β hβ p n)]
    exact hHn
  have hcont : ∀ j < gridSize p n, (experimentLaw W p n).real
      (contEvent W β hβ p n j R) ≤ eCont := by
    intro j hj
    unfold contEvent
    exact hCn j hj
  have hsum := notGood_le W β hβ p n ePin eCont eHit hpinC hpinF hcont hhit (by positivity)
    (by positivity)
  have hmE := gridSize_le p n
  have hRn : (n : ℝ) ^ (1 - p.r) ≤ R := Nat.le_ceil _
  have hePinle : ePin ≤ 2 * Real.exp (-((1 / 64) * (n : ℝ) ^ (1 - p.r))) := by
    rw [hePin]
    gcongr
    linarith
  have hcn : Real.exp (-(c * n)) = Real.exp (-(c * (n : ℝ) ^ (1 : ℝ))) := by
    rw [Real.rpow_one]
  rw [one_mul] at h3 h4
  rw [heCont, heHit, hcn] at hsum
  exact absorption_arith _ (gridSize p n : ℝ) (Real.exp ((n : ℝ) ^ p.grid)) ePin _ _ _ _ _ hsum
    (Nat.cast_nonneg _) hmE (by positivity) hePinle (Real.exp_pos _).le (Real.exp_pos _).le
    (Real.exp_pos _).le h1 h2 h3 h4

theorem witnessDecayAt_of_top_nodes (p : Parameters) (sseq : ℝ)
    (hFine : FineKLStatement) (hEnd : EndpointLawStatement) (hSeq : SequenceGoodAt p sseq)
    (hfe : FineExponents p) (hse : SequenceExponents p sseq) (hcov : CoverageExponents p sseq)
    {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Tendsto (fun n : ℕ => (skDisorderLaw n).real (lowFlowWitnessEvent β ((n : ℝ) ^ (-p.d))
      (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hFine p hfe W β hβ
  have hE := hEnd p W β hβ
  have hS := hSeq W β hβ
  obtain ⟨hd, heu, huD, hukf, hse', hds⟩ := hcov
  have hzP : p.zP < 1 / 2 := hse.2.2.2.2.2.2.2.2.2.2.1
  have hD : 0 < p.D := hse.2.2.2.2.2.2.2.2.2.2.2
  set Cp := max C 0 with hCp_def
  have hCp : 0 ≤ Cp := le_max_right _ _
  let b1 : ℕ → ℝ := fun n => β ^ 2 / 2 * (n : ℝ) ^ (p.uEnt - p.D) +
    Cp * (n : ℝ) ^ (p.uEnt - p.kf + p.D)
  let b2 : ℕ → ℝ := fun n => (primLaw n).real (parisiPressureUpperEvent n β p.zP)
  let b3 : ℕ → ℝ := fun n => Real.exp (-(1 / 2) * (n : ℝ) ^ (1 - sseq))
  have hb1 : Tendsto b1 atTop (𝓝 0) := by
    have h1 := tendsto_natCast_rpow_zero (p.uEnt - p.D) (by linarith)
    have h2 := tendsto_natCast_rpow_zero (p.uEnt - p.kf + p.D) (by linarith)
    simpa using (h1.const_mul (β ^ 2 / 2)).add (h2.const_mul Cp)
  have hb2 : Tendsto b2 atTop (𝓝 0) :=
    parisiPressureUpperEvent_probability_tendsto_zero β p.zP (by linarith) hzP
  have hb3 : Tendsto b3 atTop (𝓝 0) := by
    have h := (polynomial_stretched_decay (1 - sseq) 0 (1 / 2) (by linarith) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Real.rpow_zero, one_mul, b3, neg_mul] using h
  have hlim : Tendsto (fun n => b1 n + b2 n + b3 n) atTop (𝓝 0) := by
    simpa using (hb1.add hb2).add hb3
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [hC, hE, hS, eventually_ge_atTop 2,
    crossing_exponent_eventually p.uEnt p.d sseq (by linarith) hds] with n hCn hEn hSn hn2 hcross
  obtain ⟨hspin, hgauss, hkl⟩ := hCn
  have hn : 0 < n := by omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn2
  have hn0R : (0 : ℝ) < n := by linarith
  set t : ℝ := (n : ℝ) ^ (1 - p.uEnt) with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos hn0R _
  set K : ℝ := Cp * (n : ℝ) ^ (1 - p.kf) with hK_def
  have hK : 0 ≤ K := mul_nonneg hCp (Real.rpow_nonneg hn0R.le _)
  have hforward : klDiv (fineProposal W β hβ p n)
      ((primitiveJointGibbsLaw n β (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) ≤
      ENNReal.ofReal K := hkl.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hn0R.le _)))
  have hδval : ((smoothing p n : ℝ≥0) : ℝ) = (n : ℝ) ^ (-p.D) := by
    unfold smoothing
    exact Real.coe_toNNReal _ (Real.rpow_nonneg hn0R.le _)
  have hδ0 : smoothing p n ≠ 0 := by
    intro h
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    simp only [hδval, NNReal.coe_zero] at this
    exact (Real.rpow_pos_of_pos hn0R (-p.D)).ne' this
  have hδ1 : smoothing p n < 1 := by
    rw [← NNReal.coe_lt_coe, hδval, NNReal.coe_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg hnR (by linarith)
  let Wit : Set (Prim n) := {G | physical n G ∈ lowFlowWitnessEvent β ((n : ℝ) ^ (-p.d))
    (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12}
  have hWit : MeasurableSet Wit :=
    (measurableSet_lowFlowWitnessEvent _ _ _ _).preimage (continuous_goeMatrix _).measurable
  let Pg : Set (Prim n) := {G | primitiveGOEPressure n β G ≤
    (n : ℝ) * parisiPressure β + (n : ℝ) ^ (1 - p.zP)}
  have hPg : MeasurableSet Pg :=
    measurableSet_le (measurable_primitiveGOEPressure n β) measurable_const
  let KLbad : Set (Outer n) := {o | ENNReal.ofReal t ≤
    actualProposalOriginalTargetKL n β (fineProposal W β hβ p n) (smoothing p n) o}
  let T : Set (Outer n) := {o | o.1 ∈ Wit ∧ o.1 ∈ Pg ∧
    actualProposalOriginalTargetKL n β (fineProposal W β hβ p n) (smoothing p n) o ≤
      ENNReal.ofReal t}
  have hKLm := measurable_actualProposalOriginalTargetKL n β (fineProposal W β hβ p n)
    (smoothing p n)
  have hT : MeasurableSet T :=
    (hWit.preimage measurable_fst).inter ((hPg.preimage measurable_fst).inter
      (measurableSet_le hKLm measurable_const))
  have hwit_eq : (skDisorderLaw n).real (lowFlowWitnessEvent β ((n : ℝ) ^ (-p.d))
      (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12) = (outerLaw n).real (Wit ×ˢ univ) := by
    rw [measureReal_def, measureReal_def, outerLaw, Measure.prod_prod, measure_univ, mul_one]
    unfold skDisorderLaw
    rw [Nat.cast_ofNat, Measure.map_apply (continuous_goeMatrix _).measurable
      (measurableSet_lowFlowWitnessEvent _ _ _ _)]
    rfl
  have hcover : Wit ×ˢ (univ : Set (Prim n)) ⊆ KLbad ∪ (Pgᶜ ×ˢ univ) ∪ T := by
    intro o ho
    by_cases h1 : ENNReal.ofReal t ≤
        actualProposalOriginalTargetKL n β (fineProposal W β hβ p n) (smoothing p n) o
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : o.1 ∈ Pg
      · exact Or.inr ⟨ho.1, h2, (lt_of_not_ge h1).le⟩
      · exact Or.inl (Or.inr ⟨h2, trivial⟩)
  have hterm1 : (outerLaw n).real KLbad ≤ b1 n := by
    have h := actualProposal_original_target_KL_tail hn β (fineProposal W β hβ p n) hspin hgauss
      (smoothing p n) hδ0 hδ1 K hK hforward t ht
    have hA : 0 ≤ (smoothing p n : ℝ) * (β ^ 2 * ((n : ℝ) - 1) / 2) +
        K / (smoothing p n : ℝ) := by
      have : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
      positivity
    have hreal := ENNReal.toReal_mono (ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (ENNReal.ofReal_ne_zero_iff.mpr ht)) h
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal ht.le] at hreal
    refine hreal.trans ?_
    rw [hδval]
    exact coverage_bound_le β p.D p.uEnt p.kf Cp hCp n (by omega)
  have hterm2 : (outerLaw n).real (Pgᶜ ×ˢ univ) ≤ b2 n := by
    rw [measureReal_def, outerLaw, Measure.prod_prod, measure_univ, mul_one]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro G hG
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, Pg] at hG
    exact hG.le
  have hterm3 : (outerLaw n).real T ≤ b3 n := by
    have hpt : ∀ o ∈ T, Real.exp (-(2 * (t + Real.log 2) / (n : ℝ) ^ (-p.d))) ≤
        (internalLaw W p n).real (goodEvent W β hβ p n o)ᶜ := by
      intro o ho
      obtain ⟨hind, hX, hY⟩ := hEn o
      have h := crossing_lower_bound W β hβ p n hn o ho.1 ho.2.1 t ht.le ho.2.2 hind hX hY
      convert h using 2
      ring
    have h := outer_measureReal_le_of_pointwise W β hβ p n T hT _ hpt
    refine h.trans ?_
    calc Real.exp (2 * (t + Real.log 2) / (n : ℝ) ^ (-p.d)) *
          (experimentLaw W p n).real {z | z.2 ∉ goodEvent W β hβ p n z.1}
        ≤ Real.exp (2 * (t + Real.log 2) / (n : ℝ) ^ (-p.d)) *
          Real.exp (-((n : ℝ) ^ (1 - sseq))) :=
          mul_le_mul_of_nonneg_left hSn (Real.exp_pos _).le
      _ = Real.exp (2 * (t + Real.log 2) / (n : ℝ) ^ (-p.d) - (n : ℝ) ^ (1 - sseq)) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ b3 n := Real.exp_le_exp.mpr hcross
  rw [hwit_eq]
  calc (outerLaw n).real (Wit ×ˢ univ)
      ≤ (outerLaw n).real (KLbad ∪ (Pgᶜ ×ˢ univ) ∪ T) := measureReal_mono hcover
    _ ≤ (outerLaw n).real (KLbad ∪ (Pgᶜ ×ˢ univ)) + (outerLaw n).real T :=
        measureReal_union_le _ _
    _ ≤ (outerLaw n).real KLbad + (outerLaw n).real (Pgᶜ ×ˢ univ) + (outerLaw n).real T := by
        gcongr
        exact measureReal_union_le _ _
    _ ≤ b1 n + b2 n + b3 n := by linarith

end SKConstants.Blueprint4
