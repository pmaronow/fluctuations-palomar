module

public import SKConstants.Completion.LM4b.ReplayPrimitives
public import SKConstants.Completion.LC4a.ConditionalCrossMoment
public import SKConstants.Completion.LC1.StieltjesCrossMoment

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Topology

namespace SKConstants.Completion.LM4b
open SKConstantsOAI.ZeroTemperatureSK LC4a LM4 LC1
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def actualRowDCoefficient (W : BrownianSystem Ω) (β : ℝ) (t : ℝ≥0)
    (u : (Bool × Ω) × A) : ℝ :=
  actualParisiQuerySigma W β t * actualParisiSpinLinkCoefficient β u.1.1 t
    (actualParisiFullScalarProcess W β t u.1.2)

omit [MeasurableSpace A] in
theorem actualRowDCoefficient_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ≥0) (u : (Bool × Ω) × A) : |actualRowDCoefficient W β t u| ≤ 2 := by
  rw [actualRowDCoefficient, abs_mul,
    abs_of_nonneg (actualParisiQuerySigma_bounds W β hβ t).1]
  exact (mul_le_mul (actualParisiQuerySigma_bounds W β hβ t).2
    (actualParisiSpinLinkCoefficient_bound β u.1.1 t _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 2)

omit [MeasurableSpace A] in
theorem actualRowDCoefficient_eq_defect (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ≥0) (u : (Bool × Ω) × A) :
    actualRowDCoefficient W β t u = actualParisiQuerySigma W β t *
      (scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β t u.1.2) :=
  sigma_mul_spinLinkCoefficient W β hβ _ _ _

def actualRowDLeftSum (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (l : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  ∑ k ∈ Finset.range (2^l), actualRowDCoefficient W β ((brownianDyadicGrid V).time l k) u *
    ((actualParisiAuxBrownianSystem W Z β hβ).B ((brownianDyadicGrid V).time l (k+1)) (u.1.2,u.2) -
      (actualParisiAuxBrownianSystem W Z β hβ).B ((brownianDyadicGrid V).time l k) (u.1.2,u.2))

def actualRowDBracket (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (u : (Bool × Ω) × A) : ℝ :=
  ∫ t in (0:ℝ)..(V:ℝ), (actualRowDCoefficient W β t.toNNReal u)^2

theorem measurable_actualRowDCoefficient (W : BrownianSystem Ω) (β : ℝ) (t : ℝ≥0) :
    Measurable (actualRowDCoefficient (A := A) W β t) := by
  have hs : Measurable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1) :=
    (measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)
  have hy : Measurable (fun u : (Bool × Ω) × A => actualParisiFullScalarProcess W β t u.1.2) :=
    (measurable_actualParisiPreContinuationField W β t).comp (measurable_snd.comp measurable_fst)
  have hm := ((continuous_actualParisiFullMagnetization β).measurable.comp ((measurable_const (a:=(t:ℝ))).prodMk hy))
  have ha := ((continuous_actualParisiFullCurvature β).measurable.comp ((measurable_const (a:=(t:ℝ))).prodMk hy))
  exact (((hs.mul ha).div (measurable_const.add (hs.mul hm))).const_mul _)

theorem measurable_actualRowDLeftSum (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) :
    Measurable (actualRowDLeftSum W Z β hβ V l) := by
  apply Finset.measurable_fun_sum
  intro k _
  exact (measurable_actualRowDCoefficient W β _).mul
    ((((actualParisiAuxBrownianSystem W Z β hβ).measurable _).sub
      ((actualParisiAuxBrownianSystem W Z β hβ).measurable _)).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem measurable_actualRowDBracket (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) :
    Measurable (actualRowDBracket (A := A) W β V) := by
  have hy : Measurable (fun p : ((Bool × Ω) × A) × ℝ =>
      actualParisiFullScalarProcess W β p.2.toNNReal p.1.1.2) := by
    have hm := measurable_fullScalar_real_shift W β 0
    simp only [zero_add] at hm
    have hp : Measurable (fun p : ((Bool × Ω) × A) × ℝ => (p.2,p.1.1.2)) :=
      measurable_snd.prodMk (measurable_snd.comp (measurable_fst.comp measurable_fst))
    simpa only [Function.comp_def] using hm.comp hp
  have hs : Measurable (fun p : ((Bool × Ω) × A) × ℝ => scalarHiddenSign p.1.1.1) :=
    (measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp (measurable_fst.comp measurable_fst))
  have ht : Measurable (fun p : ((Bool × Ω) × A) × ℝ => (p.2.toNNReal:ℝ)) :=
    measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_snd)
  have hm := (continuous_actualParisiFullMagnetization β).measurable.comp (ht.prodMk hy)
  have ha := (continuous_actualParisiFullCurvature β).measurable.comp (ht.prodMk hy)
  have hsig := (continuous_actualParisiQuerySigma W β).measurable.comp ht
  have hc : Measurable (fun p : ((Bool × Ω) × A) × ℝ =>
      (actualRowDCoefficient W β p.2.toNNReal p.1)^2) :=
    ((hsig.mul ((hs.mul ha).div (measurable_const.add (hs.mul hm)))).pow_const 2)
  have hi := hc.stronglyMeasurable.integral_prod_right'
    (ν:=volume.restrict (Ioc (0:ℝ) (V:ℝ)))
  change Measurable (fun u : (Bool × Ω) × A => ∫ t in (0:ℝ)..(V:ℝ),
    (actualRowDCoefficient W β t.toNNReal u)^2)
  simp_rw [intervalIntegral.integral_of_le V.coe_nonneg]
  exact hi.measurable

omit [MeasurableSpace A] in
theorem actualRowDBracket_bounds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (u : (Bool × Ω) × A) :
    0 ≤ actualRowDBracket W β V u ∧ actualRowDBracket W β V u ≤ 4 * (V:ℝ) := by
  constructor
  · exact intervalIntegral.integral_nonneg V.coe_nonneg (fun _ _ => sq_nonneg _)
  · have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=(V:ℝ))
      (f:=fun t => (actualRowDCoefficient W β t.toNNReal u)^2) (C:=4) (fun t _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hb := actualRowDCoefficient_bound W β hβ t.toNNReal u
        nlinarith [sq_abs (actualRowDCoefficient W β t.toNNReal u), abs_nonneg (actualRowDCoefficient W β t.toNNReal u)])
    change (∫ t in (0:ℝ)..(V:ℝ), (actualRowDCoefficient W β t.toNNReal u)^2) ≤ 4*(V:ℝ)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg V.coe_nonneg] using (le_abs_self _).trans hh

def IsActualRowDIntegral (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (J : (Bool × Ω) × A → ℝ) : Prop :=
  MemLp J 2 (actualRowBaseLaw W Z) ∧
    (∀ l, Integrable (fun u => (actualRowDLeftSum W Z β hβ V l u-J u)^2) (actualRowBaseLaw W Z)) ∧
    Tendsto (fun l => ∫ u, (actualRowDLeftSum W Z β hβ V l u-J u)^2 ∂actualRowBaseLaw W Z)
      atTop (𝓝 0)

def ActualRowReferenceTransportStatement
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (i : Fin (ranks+q)) : Prop :=
  IdentDistrib
    (fun u => ((fun l => replayRowLeftSum W β hβ δ hδ ranks q V i l u),
      replayRowBracket W β hβ δ hδ ranks q V i u))
    (fun u => ((fun l => actualRowDLeftSum W Z β hβ V l u), actualRowDBracket W β V u))
    (growingReplayUnlinkedLaw W δ ranks q) (actualRowBaseLaw W Z)

theorem actualRowDLeftSum_hasSubgaussianMGF_of_transport
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (i : Fin (ranks+q))
    (htransport : ActualRowReferenceTransportStatement W Z β hβ δ hδ ranks q V i) (l : ℕ) :
    HasSubgaussianMGF (actualRowDLeftSum W Z β hβ V l) (4*V) (actualRowBaseLaw W Z) :=
  (replayRowLeftSum_hasSubgaussianMGF W β hβ δ hδ ranks q V i l).congr_identDistrib
    (htransport.comp ((measurable_pi_apply l).comp measurable_fst))

theorem actualRowDIntegral_hasSubgaussianMGF_of_transport
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (i : Fin (ranks+q))
    (htransport : ActualRowReferenceTransportStatement W Z β hβ δ hδ ranks q V i)
    (J : (Bool × Ω) × A → ℝ) (hJ : IsActualRowDIntegral W Z β hβ V J) :
    HasSubgaussianMGF J (4*V) (actualRowBaseLaw W Z) :=
  hasSubgaussianMGF_of_tendsto_integral_sq
    (actualRowDLeftSum_hasSubgaussianMGF_of_transport W Z β hβ δ hδ ranks q V i htransport)
    hJ.2.1 hJ.2.2 tendsto_const_nhds

theorem actualRowDIntegral_exists_of_transport
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (i : Fin (ranks+q))
    (htransport : ActualRowReferenceTransportStatement W Z β hβ δ hδ ranks q V i) :
    ∃ J : (Bool × Ω) × A → ℝ, Measurable J ∧ IsActualRowDIntegral W Z β hβ V J := by
  let := W.isProbability
  let X := actualRowDLeftSum W Z β hβ V
  let μ := actualRowBaseLaw W Z
  have hmem (l : ℕ) : MemLp (X l) 2 μ :=
    (actualRowDLeftSum_hasSubgaussianMGF_of_transport W Z β hβ δ hδ ranks q V i htransport l).memLp 2
  let F : ℕ → Lp ℝ 2 μ := fun l => (hmem l).toLp (X l)
  have hcauchy : CauchySeq F := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨N,hN⟩ := brownianVectorContinuousCoordinateLeftSum_L2_cauchy
      (parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q) W.law W.B i
      W.brownian.toIsPreBrownianReal W.measurable
      (fun t u => actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q t u i)
      (fun t => (measurable_pi_apply i).comp (measurable_replayDCoefficient W β hβ δ hδ ranks q t))
      2 (fun t u => replayDCoefficient_bound W β hβ δ hδ ranks q t u i)
      (replayDCoefficient_continuous_ae W β hβ δ hδ ranks q i)
      (brownianDyadicGrid V) 1 (brownianDyadicWidth V) (brownianDyadicWidth_tendsto V)
      (fun l d j _ => brownianDyadicGrid_left_le V l d j) (ε^2) (sq_pos_of_pos hε)
    refine ⟨N,fun m hm l hl => ?_⟩
    have hd : dist (F m) (F l)^2 = ∫ u, (X m u-X l u)^2 ∂μ := by
      rw [dist_eq_norm]
      exact norm_toLp_difference_sq_eq_integral (hmem m) (hmem l)
    have hdiff := htransport.comp
      (((measurable_pi_apply m).comp measurable_fst).sub
        ((measurable_pi_apply l).comp measurable_fst) |>.pow_const 2)
    have he : (∫ u, (X m u-X l u)^2 ∂μ) =
        ∫ u, (replayRowLeftSum W β hβ δ hδ ranks q V i m u -
          replayRowLeftSum W β hβ δ hδ ranks q V i l u)^2
          ∂growingReplayUnlinkedLaw W δ ranks q := hdiff.integral_eq.symm
    have hb := hN m hm l hl
    change (∫ u, (replayRowLeftSum W β hβ δ hδ ranks q V i m u -
      replayRowLeftSum W β hβ δ hδ ranks q V i l u)^2
        ∂growingReplayUnlinkedLaw W δ ranks q) < ε^2 at hb
    rw [← he, ← hd] at hb
    nlinarith [dist_nonneg (x:=F m) (y:=F l)]
  obtain ⟨J,hJ⟩ := cauchySeq_tendsto_of_complete hcauchy
  let K := (Lp.memLp J).aestronglyMeasurable.mk (fun u => J u)
  have hJK : (fun u => J u) =ᵐ[μ] K := (Lp.memLp J).aestronglyMeasurable.ae_eq_mk
  refine ⟨K, (Lp.memLp J).aestronglyMeasurable.measurable_mk,
    (Lp.memLp J).ae_eq hJK, ?_, ?_⟩
  · intro l
    exact (((hmem l).sub (Lp.memLp J)).integrable_sq).congr
      (hJK.mono (fun u hu => by
        change J u = K u at hu
        dsimp only [X, Pi.sub_apply]
        rw [hu]))
  · have hn : Tendsto (fun l => ‖F l-J‖^2) atTop (𝓝 0) := by
      simpa using ((hJ.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => J) atTop (𝓝 J))).norm).pow 2
    convert hn using 1
    funext l
    calc
      _ = ∫ u, (X l u-J u)^2 ∂μ := integral_congr_ae (hJK.mono (fun u hu => by
        change J u = K u at hu
        dsimp only [X, Pi.sub_apply]
        rw [hu]))
      _ = _ := (norm_toLp_sub_sq_eq_integral (hmem l) J).symm

theorem actualRow_reference_primitives_of_transport
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (i : Fin (ranks+q))
    (htransport : ActualRowReferenceTransportStatement W Z β hβ δ hδ ranks q V i) :
    ∃ J : (Bool × Ω) × A → ℝ,
      Measurable J ∧ Measurable (actualRowDBracket (A:=A) W β V) ∧
      IsActualRowDIntegral W Z β hβ V J ∧
      HasSubgaussianMGF J (4*V) (actualRowBaseLaw W Z) ∧
      (∀ᵐ u ∂actualRowBaseLaw W Z,
        0 ≤ actualRowDBracket W β V u ∧ actualRowDBracket W β V u ≤ 4*(V:ℝ)) := by
  obtain ⟨J,hJm,hJ⟩ := actualRowDIntegral_exists_of_transport W Z β hβ δ hδ ranks q V i htransport
  exact ⟨J,hJm,measurable_actualRowDBracket W β V,hJ,
    actualRowDIntegral_hasSubgaussianMGF_of_transport W Z β hβ δ hδ ranks q V i htransport J hJ,
    ae_of_all _ (actualRowDBracket_bounds W β hβ V)⟩

end SKConstants.Completion.LM4b
