module
public import SKConstants.ParisiFullSpinRowMoments
public import SKConstants.ScalarNormalizedBrownianRows
public import SKConstants.ScalarProcessMixedRow

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d N : ℕ}
local instance ParisiFullMixedRows_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance ParisiFullMixedRows_localInstance2 (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

def actualParisiFullQuerySpinLaw (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (H : ℝ≥0) :
    Measure ((Bool × Ω) × A) := (actualParisiFullTerminalSpinLaw β W H).prod Z.law
instance actualParisiFullQuerySpinLaw_isProbability (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (H : ℝ≥0) : IsProbabilityMeasure (actualParisiFullQuerySpinLaw W Z β H) := by
  dsimp [actualParisiFullQuerySpinLaw]
  infer_instance

lemma actualParisiFullQuerySpinLaw_path_hasLaw (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (H : ℝ≥0) :
    HasLaw (fun u : (Bool × Ω) × A => u.1.2) W.law (actualParisiFullQuerySpinLaw W Z β H) := by
  refine ⟨(measurable_snd.comp measurable_fst).aemeasurable,?_⟩
  change (actualParisiFullQuerySpinLaw W Z β H).map (Prod.snd ∘ Prod.fst)=W.law
  rw [← Measure.map_map measurable_snd measurable_fst,actualParisiFullQuerySpinLaw,
    Measure.map_fst_prod,measure_univ,one_smul,actualParisiFullTerminalSpinLaw_path_marginal]

lemma actualParisiFullQuerySpinLaw_drivers_hasLaw (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (H : ℝ≥0) :
    HasLaw (fun u : (Bool × Ω) × A => (u.1.2,u.2)) (W.law.prod Z.law)
      (actualParisiFullQuerySpinLaw W Z β H) := by
  refine ⟨((measurable_snd.comp measurable_fst).prodMk measurable_snd).aemeasurable,?_⟩
  have he := Measure.map_prod_map (actualParisiFullTerminalSpinLaw β W H) Z.law measurable_snd measurable_id
  rw [actualParisiFullTerminalSpinLaw_path_marginal,Measure.map_id] at he
  exact he.symm

lemma actualParisiFullQuerySpinLaw_terminal_hasLaw (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (H : ℝ≥0) :
    HasLaw Prod.fst (actualParisiFullTerminalSpinLaw β W H) (actualParisiFullQuerySpinLaw W Z β H) :=
  (measurePreserving_fst (μ:=actualParisiFullTerminalSpinLaw β W H) (ν:=Z.law)).hasLaw

def actualParisiFullMixedRow (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1<β)
    (t q : ℕ → ℝ≥0) (d : ℕ) (u : (Bool × Ω) × A) : EuclideanSpace ℝ (Fin (d+(d+1))) :=
  WithLp.toLp 2 (Fin.append (actualParisiNormalizedPosteriorRow W β t d u.1.2).ofLp
    (Fin.append (scalarNormalizedBrownianRow (d:=d) (actualParisiQueryBrownianSystem W Z β hβ).B q (u.1.2,u.2)).ofLp
      (fun _ : Fin 1 => scalarHiddenSign u.1.1)))

lemma actualParisiFullMixedRow_inner (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1<β)
    (t q : ℕ → ℝ≥0) (u : (Bool × Ω) × A) (a : EuclideanSpace ℝ (Fin (d+(d+1)))) :
    ⟪actualParisiFullMixedRow W Z β hβ t q d u,a⟫_ℝ=
      ⟪actualParisiNormalizedPosteriorRow W β t d u.1.2,mixedPosteriorCoefficient a⟫_ℝ+
      ⟪scalarNormalizedBrownianRow (actualParisiQueryBrownianSystem W Z β hβ).B q (u.1.2,u.2),mixedInnovationCoefficient a⟫_ℝ+
      mixedSpinCoefficient a*scalarHiddenSign u.1.1 := by
  simp only [actualParisiFullMixedRow,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,
    WithLp.ofLp_toLp,Fin.sum_univ_add,Fin.append_left,Fin.append_right,mixedPosteriorCoefficient,
    mixedInnovationCoefficient,mixedSpinCoefficient,Fin.sum_univ_one]
  ring

lemma measurable_actualParisiFullMixedRow (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1<β)
    (t q : ℕ → ℝ≥0) (d : ℕ) : Measurable (actualParisiFullMixedRow W Z β hβ t q d) := by
  have hT : Measurable (fun u : (Bool × Ω) × A => actualParisiNormalizedPosteriorRow W β t d u.1.2) :=
    (measurable_actualParisiNormalizedPosteriorRow W β t d).comp (measurable_snd.comp measurable_fst)
  have hG : Measurable (fun u : (Bool × Ω) × A => scalarNormalizedBrownianRow (d:=d) (actualParisiQueryBrownianSystem W Z β hβ).B q (u.1.2,u.2)) := (measurable_scalarNormalizedBrownianRow (d:=d) (actualParisiQueryBrownianSystem W Z β hβ).B
    (actualParisiQueryBrownianSystem W Z β hβ).measurable q).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hS : Measurable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1) := (measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [actualParisiFullMixedRow,Fin.append_left,Function.comp_def] using
      (measurable_pi_apply j).comp ((WithLp.measurable_ofLp 2 _).comp hT)
  · refine Fin.addCases (fun j => ?_) (fun _ => ?_) j
    · simpa only [Fin.append_right,Fin.append_left,Function.comp_def] using
        (measurable_pi_apply j).comp ((WithLp.measurable_ofLp 2 _).comp hG)
    · simpa only [Fin.append_right] using hS

private lemma sqrt_sum_sq_le (K L : ℝ≥0) : (K.sqrt+L.sqrt)^2 ≤ 2*(K+L) := by
  apply NNReal.coe_le_coe.mp
  push_cast
  nlinarith [Real.sq_sqrt K.coe_nonneg,Real.sq_sqrt L.coe_nonneg,
    sq_nonneg (Real.sqrt (K:ℝ)-Real.sqrt (L:ℝ))]

lemma actualParisiFullMixedRow_unit_hasSubgaussianMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1<β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (n : ℕ) (htn : t n=parisiEquilibriumPhysicalEndpoint β)
    (q : ℕ → ℝ≥0) (hq : StrictMono q) (hq0 : q 0=0) (m : ℕ)
    (g : ℕ → ℝ≥0) (hg : StrictMono g) (H : ℝ≥0)
    (a : EuclideanSpace ℝ (Fin ((n+m)+((n+m)+1)))) (ha : ‖a‖≤1) :
    HasSubgaussianMGF (fun u=>⟪actualParisiFullMixedRow W Z β hβ (actualParisiJoinedGrid β t n q) g (n+m) u,a⟫_ℝ)
      (4*actualParisiPosteriorRowMGFProxy W β (parisiEquilibriumPhysicalEndpoint β+q m)+8)
      (actualParisiFullQuerySpinLaw W Z β H) := by
  let K := actualParisiPosteriorRowMGFProxy W β (parisiEquilibriumPhysicalEndpoint β+q m)
  have hn := mixedCoefficient_norm_sq a
  have ha2 : ‖a‖^2≤1 := by nlinarith [norm_nonneg a]
  have hTnorm : ‖mixedPosteriorCoefficient a‖≤1 := by
    nlinarith [sq_nonneg (mixedSpinCoefficient a),sq_nonneg ‖mixedInnovationCoefficient a‖,norm_nonneg (mixedPosteriorCoefficient a)]
  have hGnorm : ‖mixedInnovationCoefficient a‖≤1 := by
    nlinarith [sq_nonneg (mixedSpinCoefficient a),sq_nonneg ‖mixedPosteriorCoefficient a‖,norm_nonneg (mixedInnovationCoefficient a)]
  have hSnorm : (mixedSpinCoefficient a)^2≤1 := by
    nlinarith [sq_nonneg ‖mixedPosteriorCoefficient a‖,sq_nonneg ‖mixedInnovationCoefficient a‖]
  have hT : HasSubgaussianMGF
      (fun u : (Bool × Ω) × A => ⟪actualParisiNormalizedPosteriorRow W β (actualParisiJoinedGrid β t n q) (n+m) u.1.2,mixedPosteriorCoefficient a⟫_ℝ) K
      (actualParisiFullQuerySpinLaw W Z β H) := by
    apply HasSubgaussianMGF.of_map (X:=fun w => ⟪actualParisiNormalizedPosteriorRow W β (actualParisiJoinedGrid β t n q) (n+m) w,mixedPosteriorCoefficient a⟫_ℝ) (actualParisiFullQuerySpinLaw_path_hasLaw W Z β H).aemeasurable
    rw [(actualParisiFullQuerySpinLaw_path_hasLaw W Z β H).map_eq]
    exact actualParisiNormalizedJoinedPosteriorRow_unit_hasSubgaussianMGF W β hβ t ht n htn q hq hq0 m _ hTnorm
  have hG : HasSubgaussianMGF
      (fun u : (Bool × Ω) × A => ⟪scalarNormalizedBrownianRow (actualParisiQueryBrownianSystem W Z β hβ).B g (u.1.2,u.2),mixedInnovationCoefficient a⟫_ℝ) 1
      (actualParisiFullQuerySpinLaw W Z β H) := by
    apply HasSubgaussianMGF.of_map (X:=fun u => ⟪scalarNormalizedBrownianRow (actualParisiQueryBrownianSystem W Z β hβ).B g u,mixedInnovationCoefficient a⟫_ℝ) (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).aemeasurable
    rw [(actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).map_eq]
    exact scalarNormalizedBrownianRow_unit_hasSubgaussianMGF _ _
      (actualParisiQueryBrownianSystem W Z β hβ).brownian.toIsPreBrownianReal g hg _ hGnorm
  have hS : HasSubgaussianMGF (fun u : (Bool × Ω) × A => mixedSpinCoefficient a*scalarHiddenSign u.1.1) 1
      (actualParisiFullQuerySpinLaw W Z β H) := by
    have h : HasSubgaussianMGF (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1) 1
        (actualParisiFullQuerySpinLaw W Z β H) := by
      apply HasSubgaussianMGF.of_map (X:=fun u : Bool × Ω => scalarHiddenSign u.1) (actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β H).aemeasurable
      rw [(actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β H).map_eq]
      exact actualParisiFullTerminalSpinLaw_spin_hasSubgaussianMGF W β hβ H
    apply Concentration.hasSubgaussianMGF_of_proxy_le (h.const_mul _)
    apply NNReal.coe_le_coe.mp
    change (mixedSpinCoefficient a)^2*1≤(1:ℝ)
    simpa only [mul_one] using hSnorm
  have hTG := Concentration.hasSubgaussianMGF_of_proxy_le (hT.add hG) (sqrt_sum_sq_le K 1)
  have hAll := Concentration.hasSubgaussianMGF_of_proxy_le (hTG.add hS) (sqrt_sum_sq_le (2*(K+1)) 1)
  have hFinal := Concentration.hasSubgaussianMGF_of_proxy_le hAll (show 2*(2*(K+1)+1)≤4*K+8 by
    apply NNReal.coe_le_coe.mp;push_cast;linarith)
  simpa only [actualParisiFullMixedRow_inner] using hFinal

theorem actualParisiFullMixedRow_secondMoment_le
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1<β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (n : ℕ) (htn : t n=parisiEquilibriumPhysicalEndpoint β)
    (q : ℕ → ℝ≥0) (hq : StrictMono q) (hq0 : q 0=0) (m : ℕ)
    (g : ℕ → ℝ≥0) (hg : StrictMono g) (H : ℝ≥0)
    (a : EuclideanSpace ℝ (Fin ((n+m)+((n+m)+1)))) :
    (∫ u,⟪actualParisiFullMixedRow W Z β hβ (actualParisiJoinedGrid β t n q) g (n+m) u,a⟫_ℝ^2
      ∂actualParisiFullQuerySpinLaw W Z β H) ≤ 3*‖a‖^2 := by
  let μ := actualParisiFullQuerySpinLaw W Z β H
  let u := actualParisiJoinedGrid β t n q
  let T : (Bool × Ω) × A → ℝ := fun w => ⟪actualParisiNormalizedPosteriorRow W β u (n+m) w.1.2,mixedPosteriorCoefficient a⟫_ℝ
  let G : (Bool × Ω) × A → ℝ := fun w => ⟪scalarNormalizedBrownianRow (actualParisiQueryBrownianSystem W Z β hβ).B g (w.1.2,w.2),mixedInnovationCoefficient a⟫_ℝ
  let S : (Bool × Ω) × A → ℝ := fun w => mixedSpinCoefficient a*scalarHiddenSign w.1.1
  have hmT : Measurable (fun w => ⟪actualParisiNormalizedPosteriorRow W β u (n+m) w,mixedPosteriorCoefficient a⟫_ℝ) := by
    have hm := measurable_actualParisiNormalizedPosteriorRow W β u (n+m)
    fun_prop
  have hmG : Measurable (fun w => ⟪scalarNormalizedBrownianRow (actualParisiQueryBrownianSystem W Z β hβ).B g w,mixedInnovationCoefficient a⟫_ℝ) := by
    have hm := measurable_scalarNormalizedBrownianRow (d:=n+m) (actualParisiQueryBrownianSystem W Z β hβ).B
      (actualParisiQueryBrownianSystem W Z β hβ).measurable g
    fun_prop
  have hmS : Measurable (fun w : Bool × Ω => mixedSpinCoefficient a*scalarHiddenSign w.1) := by
    have hm := measurable_of_finite scalarHiddenSign
    fun_prop
  have hT : HasSubgaussianMGF T
      (actualParisiPosteriorRowMGFProxy W β (parisiEquilibriumPhysicalEndpoint β+q m)*‖mixedPosteriorCoefficient a‖₊^2) μ := by
    apply HasSubgaussianMGF.of_map (X:=fun w => ⟪actualParisiNormalizedPosteriorRow W β u (n+m) w,mixedPosteriorCoefficient a⟫_ℝ)
      (actualParisiFullQuerySpinLaw_path_hasLaw W Z β H).aemeasurable
    rw [(actualParisiFullQuerySpinLaw_path_hasLaw W Z β H).map_eq]
    exact actualParisiNormalizedJoinedPosteriorRow_hasSubgaussianMGF W β hβ t ht n htn q hq hq0 m _
  have hG : HasSubgaussianMGF G (∑ i : Fin (n+m),NNReal.mk ((mixedInnovationCoefficient a i)^2) (sq_nonneg _)) μ := by
    apply HasSubgaussianMGF.of_map (X:=fun w => ⟪scalarNormalizedBrownianRow (actualParisiQueryBrownianSystem W Z β hβ).B g w,mixedInnovationCoefficient a⟫_ℝ)
      (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).aemeasurable
    rw [(actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).map_eq]
    exact scalarNormalizedBrownianRow_linearForm_hasSubgaussianMGF _ _
      (actualParisiQueryBrownianSystem W Z β hβ).brownian.toIsPreBrownianReal g hg _
  have hS : HasSubgaussianMGF S (NNReal.mk ((mixedSpinCoefficient a)^2) (sq_nonneg _)*1) μ := by
    apply HasSubgaussianMGF.of_map (X:=fun w : Bool × Ω => mixedSpinCoefficient a*scalarHiddenSign w.1)
      (actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β H).aemeasurable
    rw [(actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β H).map_eq]
    exact (actualParisiFullTerminalSpinLaw_spin_hasSubgaussianMGF W β hβ H).const_mul _
  have hTint : Integrable (fun w => T w^2) μ := (hT.memLp 2).integrable_sq
  have hGint : Integrable (fun w => G w^2) μ := (hG.memLp 2).integrable_sq
  have hSint : Integrable (fun w => S w^2) μ := (hS.memLp 2).integrable_sq
  have hTE : (∫ w,T w^2 ∂μ)=‖mixedPosteriorCoefficient a‖^2 := by
    exact ((actualParisiFullQuerySpinLaw_path_hasLaw W Z β H).integral_comp (hmT.pow_const 2).aestronglyMeasurable).trans
      (actualParisiNormalizedPosteriorRow_secondMoment W β hβ u
        (actualParisiJoinedGrid_strictMono β t ht n htn q hq hq0) (n+m) _)
  have hGE : (∫ w,G w^2 ∂μ)=‖mixedInnovationCoefficient a‖^2 := by
    exact ((actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integral_comp (hmG.pow_const 2).aestronglyMeasurable).trans
      (scalarNormalizedBrownianRow_linearForm_secondMoment _ _
        (actualParisiQueryBrownianSystem W Z β hβ).brownian.toIsPreBrownianReal g hg _)
  have hSE : (∫ w,S w^2 ∂μ)=(mixedSpinCoefficient a)^2 := by
    calc
      _=(∫ w : Bool × Ω,(mixedSpinCoefficient a*scalarHiddenSign w.1)^2 ∂actualParisiFullTerminalSpinLaw β W H) :=
        (actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β H).integral_comp (hmS.pow_const 2).aestronglyMeasurable
      _=_ := by
        have he (w : Bool × Ω) : (mixedSpinCoefficient a*scalarHiddenSign w.1)^2=
            (mixedSpinCoefficient a)^2*(scalarHiddenSign w.1)^2 := by ring
        simp_rw [he]
        rw [integral_const_mul,actualParisiFullTerminalSpinLaw_spin_secondMoment,mul_one]
  have hPoint (w : (Bool × Ω) × A) : (T w+G w+S w)^2≤3*(T w^2+G w^2+S w^2) := by
    nlinarith [sq_nonneg (T w-G w),sq_nonneg (T w-S w),sq_nonneg (G w-S w)]
  calc
    _ = ∫ w,(T w+G w+S w)^2 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun w => congrArg (fun x : ℝ=>x^2)
        (actualParisiFullMixedRow_inner W Z β hβ u g w a))
    _ ≤ ∫ w,3*(T w^2+G w^2+S w^2) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ (fun _=>sq_nonneg _))
        ((hTint.add hGint).add hSint |>.const_mul 3) (ae_of_all _ hPoint)
    _ = 3*((∫ w,T w^2 ∂μ)+(∫ w,G w^2 ∂μ)+(∫ w,S w^2 ∂μ)) := by
      rw [integral_const_mul]
      have hs := integral_add (hTint.add hGint) hSint
      have ht := integral_add hTint hGint
      simp only [Pi.add_apply] at hs ht
      rw [hs,ht]
    _ = 3*(‖mixedPosteriorCoefficient a‖^2+‖mixedInnovationCoefficient a‖^2+(mixedSpinCoefficient a)^2) := by
      rw [hTE,hGE,hSE]
    _ = _ := by rw [← mixedCoefficient_norm_sq]

end SKConstants
