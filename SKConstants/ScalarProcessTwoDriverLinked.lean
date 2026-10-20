module
public import SKConstants.GaussianTwoDriverLikelihood
public import SKConstants.ScalarProcessHiddenChannel
public import SKConstants.ScalarProcessPosteriorIncrement

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def PairedGaussianHistory : ℕ → Type
  | 0 => PUnit
  | n+1 => PairedGaussianHistory n × (ℝ × ℝ)

instance pairedGaussianHistoryMeasurableSpace (n : ℕ) : MeasurableSpace (PairedGaussianHistory n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace PUnit)
  | succ n ih => exact @MeasurableSpace.prod (PairedGaussianHistory n) (ℝ×ℝ) ih inferInstance

def pairedGaussianHistoryLaw (h : ℕ → ℝ≥0) : (n : ℕ) → Measure (PairedGaussianHistory n)
  | 0 => Measure.dirac PUnit.unit
  | n+1 => (pairedGaussianHistoryLaw h n).prod ((gaussianReal 0 (h n)).prod (gaussianReal 0 (h n)))

instance pairedGaussianHistoryLaw_isProbability (h : ℕ → ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (pairedGaussianHistoryLaw h n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n ih => change IsProbabilityMeasure ((pairedGaussianHistoryLaw h n).prod _); infer_instance

abbrev PairedGaussianCoefficient := (n : ℕ) → PairedGaussianHistory n → ℝ × ℝ

def pairedGaussianStepFactor (a : ℝ×ℝ) (h : ℝ≥0) (p : ℝ×ℝ) : ℝ :=
  gaussianExponentialFactor a.1 h p.1 * gaussianExponentialFactor a.2 h p.2

lemma pairedGaussianStepFactor_pos (a : ℝ×ℝ) (h : ℝ≥0) (p : ℝ×ℝ) :
    0 < pairedGaussianStepFactor a h p :=
  mul_pos (gaussianExponentialFactor_pos _ _ _) (gaussianExponentialFactor_pos _ _ _)

lemma lintegral_pairedGaussianStepFactor (a : ℝ×ℝ) (h : ℝ≥0) :
    ∫⁻ p, ENNReal.ofReal (pairedGaussianStepFactor a h p)
      ∂(gaussianReal 0 h).prod (gaussianReal 0 h) = 1 := by
  simp_rw [pairedGaussianStepFactor, ENNReal.ofReal_mul (gaussianExponentialFactor_pos _ _ _).le]
  rw [lintegral_prod_mul (f:=fun b => ENNReal.ofReal (gaussianExponentialFactor a.1 h b))
    (g:=fun d => ENNReal.ofReal (gaussianExponentialFactor a.2 h d))
    (by unfold gaussianExponentialFactor; fun_prop)
    (by unfold gaussianExponentialFactor; fun_prop)]
  simp only [lintegral_gaussianExponentialFactor, mul_one]

def pairedGaussianExponential (H : PairedGaussianCoefficient) (h : ℕ → ℝ≥0) :
    (n : ℕ) → PairedGaussianHistory n → ℝ
  | 0, _ => 1
  | n+1, p => pairedGaussianExponential H h n p.1 * pairedGaussianStepFactor (H n p.1) (h n) p.2

lemma pairedGaussianExponential_pos (H : PairedGaussianCoefficient) (h : ℕ → ℝ≥0)
    (n : ℕ) (p : PairedGaussianHistory n) : 0 < pairedGaussianExponential H h n p := by
  induction n with
  | zero => exact zero_lt_one
  | succ n ih => exact mul_pos (ih p.1) (pairedGaussianStepFactor_pos _ _ _)

lemma measurable_pairedGaussianExponential (H : PairedGaussianCoefficient)
    (hH : ∀ n, Measurable (H n)) (h : ℕ → ℝ≥0) (n : ℕ) :
    Measurable (pairedGaussianExponential H h n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun p : PairedGaussianHistory n × (ℝ×ℝ) =>
      pairedGaussianExponential H h n p.1 * pairedGaussianStepFactor (H n p.1) (h n) p.2)
    unfold pairedGaussianStepFactor gaussianExponentialFactor
    have hm : Measurable (fun p : PairedGaussianHistory n × (ℝ×ℝ) => H n p.1) := (hH n).comp measurable_fst
    exact (ih.comp measurable_fst).mul (by fun_prop)

def pairedGaussianTiltStep (H : PairedGaussianCoefficient) (h : ℕ → ℝ≥0) (n : ℕ) :
    Kernel (PairedGaussianHistory n) (ℝ×ℝ) :=
  (Kernel.const _ ((gaussianReal 0 (h n)).prod (gaussianReal 0 (h n)))).withDensity
    (fun p v => ENNReal.ofReal (pairedGaussianStepFactor (H n p) (h n) v))

lemma pairedGaussianTiltStep_isMarkov (H : PairedGaussianCoefficient)
    (hH : ∀ n, Measurable (H n)) (h : ℕ → ℝ≥0) (n : ℕ) :
    IsMarkovKernel (pairedGaussianTiltStep H h n) := by
  constructor
  intro p
  constructor
  have hm : Measurable (fun p : PairedGaussianHistory n × (ℝ×ℝ) =>
      ENNReal.ofReal (pairedGaussianStepFactor (H n p.1) (h n) p.2)) := by
    unfold pairedGaussianStepFactor gaussianExponentialFactor
    have h' : Measurable (fun p : PairedGaussianHistory n × (ℝ×ℝ) => H n p.1) := (hH n).comp measurable_fst
    fun_prop
  rw [pairedGaussianTiltStep, Kernel.withDensity_apply _ hm, Kernel.const_apply,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lintegral_pairedGaussianStepFactor _ _

lemma pairedGaussianTiltStep_apply_gaussian (H : PairedGaussianCoefficient)
    (hH : ∀ n, Measurable (H n)) (h : ℕ → ℝ≥0) (n : ℕ)
    (p : PairedGaussianHistory n) (hh : h n ≠ 0) :
    pairedGaussianTiltStep H h n p =
      (gaussianReal ((H n p).1*(h n:ℝ)) (h n)).prod
        (gaussianReal ((H n p).2*(h n:ℝ)) (h n)) := by
  have hm : Measurable (fun p : PairedGaussianHistory n × (ℝ×ℝ) =>
      ENNReal.ofReal (pairedGaussianStepFactor (H n p.1) (h n) p.2)) := by
    unfold pairedGaussianStepFactor gaussianExponentialFactor
    have h' : Measurable (fun p : PairedGaussianHistory n × (ℝ×ℝ) => H n p.1) := (hH n).comp measurable_fst
    fun_prop
  rw [pairedGaussianTiltStep, Kernel.withDensity_apply _ hm, Kernel.const_apply]
  simpa only [one_mul, mul_one, pairedGaussianStepFactor] using
    gaussian_pair_withDensity_twoDriver 1 (H n p).1 (H n p).2 (h n) hh

def pairedGaussianLinkedHistoryLaw (H : PairedGaussianCoefficient) (h : ℕ → ℝ≥0) :
    (n : ℕ) → Measure (PairedGaussianHistory n)
  | 0 => Measure.dirac PUnit.unit
  | n+1 => pairedGaussianLinkedHistoryLaw H h n ⊗ₘ pairedGaussianTiltStep H h n

lemma pairedGaussianLinkedHistoryLaw_isProbability (H : PairedGaussianCoefficient)
    (hH : ∀ n, Measurable (H n)) (h : ℕ → ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (pairedGaussianLinkedHistoryLaw H h n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
    let := ih
    let := pairedGaussianTiltStep_isMarkov H hH h n
    change IsProbabilityMeasure (_ ⊗ₘ pairedGaussianTiltStep H h n)
    infer_instance

theorem pairedGaussianLinkedHistoryLaw_eq_withDensity (H : PairedGaussianCoefficient)
    (hH : ∀ n, Measurable (H n)) (h : ℕ → ℝ≥0) (n : ℕ) :
    pairedGaussianLinkedHistoryLaw H h n = (pairedGaussianHistoryLaw h n).withDensity
      (fun p => ENNReal.ofReal (pairedGaussianExponential H h n p)) := by
  induction n with
  | zero => simp [pairedGaussianLinkedHistoryLaw, pairedGaussianHistoryLaw, pairedGaussianExponential]
  | succ n ih =>
    let := pairedGaussianTiltStep_isMarkov H hH h n
    let hs : IsSFiniteKernel ((Kernel.const (PairedGaussianHistory n)
        ((gaussianReal 0 (h n)).prod (gaussianReal 0 (h n)))).withDensity
        (fun p v => ENNReal.ofReal (pairedGaussianStepFactor (H n p) (h n) v))) := by
      change IsSFiniteKernel (pairedGaussianTiltStep H h n)
      infer_instance
    have hm : Measurable (fun p : PairedGaussianHistory n × (ℝ×ℝ) =>
        ENNReal.ofReal (pairedGaussianStepFactor (H n p.1) (h n) p.2)) := by
      unfold pairedGaussianStepFactor gaussianExponentialFactor
      have h' : Measurable (fun p : PairedGaussianHistory n × (ℝ×ℝ) => H n p.1) := (hH n).comp measurable_fst
      fun_prop
    change (pairedGaussianLinkedHistoryLaw H h n ⊗ₘ pairedGaussianTiltStep H h n) = _
    rw [ih]
    have he := Measure.withDensity_compProd_withDensity
      (μ:=pairedGaussianHistoryLaw h n)
      (κ:=Kernel.const (PairedGaussianHistory n) ((gaussianReal 0 (h n)).prod (gaussianReal 0 (h n))))
      (g:=fun p v => ENNReal.ofReal (pairedGaussianStepFactor (H n p) (h n) v))
      (measurable_pairedGaussianExponential H hH h n).ennreal_ofReal hm
    rw [pairedGaussianTiltStep, he, Measure.compProd_const]
    apply withDensity_congr_ae
    exact ae_of_all _ (fun p => (ENNReal.ofReal_mul (pairedGaussianExponential_pos H h n p.1).le).symm)

def pairedGaussianBShare (H : PairedGaussianCoefficient) : PairedGaussianCoefficient :=
  fun n p => ((H n p).1,0)

def pairedGaussianDShare (H : PairedGaussianCoefficient) : PairedGaussianCoefficient :=
  fun n p => (0,(H n p).2)

lemma measurable_pairedGaussianBShare (H : PairedGaussianCoefficient) (hH : ∀ n, Measurable (H n)) :
    ∀ n, Measurable (pairedGaussianBShare H n) := fun n => (hH n).fst.prodMk measurable_const

lemma measurable_pairedGaussianDShare (H : PairedGaussianCoefficient) (hH : ∀ n, Measurable (H n)) :
    ∀ n, Measurable (pairedGaussianDShare H n) := fun n => measurable_const.prodMk (hH n).snd

lemma pairedGaussianExponential_factorization (H : PairedGaussianCoefficient) (h : ℕ → ℝ≥0)
    (n : ℕ) (p : PairedGaussianHistory n) :
    pairedGaussianExponential H h n p =
      pairedGaussianExponential (pairedGaussianBShare H) h n p *
        pairedGaussianExponential (pairedGaussianDShare H) h n p := by
  induction n with
  | zero => simp [pairedGaussianExponential]
  | succ n ih =>
    simp only [pairedGaussianExponential, pairedGaussianStepFactor,
      pairedGaussianBShare, pairedGaussianDShare, gaussianExponentialFactor,
      zero_mul, zero_pow (by norm_num : 2≠0), zero_div, sub_self, Real.exp_zero, one_mul, mul_one]
    rw [ih p.1]
    ring

theorem pairedGaussianLinkedHistoryLaw_eq_reference_withDensity_B
    (H : PairedGaussianCoefficient) (hH : ∀ n, Measurable (H n)) (h : ℕ → ℝ≥0) (n : ℕ) :
    pairedGaussianLinkedHistoryLaw H h n =
      (pairedGaussianLinkedHistoryLaw (pairedGaussianDShare H) h n).withDensity
        (fun p => ENNReal.ofReal (pairedGaussianExponential (pairedGaussianBShare H) h n p)) := by
  rw [pairedGaussianLinkedHistoryLaw_eq_withDensity H hH h n,
    pairedGaussianLinkedHistoryLaw_eq_withDensity _ (measurable_pairedGaussianDShare H hH) h n,
    ← withDensity_mul _
      (measurable_pairedGaussianExponential _ (measurable_pairedGaussianDShare H hH) h n).ennreal_ofReal
      (measurable_pairedGaussianExponential _ (measurable_pairedGaussianBShare H hH) h n).ennreal_ofReal]
  apply withDensity_congr_ae
  exact ae_of_all _ (fun p => by
    simp only [Pi.mul_apply]
    rw [pairedGaussianExponential_factorization, ENNReal.ofReal_mul (pairedGaussianExponential_pos _ _ _ _).le,
      mul_comm])

def scalarTwoDriverEulerField (x z : ℝ) (h : ℕ → ℝ≥0) (ρ s : ℕ → ℝ) :
    (n : ℕ) → PairedGaussianHistory n → ℝ
  | 0, _ => z
  | n+1, p => scalarTwoDriverEulerField x z h ρ s n p.1 +
      Real.tanh (scalarTwoDriverEulerField x z h ρ s n p.1)*(h n:ℝ) +
      ρ n*p.2.1+s n*p.2.2

lemma measurable_scalarTwoDriverEulerField (x z : ℝ) (h : ℕ → ℝ≥0) (ρ s : ℕ → ℝ) (n : ℕ) :
    Measurable (scalarTwoDriverEulerField x z h ρ s n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun p : PairedGaussianHistory n × (ℝ×ℝ) =>
      scalarTwoDriverEulerField x z h ρ s n p.1 +
        Real.tanh (scalarTwoDriverEulerField x z h ρ s n p.1)*(h n:ℝ)+ρ n*p.2.1+s n*p.2.2)
    have hm : Measurable (fun p : PairedGaussianHistory n × (ℝ×ℝ) => scalarTwoDriverEulerField x z h ρ s n p.1) := ih.comp measurable_fst
    have ht := scalar_tanh_lipschitz.continuous.measurable.comp hm
    exact ((hm.add (ht.mul_const _)).add (measurable_snd.fst.const_mul _)).add
      (measurable_snd.snd.const_mul _)

def scalarTwoDriverPosteriorCoefficient (x z : ℝ) (h : ℕ → ℝ≥0) (ρ s : ℕ → ℝ) :
    PairedGaussianCoefficient := fun n p =>
  (ρ n*(x-Real.tanh (scalarTwoDriverEulerField x z h ρ s n p)),
    s n*(x-Real.tanh (scalarTwoDriverEulerField x z h ρ s n p)))

lemma measurable_scalarTwoDriverPosteriorCoefficient (x z : ℝ) (h : ℕ → ℝ≥0) (ρ s : ℕ → ℝ) :
    ∀ n, Measurable (scalarTwoDriverPosteriorCoefficient x z h ρ s n) := by
  intro n
  unfold scalarTwoDriverPosteriorCoefficient
  have hm := measurable_scalarTwoDriverEulerField x z h ρ s n
  have ht : Measurable (fun p => x-Real.tanh (scalarTwoDriverEulerField x z h ρ s n p)) :=
    measurable_const.sub (scalar_tanh_lipschitz.continuous.measurable.comp hm)
  exact (ht.const_mul _).prodMk (ht.const_mul _)

theorem scalarTwoDriverEulerField_linked_next_hasLaw (x z : ℝ) (h : ℕ → ℝ≥0)
    (ρ s : ℕ → ℝ) (n : ℕ) (p : PairedGaussianHistory n)
    (hh : h n ≠ 0) (hrs : (ρ n)^2+(s n)^2=1) :
    HasLaw (fun v : ℝ×ℝ => scalarTwoDriverEulerField x z h ρ s (n+1) (p,v))
      (gaussianReal (scalarTwoDriverEulerField x z h ρ s n p+x*(h n:ℝ)) (h n))
      (pairedGaussianTiltStep (scalarTwoDriverPosteriorCoefficient x z h ρ s) h n p) := by
  rw [pairedGaussianTiltStep_apply_gaussian _ (measurable_scalarTwoDriverPosteriorCoefficient x z h ρ s) h n p hh]
  let y := scalarTwoDriverEulerField x z h ρ s n p
  let ξ := x-Real.tanh y
  change HasLaw _ _ ((gaussianReal ((ρ n*ξ)*(h n:ℝ)) (h n)).prod
    (gaussianReal ((s n*ξ)*(h n:ℝ)) (h n)))
  let μ := (gaussianReal ((ρ n*ξ)*(h n:ℝ)) (h n)).prod
    (gaussianReal ((s n*ξ)*(h n:ℝ)) (h n))
  have hb : HasLaw (Prod.fst : ℝ×ℝ → ℝ) (gaussianReal ((ρ n*ξ)*(h n:ℝ)) (h n)) μ :=
    (measurePreserving_fst (μ:=gaussianReal ((ρ n*ξ)*(h n:ℝ)) (h n))
      (ν:=gaussianReal ((s n*ξ)*(h n:ℝ)) (h n))).hasLaw
  have hd : HasLaw (Prod.snd : ℝ×ℝ → ℝ) (gaussianReal ((s n*ξ)*(h n:ℝ)) (h n)) μ :=
    (measurePreserving_snd (μ:=gaussianReal ((ρ n*ξ)*(h n:ℝ)) (h n))
      (ν:=gaussianReal ((s n*ξ)*(h n:ℝ)) (h n))).hasLaw
  have hi : IndepFun (fun v : ℝ×ℝ => ρ n*v.1) (fun v : ℝ×ℝ => s n*v.2) μ :=
    (indepFun_prod (μ:=gaussianReal ((ρ n*ξ)*(h n:ℝ)) (h n))
      (ν:=gaussianReal ((s n*ξ)*(h n:ℝ)) (h n)) measurable_id measurable_id).comp
        (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  have hs := gaussianReal_add_gaussianReal_of_indepFun hi
    (gaussianReal_const_mul hb (ρ n)) (gaussianReal_const_mul hd (s n))
  have hvar : NNReal.mk ((ρ n)^2) (sq_nonneg _) * h n+
      NNReal.mk ((s n)^2) (sq_nonneg _) * h n=h n := by
    apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk]
    nlinarith [congrArg (fun a : ℝ => a*(h n:ℝ)) hrs]
  rw [hvar] at hs
  have hsum : HasLaw (fun v : ℝ×ℝ => ρ n*v.1+s n*v.2)
      (gaussianReal (ρ n*((ρ n*ξ)*(h n:ℝ))+s n*((s n*ξ)*(h n:ℝ))) (h n)) μ :=
    ⟨by fun_prop, hs⟩
  have hmean : ρ n*((ρ n*ξ)*(h n:ℝ))+s n*((s n*ξ)*(h n:ℝ))+
      (y+Real.tanh y*(h n:ℝ))=y+x*(h n:ℝ) := by
    dsimp [ξ]
    nlinarith [congrArg (fun a : ℝ => a*((x-Real.tanh y)*(h n:ℝ))) hrs]
  have ht := gaussianReal_const_add hsum (y+Real.tanh y*(h n:ℝ))
  rw [hmean] at ht
  simpa only [scalarTwoDriverEulerField, y, add_assoc] using ht

def scalarTwoDriverEulerHistory (x z : ℝ) (h : ℕ → ℝ≥0) (ρ s : ℕ → ℝ) :
    (n : ℕ) → PairedGaussianHistory n → ScalarObservationHistory n
  | 0, _ => PUnit.unit
  | n+1, p => (scalarTwoDriverEulerHistory x z h ρ s n p.1,
      scalarTwoDriverEulerField x z h ρ s (n+1) p)

lemma measurable_scalarTwoDriverEulerHistory (x z : ℝ) (h : ℕ → ℝ≥0) (ρ s : ℕ → ℝ) (n : ℕ) :
    Measurable (scalarTwoDriverEulerHistory x z h ρ s n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).prodMk
      (measurable_scalarTwoDriverEulerField x z h ρ s (n+1))

lemma scalarLastField_scalarTwoDriverEulerHistory (x z : ℝ) (h : ℕ → ℝ≥0)
    (ρ s : ℕ → ℝ) (n : ℕ) (p : PairedGaussianHistory n) :
    scalarLastField z n (scalarTwoDriverEulerHistory x z h ρ s n p)=
      scalarTwoDriverEulerField x z h ρ s n p := by
  cases n <;> rfl

theorem scalarTwoDriverEulerHistory_linked_hasLaw (b : Bool) (z : ℝ) (h : ℕ → ℝ≥0)
    (ρ s : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hrs : ∀ n, (ρ n)^2+(s n)^2=1) (n : ℕ) :
    HasLaw (scalarTwoDriverEulerHistory (scalarHiddenSign b) z h ρ s n)
      (scalarHiddenObservationHistoryLaw b z h n)
      (pairedGaussianLinkedHistoryLaw (scalarTwoDriverPosteriorCoefficient (scalarHiddenSign b) z h ρ s) h n) := by
  let H := scalarTwoDriverPosteriorCoefficient (scalarHiddenSign b) z h ρ s
  have hH := measurable_scalarTwoDriverPosteriorCoefficient (scalarHiddenSign b) z h ρ s
  induction n with
  | zero =>
    constructor
    · exact measurable_const.aemeasurable
    · simp only [scalarTwoDriverEulerHistory, pairedGaussianLinkedHistoryLaw,
        scalarHiddenObservationHistoryLaw, Measure.map_const, measure_univ, one_smul]
  | succ n ih =>
    let := pairedGaussianLinkedHistoryLaw_isProbability H hH h n
    let := pairedGaussianTiltStep_isMarkov H hH h n
    constructor
    · exact (measurable_scalarTwoDriverEulerHistory _ z h ρ s (n+1)).aemeasurable
    · apply Measure.ext_of_lintegral
      intro f hf
      rw [lintegral_map hf (measurable_scalarTwoDriverEulerHistory _ z h ρ s (n+1))]
      let F : PairedGaussianHistory n × (ℝ×ℝ) → ℝ≥0∞ :=
        fun p => f (scalarTwoDriverEulerHistory (scalarHiddenSign b) z h ρ s (n+1) p)
      have hF : Measurable F := hf.comp (measurable_scalarTwoDriverEulerHistory _ z h ρ s (n+1))
      have hf' : Measurable (fun p : ScalarObservationHistory n × ℝ => f p) := hf
      change (∫⁻ p, F p
        ∂pairedGaussianLinkedHistoryLaw H h n ⊗ₘ pairedGaussianTiltStep H h n) =
        ∫⁻ p, f p ∂scalarHiddenObservationHistoryLaw b z h n ⊗ₘ scalarHiddenObservationStepKernel b z (h n) n
      rw [Measure.lintegral_compProd hF, Measure.lintegral_compProd hf']
      have he (p : PairedGaussianHistory n) :
          (∫⁻ v, f (scalarTwoDriverEulerHistory (scalarHiddenSign b) z h ρ s (n+1) (p,v))
            ∂pairedGaussianTiltStep H h n p) =
          ∫⁻ y, f (scalarTwoDriverEulerHistory (scalarHiddenSign b) z h ρ s n p,y)
            ∂scalarHiddenObservationStepKernel b z (h n) n
              (scalarTwoDriverEulerHistory (scalarHiddenSign b) z h ρ s n p) := by
        rw [scalarHiddenObservationStepKernel_apply, scalarLastField_scalarTwoDriverEulerHistory]
        have hg : Measurable (fun y : ℝ => f
            (scalarTwoDriverEulerHistory (scalarHiddenSign b) z h ρ s n p,y)) :=
          hf.comp (measurable_const.prodMk measurable_id)
        simpa only [Function.comp_def, scalarTwoDriverEulerHistory, H] using
          (scalarTwoDriverEulerField_linked_next_hasLaw (scalarHiddenSign b) z h ρ s n p (hh n) (hrs n)).lintegral_comp
            hg.aemeasurable
      change (∫⁻ p, ∫⁻ v, f (scalarTwoDriverEulerHistory (scalarHiddenSign b) z h ρ s (n+1) (p,v))
        ∂pairedGaussianTiltStep H h n p ∂pairedGaussianLinkedHistoryLaw H h n) = _
      simp_rw [he]
      exact ih.lintegral_comp hf'.lintegral_kernel_prod_right'.aemeasurable

end SKConstants
