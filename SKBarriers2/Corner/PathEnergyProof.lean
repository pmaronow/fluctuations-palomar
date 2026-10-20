module

public import SKBarriers2.Corner.MassSensitivityC2Proof3
public import SKBarriers2.Corner.KStabilityClose

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem qBoundedJets_secondCenteredScore_order {n : ℕ} {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential (n+3) B f) (hg : QBoundedJets (n+3) A g)
    (μ : ℝ) (v w : E) (t : ℝ) :
    QBoundedJets (n+1) ((A*‖v‖+|μ| *B*‖v‖+B*‖w‖)*|t|)
      (fun x => secondCenteredScore μ v w f g x t) := by
  have hgp : QPotential (n+2) A g :=
    (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by omega : n+2 ≤ n+3))).potential
  have hG := hgp.increment (t • v)
  have hF := ((hf.of_le (by omega : n+2 ≤ n+3)).increment (t • v)).const_smul μ
  have hD := (((hf.derivativeJets.of_le (by omega : n+1 ≤ n+2)).apply_const w).translate
    (t • v)).const_smul t
  convert (hG.add hF).add hD using 1
  · rw [norm_smul, Real.norm_eq_abs]
    ring
  · rfl

theorem qBoundedJets_secondScoreVariance_order {n : ℕ} {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential (n+3) B f) (hg : QBoundedJets (n+3) A g)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (μ : ℝ) (v w : E) (hv : ‖v‖ ≤ 1) :
    QBoundedJets (n+1)
      (potentialCovarianceCoefficient (n+1) B *
        (A*‖v‖+|μ| *B*‖v‖+B*‖w‖)^2)
      (secondScoreVariance m μ v w f g) := by
  let C := A*‖v‖+|μ| *B*‖v‖+B*‖w‖
  have hC : 0 ≤ C := by dsimp only [C]; positivity [hf.nonneg, hg.nonneg]
  have hline : ContDiff ℝ (n+1) (fun z : ℝ × E => z.2+z.1 • v) :=
    contDiff_snd.add (contDiff_fst.smul contDiff_const)
  have hfs : ContDiff ℝ (n+1) f := hf.smooth.of_le (by
    exact_mod_cast (show n+1 ≤ n+3 by omega))
  have hgs : ContDiff ℝ (n+1) g := hg.smooth.of_le (by
    exact_mod_cast (show n+1 ≤ n+3 by omega))
  have hD : ContDiff ℝ (n+1) (fun z : ℝ × E => fderiv ℝ f (z.2+z.1 • v) w) :=
    ((hf.smooth.fderiv_right (m := n+1) (by
      exact_mod_cast (show n+1+1 ≤ n+3 by omega))).comp hline).clm_apply contDiff_const
  have hR : ContDiff ℝ (n+1)
      (fun z : ℝ × E => secondCenteredScore μ v w f g z.2 z.1) :=
    (((hgs.comp hline).sub (hgs.comp contDiff_snd)).add
      (contDiff_const.mul ((hfs.comp hline).sub (hfs.comp contDiff_snd)))).add
        (contDiff_fst.mul hD)
  have hRj (t : ℝ) : QBoundedJets (n+1) (C*|t|^1)
      (fun x => secondCenteredScore μ v w f g x t) := by
    simpa only [pow_one] using qBoundedJets_secondCenteredScore_order hf hg μ v w t
  have hR2j (t : ℝ) : QBoundedJets (n+1) (((2:ℝ)^(n+1)*C^2)*|t|^2)
      (fun x => secondCenteredScore μ v w f g x t^2) := by
    convert (hRj t).mul (hRj t) using 1
    · ring
    · funext x; ring
  have hM := qBoundedJets_noiseMean_poly (hf.of_le (by omega : n+1+1 ≤ n+3))
    hC 1 hR hRj hm v hv
  have hM2 := qBoundedJets_noiseMean_poly
    (g := fun x t => secondCenteredScore μ v w f g x t^2)
    (hf.of_le (by omega : n+1+1 ≤ n+3))
    (show 0 ≤ (2:ℝ)^(n+1)*C^2 by positivity) 2 (hR.pow 2) hR2j hm v hv
  convert hM2.sub (hM.mul hM) using 1
  · dsimp only [potentialCovarianceCoefficient]; ring
  · funext x; simp only [secondScoreVariance, pow_two]

theorem qBoundedJets_mixedDirectionSource_order {n : ℕ} {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential (n+3) B f) (hg : QBoundedJets (n+3) A g)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v w : E) :
    QBoundedJets (n+1) ((1+(2:ℝ)^(n+1)*B)*A*‖v‖*‖w‖)
      (mixedDirectionSource m v w f g) := by
  have hH := (hg.derivativeJets.derivativeJets.apply_const v).apply_const w
  have hW := (hg.derivativeJets.of_le (by omega : n+1 ≤ n+2)).apply_const w
  have hV := (hf.derivativeJets.of_le (by omega : n+1 ≤ n+2)).apply_const v
  have H := hH.add ((hW.mul hV).const_smul m)
  apply H.mono
  rw [abs_of_nonneg hm.1]
  calc
    _ ≤ A*‖v‖*‖w‖+(2:ℝ)^(n+1)*(A*‖w‖)*(B*‖v‖) := by
      apply add_le_add le_rfl
      exact mul_le_of_le_one_left (by positivity [hf.nonneg, hg.nonneg]) hm.2
    _ = _ := by ring

theorem qBoundedJets_noiseHessian_order {n : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential (n+3) B f) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
    (v w : E) (hv : ‖v‖ ≤ 1) :
    QBoundedJets (n+1) (noiseAverageCoefficient (n+1) 2 B*B*‖w‖^2)
      (fun x => noiseMean m v f x (fun t => t^2*
        fderiv ℝ (fderiv ℝ f) (x+t • v) w w)) := by
  have hH := (hf.derivativeJets.derivativeJets.apply_const w).apply_const w
  have hc : ContDiff ℝ (n+1) (fun z : ℝ × E => z.1^2*
      fderiv ℝ (fderiv ℝ f) (z.2+z.1 • v) w w) :=
    (contDiff_fst.pow 2).mul
      (hH.smooth.comp (contDiff_snd.add (contDiff_fst.smul contDiff_const)))
  have hj (t : ℝ) : QBoundedJets (n+1) ((B*‖w‖^2)*|t|^2)
      (fun x => t^2*fderiv ℝ (fderiv ℝ f) (x+t • v) w w) := by
    convert (hH.translate (t • v)).const_smul (t^2) using 1
    rw [abs_pow, sq_abs]; ring
  convert qBoundedJets_noiseMean_poly
    (g := fun x t => t^2*fderiv ℝ (fderiv ℝ f) (x+t • v) w w)
    (hf.of_le (by omega : n+1+1 ≤ n+3))
    (show 0 ≤ B*‖w‖^2 by positivity [hf.nonneg]) 2 hc hj hm v hv using 1
  ring

def secondVariationJetBound (n : ℕ) (B A H m dm ddm : ℝ) (v w b : E) : ℝ :=
  H+tiltedStabilityCoefficient (n+1) B*H*‖v‖^2+
    2*(tiltedCoarseCoefficient (n+1) B*(1+(2:ℝ)^(n+1)*B))*A*‖v‖*‖w‖+
    noiseAverageCoefficient (n+1) 2 B*B*‖w‖^2+
    directionSensitivityCoefficient (n+1) B*‖v‖*‖b‖+
    potentialCovarianceCoefficient (n+1) B*
      (A*‖v‖+|dm/m| *B*‖v‖+B*‖w‖)^2+
    massSensitivityJetCoefficient n B*‖v‖^2*|ddm-2*dm^2/m|

theorem qBoundedJets_secondVariationStep_order {n : ℕ} {B A H : ℝ} {f g q : E → ℝ}
    (hf : QPotential (n+3) B f) (hg : QBoundedJets (n+3) A g)
    (hq : QBoundedJets (n+1) H q)
    {m : ℝ} (hm : m ∈ Ioc (0:ℝ) 1) (v w b : E) (dm ddm : ℝ)
    (hv : ‖v‖ ≤ 1) (hsmall : B*‖v‖^2 ≤ 1/2) :
    QBoundedJets (n+1) (secondVariationJetBound n B A H m dm ddm v w b)
      (secondVariationStep m v f g q dm ddm w b) := by
  have hmcc : m ∈ Icc (0:ℝ) 1 := ⟨hm.1.le,hm.2⟩
  have hcurv : m*(B*‖v‖^2) ≤ 1/2 :=
    (mul_le_of_le_one_left (by positivity [hf.nonneg]) hm.2).trans hsmall
  have hT := qBoundedJets_tiltedAverage (n+1) hf (by omega) (by omega) hq hmcc v hcurv
  have hD := (qBoundedJets_tiltedAverage_coarse (n+1) hf (by omega) (by omega)
    (qBoundedJets_mixedDirectionSource_order hf hg hmcc v w) hmcc v).const_smul 2
  have hN := qBoundedJets_noiseHessian_order hf hmcc v w hv
  have hB := qBoundedJets_directionSensitivity hf hmcc v b
  have hV := qBoundedJets_secondScoreVariance_order hf hg hmcc (dm/m) v w hv
  have hVm : QBoundedJets (n+1)
      (potentialCovarianceCoefficient (n+1) B*(A*‖v‖+|dm/m| *B*‖v‖+B*‖w‖)^2)
      (fun x => m*secondScoreVariance m (dm/m) v w f g x) :=
    (hV.const_smul m).mono (mul_le_of_le_one_left hV.nonneg (by
      rw [abs_of_pos hm.1]; exact hm.2))
  have hM := (qBoundedJets_massSensitivity (n := n) hf hm v hv hsmall).const_smul
    (ddm-2*dm^2/m)
  convert ((((hT.add hD).add hN).add hB).add hVm).add hM using 1
  · dsimp only [secondVariationJetBound]; norm_num; ring
  · rfl

theorem secondVariationJetBound_le_source (n : ℕ) {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ A H m dm ddm : ℝ, 0 ≤ A → 0 ≤ H → 0 < m → m⁻¹ ≤ R →
      ∀ v w b : E,
      secondVariationJetBound n B A H m dm ddm v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * secondVariationSource A dm ddm v w b := by
  let T := |tiltedStabilityCoefficient (n+1) B|
  let D := |tiltedCoarseCoefficient (n+1) B * (1 + (2:ℝ)^(n+1) * B)|
  let N := |noiseAverageCoefficient (n+1) 2 B * B|
  let J := |directionSensitivityCoefficient (n+1) B|
  let Q := |potentialCovarianceCoefficient (n+1) B|
  let M := |massSensitivityJetCoefficient n B|
  have hT : 0 ≤ T := abs_nonneg _
  have hD : 0 ≤ D := abs_nonneg _
  have hN : 0 ≤ N := abs_nonneg _
  have hJ : 0 ≤ J := abs_nonneg _
  have hQ : 0 ≤ Q := abs_nonneg _
  have hM : 0 ≤ M := abs_nonneg _
  let K := 1 + T + 2 * D + N + J + 3 * Q * (1 + B ^ 2 * R ^ 2 + B ^ 2) + M * (1 + 2 * R)
  have hK : 0 < K := by dsimp only [K]; positivity
  have ht : T ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hd : 2 * D ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hn : N + 3 * Q * B ^ 2 ≤ K := by
    apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hj : J ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hq : 3 * Q ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hm0 : M ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hmq : 3 * Q * B ^ 2 * R ^ 2 + 2 * M * R ≤ K := by
    apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  refine ⟨K, hK, ?_⟩
  intro A H m dm ddm hA hH hm hinv v w b
  have hratio : |dm / m| ≤ |dm| * R := by
    rw [abs_div, abs_of_pos hm, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (abs_nonneg dm)
  have hscore : A * ‖v‖ + |dm / m| * B * ‖v‖ + B * ‖w‖ ≤
      A * ‖v‖ + |dm| * R * B * ‖v‖ + B * ‖w‖ := by
    gcongr
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ A * ‖v‖ + |dm / m| * B * ‖v‖ + B * ‖w‖)
    (by positivity : 0 ≤ A * ‖v‖ + |dm| * R * B * ‖v‖ + B * ‖w‖)).mpr hscore
  have hthree : (A * ‖v‖ + |dm| * R * B * ‖v‖ + B * ‖w‖) ^ 2 ≤
      3 * ((A * ‖v‖) ^ 2 + (|dm| * R * B * ‖v‖) ^ 2 + (B * ‖w‖) ^ 2) := by
    nlinarith [sq_nonneg (A * ‖v‖ - |dm| * R * B * ‖v‖),
      sq_nonneg (A * ‖v‖ - B * ‖w‖), sq_nonneg (|dm| * R * B * ‖v‖ - B * ‖w‖)]
  have hvar : Q * (A * ‖v‖ + |dm / m| * B * ‖v‖ + B * ‖w‖) ^ 2 ≤
      3 * Q * ‖v‖ ^ 2 * A ^ 2 + 3 * Q * B ^ 2 * R ^ 2 * ‖v‖ ^ 2 * dm ^ 2 +
        3 * Q * B ^ 2 * ‖w‖ ^ 2 := by
    have H' := mul_le_mul_of_nonneg_left (hsq.trans hthree) hQ
    simp only [mul_pow, sq_abs] at H'
    nlinarith only [H']
  have hmassAbs : |ddm - 2 * dm ^ 2 / m| ≤ |ddm| + 2 * dm ^ 2 * R := by
    apply (abs_sub _ _).trans
    apply add_le_add (le_refl |ddm|)
    rw [abs_div, abs_of_pos hm, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sq_nonneg dm), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hmass := mul_le_mul_of_nonneg_left hmassAbs
    (show 0 ≤ M * ‖v‖ ^ 2 by positivity)
  have hraw : secondVariationJetBound n B A H m dm ddm v w b ≤
      H + T * H * ‖v‖ ^ 2 + 2 * D * A * ‖v‖ * ‖w‖ + N * ‖w‖ ^ 2 +
        J * ‖v‖ * ‖b‖ + Q * (A * ‖v‖ + |dm / m| * B * ‖v‖ + B * ‖w‖) ^ 2 +
        M * ‖v‖ ^ 2 * |ddm - 2 * dm ^ 2 / m| := by
    dsimp only [secondVariationJetBound, T, D, N, J, Q, M]
    gcongr <;> exact le_abs_self _
  calc
    secondVariationJetBound n B A H m dm ddm v w b ≤
        H + T * H * ‖v‖ ^ 2 + (2 * D) * (A * ‖v‖ * ‖w‖) +
          (N + 3 * Q * B ^ 2) * ‖w‖ ^ 2 + J * (‖v‖ * ‖b‖) +
          (3 * Q) * (‖v‖ ^ 2 * A ^ 2) + M * (‖v‖ ^ 2 * |ddm|) +
          (3 * Q * B ^ 2 * R ^ 2 + 2 * M * R) * (‖v‖ ^ 2 * dm ^ 2) := by
      nlinarith only [hraw, hvar, hmass]
    _ ≤ H + K * H * ‖v‖ ^ 2 + K * (A * ‖v‖ * ‖w‖) + K * ‖w‖ ^ 2 +
        K * (‖v‖ * ‖b‖) + K * (‖v‖ ^ 2 * A ^ 2) + K * (‖v‖ ^ 2 * |ddm|) +
        K * (‖v‖ ^ 2 * dm ^ 2) := by
      gcongr
    _ ≤ (1 + K * ‖v‖ ^ 2) * H + K * secondVariationSource A dm ddm v w b := by
      dsimp only [secondVariationSource]
      rw [sq_abs]
      have hextra : 0 ≤ K * ‖v‖ ^ 2 * |dm| * A := by positivity
      nlinarith only [hextra]

section HigherSecondVariation

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem qBoundedJets_second_deriv_exponential_movingStep_order {F : P × E → ℝ}
    (hF : ParamRegular F) (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E)
    {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) {n : ℕ} {B A H : ℝ}
    (hf : QPotential (n+3) B (fun y => F (p k,y)))
    (hg : QBoundedJets (n+3) A (fun y => fderiv ℝ F (p k,y) (deriv p k,0)))
    (hh : QBoundedJets (n+1) H (fun y =>
      fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
        fderiv ℝ F (p k,y) (deriv (deriv p) k,0)))
    (hm : Real.exp (M (p k)) ≤ 1) (hv : ‖V (p k)‖ ≤ 1)
    (hsmall : B * ‖V (p k)‖ ^ 2 ≤ 1 / 2) :
    QBoundedJets (n+1)
      (secondVariationJetBound n B A H (Real.exp (M (p k)))
        (Real.exp (M (p k)) * M (deriv p k))
        (Real.exp (M (p k)) * ((M (deriv p k)) ^ 2 + M (deriv (deriv p) k)))
        (V (p k)) (V (deriv p k)) (V (deriv (deriv p) k)))
      (fun x => deriv (deriv (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
        (fun y => F (p t,y)) x)) k) := by
  have heq : (fun x => deriv (deriv (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
      (fun y => F (p t,y)) x)) k) =
      secondVariationStep (Real.exp (M (p k))) (V (p k))
        (fun y => F (p k,y)) (fun y => fderiv ℝ F (p k,y) (deriv p k,0))
        (fun y => fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
          fderiv ℝ F (p k,y) (deriv (deriv p) k,0))
        (Real.exp (M (p k)) * M (deriv p k))
        (Real.exp (M (p k)) * ((M (deriv p k)) ^ 2 + M (deriv (deriv p) k)))
        (V (deriv p k)) (V (deriv (deriv p) k)) :=
    funext (second_deriv_exponential_movingStep hF M V hp (hf.of_le (by omega)) (hg.of_le (by omega)) (hh.of_le (by omega)))
  rw [heq]
  exact qBoundedJets_secondVariationStep_order hf hg hh ⟨Real.exp_pos _, hm⟩ _ _ _ _ _ hv hsmall

theorem qBoundedJets_second_exponentialChain_order
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) {n : ℕ} {B R K : ℝ} {f : E → ℝ}
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient (n+3) B ≤ K)
    (hMass : massSensitivityJetCoefficient (n+2) B ≤ K)
    (hDir : directionSensitivityCoefficient (n+3) B ≤ K)
    (hsource : ∀ A H m dm ddm : ℝ, 0 ≤ A → 0 ≤ H → 0 < m → m⁻¹ ≤ R →
      ∀ v w b : E, secondVariationJetBound n B A H m dm ddm v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * secondVariationSource A dm ddm v w b)
    (hpotential : ∀ front tail, ps = front ++ tail →
      QPotential (n+5) B (vectorIncrementChain (ParamChain.exponentialSteps tail (p k)) f))
    (hgeometry : ∀ c ∈ ps, Real.exp (c.1 (p k)) ≤ 1 ∧ ‖c.2 (p k)‖ ≤ 1 ∧
      B * ‖c.2 (p k)‖ ^ 2 ≤ 1 / 2 ∧ (Real.exp (c.1 (p k)))⁻¹ ≤ R) :
    QBoundedJets (n+1)
      (exponentialSecondMajorant K (p k) (deriv p k) (deriv (deriv p) k) ps)
      (fun x => deriv (deriv (fun t => vectorIncrementChain
        (ParamChain.exponentialSteps ps (p t)) f x)) k) := by
  have hf : QPotential (n+5) B f := hpotential ps [] (by rw [List.append_nil])
  have hp1 := (hp.differentiableAt (by norm_num)).hasDerivAt
  induction ps with
  | nil =>
    simp only [ParamChain.exponentialSteps, List.map_nil, vectorIncrementChain, deriv_const',
      exponentialSecondMajorant]
    refine ⟨le_rfl, contDiff_const, ?_⟩
    intro j hj x
    simp
  | cons c ps ih =>
    have hpotTail : ∀ front tail, ps = front ++ tail →
        QPotential (n+5) B (vectorIncrementChain (ParamChain.exponentialSteps tail (p k)) f) := by
      intro front tail hsplit
      apply hpotential (c :: front) tail
      simpa only [List.cons_append, List.cons.injEq, true_and] using hsplit
    have hgeoTail : ∀ d ∈ ps, Real.exp (d.1 (p k)) ≤ 1 ∧ ‖d.2 (p k)‖ ≤ 1 ∧
        B * ‖d.2 (p k)‖ ^ 2 ≤ 1 / 2 ∧ (Real.exp (d.1 (p k)))⁻¹ ≤ R :=
      fun d hd => hgeometry d (List.mem_cons_of_mem c hd)
    have hinner := ih hpotTail hgeoTail
    have hfirst := qBoundedJets_first_exponentialChain (n := n+2) ps hp1 hK hTilt hMass hDir
      hpotTail (fun d hd => ⟨(hgeoTail d hd).1, (hgeoTail d hd).2.1, (hgeoTail d hd).2.2.1⟩)
    let F : P × E → ℝ := ParamChain.exponentialChain ps (fun z => f z.2)
    have hF : ParamRegular F := ParamChain.regular_exponentialChain ps
      (ParamChain.regular_fixedTerminal hf (by omega) P)
    have hGid : (fun y => fderiv ℝ F (p k,y) (deriv p k,0)) =
        fun y => deriv (fun t => vectorIncrementChain (ParamChain.exponentialSteps ps (p t)) f y) k := by
      funext y
      exact (((hF.1.differentiable (by norm_num) (p k,y)).hasFDerivAt.comp_hasDerivAt k
        (hp1.prodMk (hasDerivAt_const k y))).deriv).symm
    have hHid : (fun y => fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
        fderiv ℝ F (p k,y) (deriv (deriv p) k,0)) =
        fun y => deriv (deriv (fun t => vectorIncrementChain
          (ParamChain.exponentialSteps ps (p t)) f y)) k := by
      funext y
      exact (ParamChain.second_parameter_curve hF.1 hp y).symm
    have hG : QBoundedJets (n+3) (firstVariationMajorant K (p k) (deriv p k) ps)
        (fun y => fderiv ℝ F (p k,y) (deriv p k,0)) := by rw [hGid]; exact hfirst
    have hH : QBoundedJets (n+1) (exponentialSecondMajorant K (p k) (deriv p k) (deriv (deriv p) k) ps)
        (fun y => fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
          fderiv ℝ F (p k,y) (deriv (deriv p) k,0)) := by rw [hHid]; exact hinner
    have hgeo := hgeometry c (List.mem_cons_self ..)
    have hstep := qBoundedJets_second_deriv_exponential_movingStep_order hF c.1 c.2 hp
      ((hpotential [c] ps rfl).of_le (by omega : n+3 ≤ n+5)) hG hH
      hgeo.1 hgeo.2.1 hgeo.2.2.1
    apply hstep.mono
    exact hsource _ _ _ _ _ hG.nonneg hH.nonneg (Real.exp_pos _) hgeo.2.2.2 _ _ _

end HigherSecondVariation

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

private theorem pathEnergy_positive_masses_eventually (ps : List (ℝ → ℝ × E)) {k : ℝ}
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hpos : ∀ p ∈ ps, 0 < (p k).1) :
    ∀ᶠ t in 𝓝 k, ∀ p ∈ ps, 0 < (p t).1 := by
  have H : ∀ᶠ t in 𝓝 k, ∀ i : Fin ps.length, 0 < (ps.get i t).1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hreg _ (List.get_mem ps i)).fst.continuousAt.eventually
      (Ioi_mem_nhds (hpos _ (List.get_mem ps i)))
  filter_upwards [H] with t ht p hp
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
  exact ht i

theorem qBoundedJets_second_curveChain_order
    (ps : List (ℝ → ℝ × E)) {n : ℕ} {k B R K : ℝ} {f : E → ℝ}
    (hf : QPotential (n+5) B f)
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hpos : ∀ p ∈ ps, 0 < (p k).1)
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient (n+3) (B + 1) ≤ K)
    (hMass : massSensitivityJetCoefficient (n+2) (B + 1) ≤ K)
    (hDir : directionSensitivityCoefficient (n+3) (B + 1) ≤ K)
    (hsource : ∀ A H m dm ddm : ℝ, 0 ≤ A → 0 ≤ H → 0 < m → m⁻¹ ≤ R →
      ∀ v w b : E, secondVariationJetBound n (B + 1) A H m dm ddm v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * secondVariationSource A dm ddm v w b)
    (hgeometry : ∀ p ∈ ps, (p k).1 ≤ 1 ∧ ‖(p k).2‖ ≤ 1 ∧
      (B + 1) * ‖(p k).2‖ ^ 2 ≤ 1 / 2 ∧ ((p k).1)⁻¹ ≤ R)
    (hbudget : (stepStabilityCoefficient (n+5) (B + 1) + 1) *
      chainEnergy (ps.map (fun p => p k)) ≤ 1)
    (hcurv : (B + 1) * chainEnergy (ps.map (fun p => p k)) ≤ 1 / 2) :
    QBoundedJets (n+1) (curveSecondMajorant K k ps)
      (fun x => deriv (deriv (fun t =>
        vectorIncrementChain (ps.map (fun p => p t)) f x)) k) := by
  let p := ParamChain.logParameters ps
  let cs := ParamChain.coordinateSteps (X := E) ps.length
  have hp : ContDiffAt ℝ 2 p k := ParamChain.logParameters_contDiffAt ps hreg hpos
  have hpath : ParamChain.exponentialSteps cs (p k) = ps.map (fun p => p k) :=
    ParamChain.coordinateSteps_apply ps k hpos
  have hmass : ∀ c ∈ ParamChain.exponentialSteps cs (p k), c.1 ∈ Icc (0 : ℝ) 1 := by
    rw [hpath]
    intro c hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
    exact ⟨(hpos q hq).le, (hgeometry q hq).1⟩
  have hgeom : ∀ c ∈ cs, Real.exp (c.1 (p k)) ≤ 1 ∧ ‖c.2 (p k)‖ ≤ 1 ∧
      (B + 1) * ‖c.2 (p k)‖ ^ 2 ≤ 1 / 2 ∧ (Real.exp (c.1 (p k)))⁻¹ ≤ R := by
    intro c hc
    have hmem : (Real.exp (c.1 (p k)), c.2 (p k)) ∈ ParamChain.exponentialSteps cs (p k) :=
      List.mem_map.mpr ⟨c, hc, rfl⟩
    rw [hpath] at hmem
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hmem
    simpa only [heq] using hgeometry q hq
  have hpot : ∀ front tail, cs = front ++ tail →
      QPotential (n+5) (B + 1) (vectorIncrementChain (ParamChain.exponentialSteps tail (p k)) f) := by
    intro front tail hsplit
    have hsplit' : ParamChain.exponentialSteps cs (p k) =
        ParamChain.exponentialSteps front (p k) ++ ParamChain.exponentialSteps tail (p k) := by
      simp only [ParamChain.exponentialSteps, hsplit, List.map_append]
    apply qPotential_chain_tail (ParamChain.exponentialSteps front (p k)) _ hf (by omega)
    · rw [← hsplit']
      exact hmass
    · rw [← hsplit', hpath]
      exact hbudget
    · rw [← hsplit', hpath]
      exact hcurv
  have H := qBoundedJets_second_exponentialChain_order cs hp hK hTilt hMass hDir hsource hpot hgeom
  rw [exponentialSecondMajorant_logParameters K ps hreg hpos] at H
  have heq : (fun x => deriv (deriv (fun t => vectorIncrementChain
      (ps.map (fun q => q t)) f x)) k) =
      fun x => deriv (deriv (fun t => vectorIncrementChain
        (ParamChain.exponentialSteps cs (p t)) f x)) k := by
    funext x
    apply Filter.EventuallyEq.deriv_eq
    apply Filter.EventuallyEq.deriv
    filter_upwards [pathEnergy_positive_masses_eventually ps hreg hpos] with t ht
    rw [ParamChain.coordinateSteps_apply ps t ht]
  rw [heq]
  exact H

theorem kStageMass_interpolated (α : ℝ → ℝ) (a lam s h x : ℝ) (σ : Fin 6) :
    kStageMass (interpolatedProfile α a lam) s h x σ =
      fun t => (1-lam)*(a/kStageMassDivisor σ)+lam*kStageMass α s h x σ t := by
  funext t
  dsimp only [kStageMass, quadraticGridMass, interpolatedProfile]
  ring

theorem windowVariationEnergy_interpolated (β : ℝ) (α : ℝ → ℝ)
    (a lam s h k : ℝ) (N : ℕ) :
    variationEnergy (windowVariationEnergy k)
        (windowKCurves β (interpolatedProfile α a lam) s h N) =
      variationEnergy (windowVariationEnergy k) (windowKCurves β α s h N) := by
  simp only [variationEnergy,windowKCurves,List.map_flatMap,List.map_map,
    Function.comp_def,windowVariationEnergy]

theorem scalarData_interpolated_window_variation_inputs {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ A a0 h0 : ℝ, 0 < A ∧ 0 < a0 ∧ 0 < h0 ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ k : ℝ, |k| ≤ 1/2 →
      let α := cdf (D.μ : Measure ℝ)
      let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
      variationEnergy (windowVariationEnergy k) ps ≤ A*h ∧
        ∀ p ∈ ps, ContDiffAt ℝ 2 p k ∧ (p k).1 ∈ Icc a0 1 ∧
          |deriv (fun t => (p t).1) k| ≤ 1 ∧
          |deriv (deriv (fun t => (p t).1)) k| ≤ 1 := by
  let α := cdf (D.μ : Measure ℝ)
  obtain ⟨A,hV,hA,hhV,hvariation⟩ := scalarData_window_variation_budget D hl hlu hu
  obtain ⟨a0,hF,ha0,hhF,hfloor⟩ := scalarData_window_mass_floor D hl hu
  obtain ⟨hR,hhR,hregular⟩ := scalarData_interpolated_window_curve_regular D hl hlu hu
  let a1 := α (l/2)/3
  have ha1 : 0 < a1 := div_pos (D.cdf_pos (by positivity)) (by norm_num)
  refine ⟨A,min a0 a1,min hV (min hF (min hR (kStabilityInteriorRadius D.q l u))),
    hA,lt_min ha0 ha1,lt_min hhV (lt_min hhF
      (lt_min hhR (kStabilityInteriorRadius_pos hl hu))),?_⟩
  intro r hr h hh hh0 N hN lam hlam k hk
  dsimp only
  have hhV' := hh0.trans (min_le_left _ _)
  have hhF' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhR' := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hhI := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨he,hd⟩ := hvariation r hr h hh hhV' N hN k hk
  constructor
  · rw [windowVariationEnergy_interpolated]
    exact he
  · intro p hp
    have hpreg := (hregular r hr h hh hhR' N hN lam hlam p hp k hk).1
    obtain ⟨σ,hσ,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨j,hj,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    let p0 : ℝ → ℝ × E := fun t =>
      (kStageMass α (r-h) h ((j:ℝ)/(N:ℝ)) σ t,
        (β*Real.sqrt (h/(N:ℝ))) • kDirectionShape i t)
    have hp0 : p0 ∈ windowKCurves β α (r-h) h N := by
      exact List.mem_flatMap.mpr ⟨σ,hσ,List.mem_flatMap.mpr
        ⟨j,hj,List.mem_map.mpr ⟨i,hi,rfl⟩⟩⟩
    have hm0 := hfloor r hr h hh hhF' N hN p0 hp0 k hk
    have hd0 := hd p0 hp0
    have hs := kStability_time_mem hr hh.le hhI
      (show (0:ℝ) ∈ Icc (0:ℝ) 4 by norm_num)
    have hc1 : 1 ≤ kStageMassDivisor σ := by
      fin_cases σ <;> norm_num [kStageMassDivisor]
    have hc3 : kStageMassDivisor σ ≤ 3 := by
      fin_cases σ <;> norm_num [kStageMassDivisor]
    have hcpos : 0 < kStageMassDivisor σ := by linarith
    have haf : α (r-h)/kStageMassDivisor σ ∈ Icc a1 1 := by
      constructor
      · apply (le_div_iff₀ hcpos).mpr
        calc
          a1*kStageMassDivisor σ ≤ a1*3 :=
            mul_le_mul_of_nonneg_left hc3 ha1.le
          _ = α (l/2) := by dsimp only [a1]; ring
          _ ≤ α (r-h) := α.mono (by linarith [hs.1])
      · exact (div_le_self (cdf_nonneg _ _) hc1).trans (cdf_le_one _ _)
    refine ⟨hpreg,?_,?_,?_⟩
    · change kStageMass (interpolatedProfile α (α (r-h)) lam)
        (r-h) h ((j:ℝ)/(N:ℝ)) σ k ∈ Icc (min a0 a1) 1
      rw [kStageMass_interpolated]
      constructor
      · have hlow0 := (min_le_left a0 a1).trans hm0.1
        have hlow1 := (min_le_right a0 a1).trans haf.1
        nlinarith [mul_nonneg (sub_nonneg.mpr hlam.2) (sub_nonneg.mpr hlow1),
          mul_nonneg hlam.1 (sub_nonneg.mpr hlow0)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hlam.2) (sub_nonneg.mpr haf.2),
          mul_nonneg hlam.1 (sub_nonneg.mpr hm0.2)]
    · change |deriv (kStageMass (interpolatedProfile α (α (r-h)) lam)
        (r-h) h ((j:ℝ)/(N:ℝ)) σ) k| ≤ 1
      rw [kStageMass_interpolated,deriv_const_add,deriv_const_mul_field,
        abs_mul,abs_of_nonneg hlam.1]
      exact (mul_le_mul_of_nonneg_left hd0.1 hlam.1).trans (by simpa using hlam.2)
    · change |deriv (deriv (kStageMass (interpolatedProfile α (α (r-h)) lam)
        (r-h) h ((j:ℝ)/(N:ℝ)) σ)) k| ≤ 1
      rw [kStageMass_interpolated,deriv_const_add',deriv_const_mul_field',
        deriv_const_mul_field,abs_mul,abs_of_nonneg hlam.1]
      exact (mul_le_mul_of_nonneg_left hd0.2 hlam.1).trans (by simpa using hlam.2)

private theorem pathEnergy_chainEnergy_le_variation (ps : List (ℝ → ℝ × E)) (k : ℝ) :
    chainEnergy (ps.map (fun p => p k)) ≤ variationEnergy (windowVariationEnergy k) ps := by
  rw [windowVariationEnergy_sum]
  have h1 : 0 ≤ (ps.map fun p => ‖deriv (fun t => (p t).2) k‖^2).sum :=
    List.sum_nonneg (fun a ha => by
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
      exact sq_nonneg _)
  have h2 : 0 ≤ (ps.map fun p => ‖deriv (deriv (fun t => (p t).2)) k‖^2).sum :=
    List.sum_nonneg (fun a ha => by
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
      exact sq_nonneg _)
  simp only [chainEnergy,List.map_map,Function.comp_def]
  linarith

theorem scalarData_interpolated_window_variations_c6_c4 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ C h0 : ℝ, 0 < C ∧ 0 < h0 ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ k : ℝ, |k| ≤ 1/2 →
      let α := cdf (D.μ : Measure ℝ)
      let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
      ∀ front tail, ps = front++tail →
        QBoundedJets 6 (C*h) (fun x => deriv (fun t => vectorIncrementChain
          (tail.map (fun p => p t)) (massVariationTerminal β α (r-h) h) x) k) ∧
        QBoundedJets 4 (C*h) (fun x => deriv (deriv (fun t => vectorIncrementChain
          (tail.map (fun p => p t)) (massVariationTerminal β α (r-h) h) x)) k) := by
  obtain ⟨A,a0,hV,hA,ha0,hhV,hvariation⟩ :=
    scalarData_interpolated_window_variation_inputs D hl hlu hu
  let B := terminalJetBound D 8
  have hB : 0 ≤ B := terminalJetBound_nonneg D 8
  obtain ⟨K0,hK0,hsource0⟩ := secondVariationJetBound_le_source 3
    (show 0 ≤ B+1 by positivity) (show 0 ≤ a0⁻¹ by positivity)
  let K := K0+|tiltedStabilityCoefficient 6 (B+1)|+
    |massSensitivityJetCoefficient 5 (B+1)|+|directionSensitivityCoefficient 6 (B+1)|+1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKK : K0 ≤ K := by
    dsimp only [K]
    linarith [abs_nonneg (tiltedStabilityCoefficient 6 (B+1)),
      abs_nonneg (massSensitivityJetCoefficient 5 (B+1)),
      abs_nonneg (directionSensitivityCoefficient 6 (B+1))]
  have hTilt : tiltedStabilityCoefficient 6 (B+1) ≤ K := by
    dsimp only [K]
    linarith [le_abs_self (tiltedStabilityCoefficient 6 (B+1)),
      abs_nonneg (massSensitivityJetCoefficient 5 (B+1)),
      abs_nonneg (directionSensitivityCoefficient 6 (B+1))]
  have hMass : massSensitivityJetCoefficient 5 (B+1) ≤ K := by
    dsimp only [K]
    linarith [le_abs_self (massSensitivityJetCoefficient 5 (B+1)),
      abs_nonneg (tiltedStabilityCoefficient 6 (B+1)),
      abs_nonneg (directionSensitivityCoefficient 6 (B+1))]
  have hDir : directionSensitivityCoefficient 6 (B+1) ≤ K := by
    dsimp only [K]
    linarith [le_abs_self (directionSensitivityCoefficient 6 (B+1)),
      abs_nonneg (tiltedStabilityCoefficient 6 (B+1)),
      abs_nonneg (massSensitivityJetCoefficient 5 (B+1))]
  have hsource : ∀ A H m dm ddm : ℝ, 0 ≤ A → 0 ≤ H → 0 < m → m⁻¹ ≤ a0⁻¹ →
      ∀ v w b : E, secondVariationJetBound 3 (B+1) A H m dm ddm v w b ≤
        (1+K*‖v‖^2)*H+K*secondVariationSource A dm ddm v w b := by
    intro A H m dm ddm hA hH hm hinv v w b
    apply (hsource0 A H m dm ddm hA hH hm hinv v w b).trans
    have hs : 0 ≤ secondVariationSource A dm ddm v w b := by
      dsimp only [secondVariationSource]; positivity
    gcongr
  have hS : 0 ≤ stepStabilityCoefficient 8 (B+1) :=
    stepStabilityCoefficient_nonneg 8 (by positivity)
  let L := stepStabilityCoefficient 8 (B+1)+1+2*(B+1)+8*K+1
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨24*K*A,min hV (min (kStabilityInteriorRadius D.q l u) (A*L+1)⁻¹),
    by positivity,lt_min hhV (lt_min (kStabilityInteriorRadius_pos hl hu)
      (inv_pos.mpr (by positivity))),?_⟩
  intro r hr h hh hh0 N hN lam hlam k hk
  dsimp only
  let α := cdf (D.μ : Measure ℝ)
  let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
  have hhV' := hh0.trans (min_le_left _ _)
  have hhI := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhinv := hh0.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨henergy,hinputs⟩ := hvariation r hr h hh hhV' N hN lam hlam k hk
  have he : 0 ≤ variationEnergy (windowVariationEnergy k) ps :=
    variationEnergy_nonneg (fun p _ => windowVariationEnergy_nonneg k p)
  have hLE : L*variationEnergy (windowVariationEnergy k) ps ≤ 1 := by
    have hinv : h*(A*L+1) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < A*L+1)).mp (by simpa only [one_div] using hhinv)
    have H := mul_le_mul_of_nonneg_left henergy hL.le
    nlinarith
  have hbudget : (stepStabilityCoefficient 8 (B+1)+1)*
      chainEnergy (ps.map (fun p => p k)) ≤ 1 := by
    apply le_trans (mul_le_mul_of_nonneg_left (pathEnergy_chainEnergy_le_variation ps k)
      (by positivity))
    exact (mul_le_mul_of_nonneg_right
      (show stepStabilityCoefficient 8 (B+1)+1 ≤ L by dsimp only [L]; linarith) he).trans hLE
  have hcurv : (B+1)*chainEnergy (ps.map (fun p => p k)) ≤ 1/2 := by
    have H := mul_le_mul_of_nonneg_right (show 2*(B+1) ≤ L by dsimp only [L]; linarith) he
    have H' := mul_le_mul_of_nonneg_left (pathEnergy_chainEnergy_le_variation ps k)
      (show 0 ≤ B+1 by positivity)
    nlinarith
  have hsmall : 8*K*variationEnergy (windowVariationEnergy k) ps ≤ 1 :=
    (mul_le_mul_of_nonneg_right (show 8*K ≤ L by dsimp only [L]; linarith) he).trans hLE
  have he1 : variationEnergy (windowVariationEnergy k) ps ≤ 1 := by
    have H := mul_le_mul_of_nonneg_right (show 1 ≤ L by dsimp only [L]; linarith) he
    nlinarith
  have hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k := fun p hp => (hinputs p hp).1
  have hpos : ∀ p ∈ ps, 0 < (p k).1 :=
    fun p hp => ha0.trans_le (hinputs p hp).2.1.1
  have hgeometry : ∀ p ∈ ps, (p k).1 ≤ 1 ∧ ‖(p k).2‖ ≤ 1 ∧
      (B+1)*‖(p k).2‖^2 ≤ 1/2 ∧ ((p k).1)⁻¹ ≤ a0⁻¹ := by
    intro p hp
    have hsingle : ‖(p k).2‖^2 ≤ chainEnergy (ps.map (fun p => p k)) := by
      simp only [chainEnergy,List.map_map,Function.comp_def]
      exact List.single_le_sum (fun a ha => by
        obtain ⟨q,_,rfl⟩ := List.mem_map.mp ha
        exact sq_nonneg _) _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
    have hv2 := hsingle.trans (pathEnergy_chainEnergy_le_variation ps k)
    refine ⟨(hinputs p hp).2.1.2,?_,?_,?_⟩
    · nlinarith [norm_nonneg ((p k).2)]
    · exact (mul_le_mul_of_nonneg_left hsingle (by positivity)).trans hcurv
    · simpa only [one_div] using one_div_le_one_div_of_le ha0 (hinputs p hp).2.1.1
  have htime := kStability_time_mem hr hh.le hhI
    (show (4:ℝ) ∈ Icc (0:ℝ) 4 by norm_num)
  have hf : QPotential 8 B (massVariationTerminal β α (r-h) h) :=
    scalarData_massVariationTerminal_qPotential D 8 (by
      constructor <;> linarith [htime.1,htime.2,D.q_mem.2])
  intro front tail hsplit
  change ps = front++tail at hsplit
  have hsub : ∀ p ∈ tail, p ∈ ps :=
    fun p hp => hsplit.symm ▸ List.mem_append_right front hp
  have heTail : variationEnergy (windowVariationEnergy k) tail ≤
      variationEnergy (windowVariationEnergy k) ps := by
    rw [hsplit,variationEnergy_append]
    exact le_add_of_nonneg_left (variationEnergy_nonneg
      (fun p _ => windowVariationEnergy_nonneg k p))
  have hcTail : chainEnergy (tail.map (fun p => p k)) ≤
      chainEnergy (ps.map (fun p => p k)) := by
    rw [hsplit,List.map_append,chainEnergy_append]
    exact le_add_of_nonneg_left (chainEnergy_nonneg _)
  have hmTail : ∀ p ∈ tail, |deriv (fun t => (p t).1) k| ≤ 1 ∧
      |deriv (deriv (fun t => (p t).1)) k| ≤ 1 :=
    fun p hp => (hinputs p (hsub p hp)).2.2
  have hsTail : 8*K*variationEnergy (windowVariationEnergy k) tail ≤ 1 :=
    (mul_le_mul_of_nonneg_left heTail (by positivity)).trans hsmall
  constructor
  · apply (qBoundedJets_first_curveChain_tail (n := 5) ps hf hreg hpos hK.le
      hTilt hMass hDir (fun p hp =>
        ⟨(hgeometry p hp).1,(hgeometry p hp).2.1,(hgeometry p hp).2.2.1⟩)
      hbudget hcurv front tail hsplit).mono
    calc
      _ ≤ 8*K*variationEnergy (windowVariationEnergy k) tail :=
        curveFirstMajorant_le_variation tail k hK.le hmTail hsTail
      _ ≤ 24*K*A*h := by
        have H := mul_le_mul_of_nonneg_left (heTail.trans henergy)
          (show 0 ≤ 8*K by positivity)
        nlinarith [mul_nonneg (show 0 ≤ K*A by positivity) hh.le]
  · apply (qBoundedJets_second_curveChain_order (n := 3) tail hf
      (fun p hp => hreg p (hsub p hp)) (fun p hp => hpos p (hsub p hp)) hK.le
      hTilt hMass hDir hsource (fun p hp => hgeometry p (hsub p hp))
      ((mul_le_mul_of_nonneg_left hcTail (by positivity)).trans hbudget)
      ((mul_le_mul_of_nonneg_left hcTail (by positivity)).trans hcurv)).mono
    calc
      _ ≤ 24*K*variationEnergy (windowVariationEnergy k) tail :=
        curveSecondMajorant_le_variation tail k hK.le hmTail hsTail
      _ ≤ 24*K*A*h := by
        have H := mul_le_mul_of_nonneg_left (heTail.trans henergy)
          (show 0 ≤ 24*K by positivity)
        nlinarith

theorem scalarData_orderedInnerVariations_c6_c4 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ C h0 : ℝ, 0 < C ∧ 0 < h0 ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ 1/2 →
      let α := cdf (D.μ : Measure ℝ)
      QBoundedJets 6 (C*h)
          (orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j 1 k) ∧
        QBoundedJets 4 (C*h)
          (orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j 2 k) := by
  by_cases hlu : l ≤ u
  · obtain ⟨C,h0,hC,hh0,hvariations⟩ :=
      scalarData_interpolated_window_variations_c6_c4 D hl hlu hu
    refine ⟨C,h0,hC,hh0,?_⟩
    intro r hr h hh hhh0 N hN lam hlam j k hk
    let α := cdf (D.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    have H := hvariations r hr h hh hhh0 N hN lam hlam k hk
      (ps.take (j.val+1)) (ps.drop (j.val+1)) (List.take_append_drop _ _).symm
    have he (t : ℝ) : (ps.drop (j.val+1)).map (fun p => p t) =
        (massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N) lam).drop (j.val+1) := by
      rw [List.map_drop]
      dsimp only [ps]
      rw [windowKCurves_apply β _ (r-h) h t N hh.le,massPath_window_eq]
    dsimp only at H ⊢
    simp_rw [he] at H
    change QBoundedJets 6 (C*h) (fun x => iteratedDeriv 1 (fun t =>
        orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t x) k) ∧
      QBoundedJets 4 (C*h) (fun x => iteratedDeriv 2 (fun t =>
        orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t x) k)
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    exact H
  · refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

theorem scalarData_window_secondTerminalSource_remainder_c4 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ K h0 kap : ℝ, 0 ≤ K ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ᶠ N : ℕ in atTop,
        ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap → ∀ x : E,
          let α := cdf (D.μ : Measure ℝ)
          let jj := windowEntryIndex β α (α (r-h)) (1/2) (r-h) h k N j
          let m := windowEntryMass β α (α (r-h)) (1/2) (r-h) h k N lam jj
          let v := ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get jj).2.2
          let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
          let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
          |secondVariationStep m v F (G 1) (G 2) 0 0 0 0 x -
            terminalSecondGenerator m v F (G 1) (G 2) x| ≤ K*h^3/(N:ℝ)^2 := by
  let α := cdf (D.μ : Measure ℝ)
  obtain ⟨B,hK0,hBpos,hhK,hvariations⟩ := scalarData_orderedInnerVariations_c6_c4 D hl hu
  have hB : 0 ≤ B := hBpos.le
  let kapK : ℝ := 1/2
  have hkapK : 0 < kapK := by norm_num [kapK]
  obtain ⟨A,a0,S,hA0,kapA,hA,ha0,hS,hhA,hkapA,hentropy⟩ :=
    scalarData_uniformWindowEntropyInputs D hl hu
  let P := pathExpansionConstant A
  let Q := 18*P+(1+A)^4
  let K := (B*P+B^2*Q)*S^2
  have hP : 0 ≤ P := pathExpansionConstant_nonneg hA
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hKnonneg : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K,min hK0 (min hA0 1),min kapK kapA,hKnonneg,
    lt_min hhK (lt_min hhA (by norm_num)),lt_min hkapK hkapA,?_⟩
  intro r hr h hh hh0
  have hhK' : h ≤ hK0 := hh0.trans (min_le_left _ _)
  have hhA' : h ≤ hA0 := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh1 : h ≤ 1 := hh0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlim : Tendsto (fun N : ℕ => S*h/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))] with N hN hsmall
  intro lam hlam j k hk x
  dsimp only
  let jj := windowEntryIndex β α (α (r-h)) (1/2) (r-h) h k N j
  let m := windowEntryMass β α (α (r-h)) (1/2) (r-h) h k N lam jj
  let v := ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get jj).2.2
  let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
  let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
  obtain ⟨_,hentropyN⟩ := hentropy r hr h hh hhA' k
    (hk.trans (min_le_right _ _)) N hN
  obtain ⟨hinner,hentry⟩ := hentropyN lam hlam
  have hF : QPotential 4 A F := by
    simpa only [F,orderedInnerChain,massPath,List.map_drop,jj,windowEntryIndex] using
      (hinner jj.val jj.isLt).of_le (by norm_num : 4 ≤ 10)
  have hm : m ∈ Icc (0:ℝ) 1 :=
    ⟨ha0.le.trans (hentry jj).1.1,(hentry jj).1.2⟩
  have hdir : ‖v‖^2 ≤ S*h/(N:ℝ) := (hentry jj).2
  have hv : ‖v‖ ≤ 1 := by nlinarith [norm_nonneg v]
  have hv4 : ‖v‖^4 ≤ (S*h/(N:ℝ))^2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hdir 2
  obtain ⟨hG1,hG2⟩ := hvariations r hr h hh hhK' N hN lam hlam j k
    (hk.trans (min_le_left _ _))
  have H := abs_secondVariationStep_terminal_remainder_le hF
    (hG1.of_le (by norm_num : 4 ≤ 6)) hG2 hm v x hv
  change |secondVariationStep m v F (G 1) (G 2) 0 0 0 0 x -
    terminalSecondGenerator m v F (G 1) (G 2) x| ≤ K*h^3/(N:ℝ)^2
  calc
    _ ≤ ((B*h)*P+(B*h)^2*Q)*‖v‖^4 := H
    _ ≤ ((B*h)*P+(B*h)^2*Q)*(S*h/(N:ℝ))^2 :=
      mul_le_mul_of_nonneg_left hv4 (by positivity)
    _ = ((B*P)*S^2*h^3+(B^2*Q)*S^2*h^4)/(N:ℝ)^2 := by ring
    _ ≤ ((B*P)*S^2*h^3+(B^2*Q)*S^2*h^3)/(N:ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ B^2*Q*S^2)
      calc
        h^4 = h^3*h := by ring
        _ ≤ h^3 := mul_le_of_le_one_right (pow_nonneg hh.le 3) hh1
    _ = _ := by dsimp only [K]; ring

end SKBarriers2.Corner
