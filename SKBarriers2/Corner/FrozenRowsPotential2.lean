module

public import SKBarriers2.Analysis.ParamStep4

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

namespace SKBarriers2.Corner
open StepCalculus

local notation "E" => (Fin 3 → ℝ)

section TranslatedTerminal

theorem second_spatial_curve {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {x : ℝ → E} {k : ℝ} (hx : ContDiffAt ℝ 2 x k) (y : E) :
    deriv (deriv (fun t => f (y + x t))) k =
      fderiv ℝ (fderiv ℝ f) (y + x k) (deriv x k) (deriv x k) +
        fderiv ℝ f (y + x k) (deriv (deriv x) k) := by
  have hd := (hx.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hx.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have heq : deriv (fun t => f (y + x t)) =ᶠ[𝓝 k]
      fun t => fderiv ℝ f (y + x t) (deriv x t) := by
    filter_upwards [hx.eventually (by norm_num)] with t ht
    exact ((hf.differentiable (by norm_num) (y + x t)).hasFDerivAt.comp_hasDerivAt t
      (((ht.differentiableAt (by norm_num)).hasDerivAt).const_add y)).deriv
  have hD := ((hf.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) (y + x k)).hasFDerivAt.comp_hasDerivAt k (hd.const_add y)
  rw [heq.deriv_eq]
  exact (hD.clm_apply hdd).deriv

theorem qBoundedJets_first_spatial_curve {n : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential (n + 1) B f) {x : ℝ → E} {k : ℝ}
    (hx : DifferentiableAt ℝ x k) :
    QBoundedJets n (B * ‖deriv x k‖)
      (fun y => deriv (fun t => f (y + x t)) k) := by
  have heq : (fun y => deriv (fun t => f (y + x t)) k) =
      fun y => fderiv ℝ f (y + x k) (deriv x k) := by
    funext y
    exact ((hf.smooth.differentiable (by norm_num) (y + x k)).hasFDerivAt.comp_hasDerivAt k
      (hx.hasDerivAt.const_add y)).deriv
  rw [heq]
  exact (hf.derivativeJets.apply_const (deriv x k)).translate (x k)

theorem qBoundedJets_second_spatial_curve {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) {x : ℝ → E} {k : ℝ}
    (hx : ContDiffAt ℝ 2 x k) :
    QBoundedJets 1 (B * (‖deriv x k‖ ^ 2 + ‖deriv (deriv x) k‖))
      (fun y => deriv (deriv (fun t => f (y + x t))) k) := by
  have heq : (fun y => deriv (deriv (fun t => f (y + x t))) k) = fun y =>
      fderiv ℝ (fderiv ℝ f) (y + x k) (deriv x k) (deriv x k) +
        fderiv ℝ f (y + x k) (deriv (deriv x) k) :=
    funext (second_spatial_curve (hf.smooth.of_le (by norm_num)) hx)
  rw [heq]
  have hH := (((hf.derivativeJets.derivativeJets.apply_const (deriv x k)).apply_const
    (deriv x k)).translate (x k)).add
      (((hf.derivativeJets.of_le (by norm_num : 1 ≤ 2)).apply_const
        (deriv (deriv x) k)).translate (x k))
  convert hH using 1
  ring

end TranslatedTerminal

section MovingTerminal

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def movingFirstMajorant (A K : ℝ) (q u : P) :
    List ((P →L[ℝ] ℝ) × (P →L[ℝ] E)) → ℝ
  | [] => A
  | c :: ps => (1 + K * ‖c.2 q‖ ^ 2) * movingFirstMajorant A K q u ps +
      K * (‖c.2 q‖ * ‖c.2 u‖ + ‖c.2 q‖ ^ 2 * |Real.exp (c.1 q) * c.1 u|)

theorem movingFirstMajorant_nonneg {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (q u : P) (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) :
    0 ≤ movingFirstMajorant A K q u ps := by
  induction ps with
  | nil => exact hA
  | cons c ps ih => dsimp only [movingFirstMajorant]; positivity

theorem qBoundedJets_first_moving_exponentialChain
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) {F : P × E → ℝ}
    (hF : ParamRegular F) {p : ℝ → P} {u : P} {k : ℝ}
    (hp : HasDerivAt p u k) {n : ℕ} {B A K : ℝ}
    (hbase : QBoundedJets (n + 1) A (fun x => deriv (fun t => F (p t,x)) k))
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient (n + 1) B ≤ K)
    (hMass : massSensitivityJetCoefficient n B ≤ K)
    (hDir : directionSensitivityCoefficient (n + 1) B ≤ K)
    (hpotential : ∀ front tail, ps = front ++ tail →
      QPotential (n + 3) B (fun x => ParamChain.exponentialChain tail F (p k,x)))
    (hgeometry : ∀ c ∈ ps, Real.exp (c.1 (p k)) ≤ 1 ∧ ‖c.2 (p k)‖ ≤ 1 ∧
      B * ‖c.2 (p k)‖ ^ 2 ≤ 1 / 2) :
    QBoundedJets (n + 1) (movingFirstMajorant A K (p k) u ps)
      (fun x => deriv (fun t => ParamChain.exponentialChain ps F (p t,x)) k) := by
  induction ps with
  | nil => exact hbase
  | cons c ps ih =>
    have hpotTail : ∀ front tail, ps = front ++ tail →
        QPotential (n + 3) B (fun x => ParamChain.exponentialChain tail F (p k,x)) := by
      intro front tail hsplit
      apply hpotential (c :: front) tail
      simpa only [List.cons_append, List.cons.injEq, true_and] using hsplit
    have hgeoTail : ∀ d ∈ ps, Real.exp (d.1 (p k)) ≤ 1 ∧ ‖d.2 (p k)‖ ≤ 1 ∧
        B * ‖d.2 (p k)‖ ^ 2 ≤ 1 / 2 :=
      fun d hd => hgeometry d (List.mem_cons_of_mem c hd)
    have hinner := ih hpotTail hgeoTail
    let G := ParamChain.exponentialChain ps F
    have hG : ParamRegular G := ParamChain.regular_exponentialChain ps hF
    have hid : (fun y => fderiv ℝ G (p k,y) (u,0)) =
        fun y => deriv (fun t => G (p t,y)) k := by
      funext y
      exact (((hG.1.differentiable (by norm_num) (p k,y)).hasFDerivAt.comp_hasDerivAt k
        (hp.prodMk (hasDerivAt_const k y))).deriv).symm
    have hfirst : QBoundedJets (n + 1) (movingFirstMajorant A K (p k) u ps)
        (fun y => fderiv ℝ G (p k,y) (u,0)) := by
      rw [hid]
      exact hinner
    have hgeo := hgeometry c (List.mem_cons_self ..)
    have hstep := qBoundedJets_deriv_exponential_movingStep hG c.1 c.2 hp
      (hpotential [c] ps rfl) hfirst hgeo.1 hgeo.2.1 hgeo.2.2
    apply hstep.mono
    dsimp only [movingFirstMajorant]
    calc
      _ ≤ movingFirstMajorant A K (p k) u ps +
          K * movingFirstMajorant A K (p k) u ps * ‖c.2 (p k)‖ ^ 2 +
          K * ‖c.2 (p k)‖ ^ 2 * |Real.exp (c.1 (p k)) * c.1 u| +
          K * ‖c.2 (p k)‖ * ‖c.2 u‖ := by
        gcongr
        exact movingFirstMajorant_nonneg hbase.nonneg hK _ _ _
      _ = _ := by ring

def movingSecondMajorant (A H K : ℝ) (q u a : P) :
    List ((P →L[ℝ] ℝ) × (P →L[ℝ] E)) → ℝ
  | [] => H
  | c :: ps => (1 + K * ‖c.2 q‖ ^ 2) * movingSecondMajorant A H K q u a ps +
      K * secondVariationSource (movingFirstMajorant A K q u ps)
        (Real.exp (c.1 q) * c.1 u)
        (Real.exp (c.1 q) * ((c.1 u) ^ 2 + c.1 a)) (c.2 q) (c.2 u) (c.2 a)

theorem movingSecondMajorant_nonneg {A H K : ℝ}
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hK : 0 ≤ K) (q u a : P)
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) :
    0 ≤ movingSecondMajorant A H K q u a ps := by
  induction ps with
  | nil => exact hH
  | cons c ps ih =>
    have ha := movingFirstMajorant_nonneg hA hK q u ps
    dsimp only [movingSecondMajorant, secondVariationSource]
    positivity

theorem qBoundedJets_second_moving_exponentialChain
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) {F : P × E → ℝ}
    (hF : ParamRegular F) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) {B R A H K : ℝ}
    (hbase₁ : QBoundedJets 3 A (fun x => deriv (fun t => F (p t,x)) k))
    (hbase₂ : QBoundedJets 1 H (fun x => deriv (deriv (fun t => F (p t,x))) k))
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient 3 B ≤ K)
    (hMass : massSensitivityJetCoefficient 2 B ≤ K)
    (hDir : directionSensitivityCoefficient 3 B ≤ K)
    (hsource : ∀ A H m dm ddm : ℝ, 0 ≤ A → 0 ≤ H → 0 < m → m⁻¹ ≤ R →
      ∀ v w b : E, secondVariationBound B A H m dm ddm v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * secondVariationSource A dm ddm v w b)
    (hpotential : ∀ front tail, ps = front ++ tail →
      QPotential 5 B (fun x => ParamChain.exponentialChain tail F (p k,x)))
    (hgeometry : ∀ c ∈ ps, Real.exp (c.1 (p k)) ≤ 1 ∧ ‖c.2 (p k)‖ ≤ 1 ∧
      B * ‖c.2 (p k)‖ ^ 2 ≤ 1 / 2 ∧ (Real.exp (c.1 (p k)))⁻¹ ≤ R) :
    QBoundedJets 1
      (movingSecondMajorant A H K (p k) (deriv p k) (deriv (deriv p) k) ps)
      (fun x => deriv (deriv (fun t => ParamChain.exponentialChain ps F (p t,x))) k) := by
  have hp1 := (hp.differentiableAt (by norm_num)).hasDerivAt
  induction ps with
  | nil => exact hbase₂
  | cons c ps ih =>
    have hpotTail : ∀ front tail, ps = front ++ tail →
        QPotential 5 B (fun x => ParamChain.exponentialChain tail F (p k,x)) := by
      intro front tail hsplit
      apply hpotential (c :: front) tail
      simpa only [List.cons_append, List.cons.injEq, true_and] using hsplit
    have hgeoTail : ∀ d ∈ ps, Real.exp (d.1 (p k)) ≤ 1 ∧ ‖d.2 (p k)‖ ≤ 1 ∧
        B * ‖d.2 (p k)‖ ^ 2 ≤ 1 / 2 ∧ (Real.exp (d.1 (p k)))⁻¹ ≤ R :=
      fun d hd => hgeometry d (List.mem_cons_of_mem c hd)
    have hinner := ih hpotTail hgeoTail
    have hfirst := qBoundedJets_first_moving_exponentialChain ps hF hp1 hbase₁ hK
      hTilt hMass hDir hpotTail
      (fun d hd => ⟨(hgeoTail d hd).1, (hgeoTail d hd).2.1, (hgeoTail d hd).2.2.1⟩)
    let G := ParamChain.exponentialChain ps F
    have hG : ParamRegular G := ParamChain.regular_exponentialChain ps hF
    have hid₁ : (fun y => fderiv ℝ G (p k,y) (deriv p k,0)) =
        fun y => deriv (fun t => G (p t,y)) k := by
      funext y
      exact (((hG.1.differentiable (by norm_num) (p k,y)).hasFDerivAt.comp_hasDerivAt k
        (hp1.prodMk (hasDerivAt_const k y))).deriv).symm
    have hid₂ : (fun y =>
        fderiv ℝ (fderiv ℝ G) (p k,y) (deriv p k,0) (deriv p k,0) +
          fderiv ℝ G (p k,y) (deriv (deriv p) k,0)) =
        fun y => deriv (deriv (fun t => G (p t,y))) k := by
      funext y
      exact (ParamChain.second_parameter_curve hG.1 hp y).symm
    have hg : QBoundedJets 3 (movingFirstMajorant A K (p k) (deriv p k) ps)
        (fun y => fderiv ℝ G (p k,y) (deriv p k,0)) := by rw [hid₁]; exact hfirst
    have hh : QBoundedJets 1
        (movingSecondMajorant A H K (p k) (deriv p k) (deriv (deriv p) k) ps)
        (fun y => fderiv ℝ (fderiv ℝ G) (p k,y) (deriv p k,0) (deriv p k,0) +
          fderiv ℝ G (p k,y) (deriv (deriv p) k,0)) := by rw [hid₂]; exact hinner
    have hgeo := hgeometry c (List.mem_cons_self ..)
    have hstep := qBoundedJets_second_deriv_exponential_movingStep hG c.1 c.2 hp
      ((hpotential [c] ps rfl).of_le (by norm_num : 3 ≤ 5)) hg hh
      hgeo.1 hgeo.2.1 hgeo.2.2.1
    apply hstep.mono
    exact hsource _ _ _ _ _ hg.nonneg hh.nonneg (Real.exp_pos _) hgeo.2.2.2 _ _ _

end MovingTerminal

end SKBarriers2.Corner
