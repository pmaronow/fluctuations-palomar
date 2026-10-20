module

public import SKBarriers2.Corner.KStabilityFinal

@[expose] public section

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
open scoped Topology

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

def curveSecondMajorant (K k : ℝ) : List (ℝ → ℝ × E) → ℝ
  | [] => 0
  | p :: ps => (1 + K * ‖(p k).2‖ ^ 2) * curveSecondMajorant K k ps +
      K * windowSecondVariationSource k p (curveFirstMajorant K k ps)

theorem curveSecondMajorant_nonneg {K : ℝ} (hK : 0 ≤ K) (k : ℝ)
    (ps : List (ℝ → ℝ × E)) : 0 ≤ curveSecondMajorant K k ps := by
  induction ps with
  | nil => exact le_rfl
  | cons p ps ih =>
    have ha := curveFirstMajorant_nonneg hK k ps
    dsimp only [curveSecondMajorant, windowSecondVariationSource]
    positivity

theorem curveSecondMajorant_le_variation (ps : List (ℝ → ℝ × E)) (k : ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hm : ∀ p ∈ ps, |deriv (fun t => (p t).1) k| ≤ 1 ∧
      |deriv (deriv (fun t => (p t).1)) k| ≤ 1)
    (hsmall : 8 * K * variationEnergy (windowVariationEnergy k) ps ≤ 1) :
    curveSecondMajorant K k ps ≤
      24 * K * variationEnergy (windowVariationEnergy k) ps := by
  exact (window_two_level_recursion_le ps k hK
    (curveFirstMajorant K k) (curveSecondMajorant K k)
    (curveFirstMajorant_nonneg hK k) (curveSecondMajorant_nonneg hK k)
    le_rfl le_rfl hm (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl) hsmall).2

private theorem second_exp_linear_parameter
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) (M : P →L[ℝ] ℝ) :
    deriv (deriv (fun t => Real.exp (M (p t)))) k =
      Real.exp (M (p k)) * ((M (deriv p k)) ^ 2 + M (deriv (deriv p) k)) := by
  have hd := (hp.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hp.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have heq : deriv (fun t => Real.exp (M (p t))) =ᶠ[𝓝 k]
      fun t => Real.exp (M (p t)) * M (deriv p t) := by
    filter_upwards [hp.eventually (by norm_num)] with t ht
    exact ((M.hasFDerivAt.comp_hasDerivAt t
      ((ht.differentiableAt (by norm_num)).hasDerivAt)).exp).deriv
  rw [heq.deriv_eq]
  have H := (((M.hasFDerivAt.comp_hasDerivAt k hd).exp).mul
    (M.hasFDerivAt.comp_hasDerivAt k hdd)).deriv
  have H' : deriv (fun t => Real.exp (M (p t)) * M (deriv p t)) k =
      Real.exp (M (p k)) * M (deriv p k) * M (deriv p k) +
        Real.exp (M (p k)) * M (deriv (deriv p) k) := by
    convert! H using 1
  rw [H']
  ring

private abbrev VariationJet := E × E × E × ℝ × ℝ

private def firstJetMajorant (K : ℝ) : List VariationJet → ℝ
  | [] => 0
  | j :: js => (1 + K * ‖j.1‖ ^ 2) * firstJetMajorant K js +
      K * (‖j.1‖ * ‖j.2.1‖ + ‖j.1‖ ^ 2 * |j.2.2.2.1|)

private def secondJetMajorant (K : ℝ) : List VariationJet → ℝ
  | [] => 0
  | j :: js => (1 + K * ‖j.1‖ ^ 2) * secondJetMajorant K js +
      K * secondVariationSource (firstJetMajorant K js)
        j.2.2.2.1 j.2.2.2.2 j.1 j.2.1 j.2.2.1

private def curveJets (k : ℝ) (ps : List (ℝ → ℝ × E)) : List VariationJet :=
  ps.map fun p => ((p k).2, deriv (fun t => (p t).2) k,
    deriv (deriv (fun t => (p t).2)) k, deriv (fun t => (p t).1) k,
    deriv (deriv (fun t => (p t).1)) k)

private theorem curveMajorants_eq_jets (K k : ℝ) (ps : List (ℝ → ℝ × E)) :
    curveFirstMajorant K k ps = firstJetMajorant K (curveJets k ps) ∧
    curveSecondMajorant K k ps = secondJetMajorant K (curveJets k ps) := by
  induction ps with
  | nil => exact ⟨rfl, rfl⟩
  | cons p ps ih =>
    dsimp only [curveJets] at ih
    simp only [curveFirstMajorant, curveSecondMajorant, curveJets, List.map_cons,
      firstJetMajorant, secondJetMajorant, ← ih.1, ← ih.2,
      windowSecondVariationSource_eq]
    constructor <;> first | rfl | trivial

private def exponentialJets {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (q u a : P) (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) : List VariationJet :=
  ps.map fun c => (c.2 q, c.2 u, c.2 a,
    Real.exp (c.1 q) * c.1 u, Real.exp (c.1 q) * ((c.1 u) ^ 2 + c.1 a))

private theorem exponentialMajorants_eq_jets
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (K : ℝ) (q u a : P) (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) :
    firstVariationMajorant K q u ps = firstJetMajorant K (exponentialJets q u a ps) ∧
    exponentialSecondMajorant K q u a ps = secondJetMajorant K (exponentialJets q u a ps) := by
  induction ps with
  | nil => exact ⟨rfl, rfl⟩
  | cons c ps ih =>
    dsimp only [exponentialJets] at ih
    simp only [firstVariationMajorant, exponentialSecondMajorant, exponentialJets,
      List.map_cons, firstJetMajorant, secondJetMajorant, ← ih.1, ← ih.2]
    constructor <;> first | rfl | trivial

private theorem positive_masses_eventually (ps : List (ℝ → ℝ × E)) {k : ℝ}
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hpos : ∀ p ∈ ps, 0 < (p k).1) :
    ∀ᶠ t in 𝓝 k, ∀ p ∈ ps, 0 < (p t).1 := by
  have hget : ∀ᶠ t in 𝓝 k, ∀ i : Fin ps.length, 0 < (ps.get i t).1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hreg _ (List.get_mem ps i)).fst.continuousAt.eventually
      (Ioi_mem_nhds (hpos _ (List.get_mem ps i)))
  filter_upwards [hget] with t ht p hp
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
  exact ht i

private theorem exponentialJets_logParameters (ps : List (ℝ → ℝ × E)) {k : ℝ}
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hpos : ∀ p ∈ ps, 0 < (p k).1) :
    exponentialJets (ParamChain.logParameters ps k) (deriv (ParamChain.logParameters ps) k)
      (deriv (deriv (ParamChain.logParameters ps)) k) (ParamChain.coordinateSteps ps.length) =
        curveJets k ps := by
  let p := ParamChain.logParameters ps
  have hp : ContDiffAt ℝ 2 p k := ParamChain.logParameters_contDiffAt ps hreg hpos
  have hd : DifferentiableAt ℝ p k := hp.differentiableAt (by norm_num)
  rw [exponentialJets, ParamChain.coordinateSteps, List.map_ofFn]
  have hcoords (i : Fin ps.length) :
      let M := (ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.proj i)
      let V := (ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.proj i)
      (V (p k), V (deriv p k), V (deriv (deriv p) k),
        Real.exp (M (p k)) * M (deriv p k),
        Real.exp (M (p k)) * ((M (deriv p k)) ^ 2 + M (deriv (deriv p) k))) =
      ((ps.get i k).2, deriv (fun t => (ps.get i t).2) k,
        deriv (deriv (fun t => (ps.get i t).2)) k,
        deriv (fun t => (ps.get i t).1) k,
        deriv (deriv (fun t => (ps.get i t).1)) k) := by
    dsimp only
    let M : ParamChain.Coordinates ps.length E →L[ℝ] ℝ :=
      (ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.proj i)
    let V : ParamChain.Coordinates ps.length E →L[ℝ] E :=
      (ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.proj i)
    have hv : (fun t => V (p t)) = fun t => (ps.get i t).2 := rfl
    have hm : (fun t => Real.exp (M (p t))) =ᶠ[𝓝 k] fun t => (ps.get i t).1 := by
      filter_upwards [positive_masses_eventually ps hreg hpos] with t ht
      exact Real.exp_log (ht _ (List.get_mem ps i))
    have h1 := ((M.hasFDerivAt.comp_hasDerivAt k hd.hasDerivAt).exp).deriv
    have h2 := second_exp_linear_parameter hp M
    change deriv (fun t => Real.exp (M (p t))) k =
      Real.exp (M (p k)) * M (deriv p k) at h1
    rw [hm.deriv_eq] at h1
    rw [hm.deriv.deriv_eq] at h2
    have hv1 : deriv (fun t => V (p t)) k = V (deriv p k) :=
      (V.hasFDerivAt.comp_hasDerivAt k hd.hasDerivAt).deriv
    have hv2 : deriv (deriv (fun t => V (p t))) k = V (deriv (deriv p) k) := by
      have heq : deriv (fun t => V (p t)) =ᶠ[𝓝 k] fun t => V (deriv p t) := by
        filter_upwards [hp.eventually (by norm_num)] with t ht
        exact (V.hasFDerivAt.comp_hasDerivAt t
          ((ht.differentiableAt (by norm_num)).hasDerivAt)).deriv
      rw [heq.deriv_eq]
      exact (V.hasFDerivAt.comp_hasDerivAt k
        (((hp.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt)).deriv
    rw [← h1, ← h2, ← hv1, ← hv2]
    rfl
  trans List.ofFn (fun i : Fin ps.length =>
    ((ps.get i k).2, deriv (fun t => (ps.get i t).2) k,
      deriv (deriv (fun t => (ps.get i t).2)) k, deriv (fun t => (ps.get i t).1) k,
      deriv (deriv (fun t => (ps.get i t).1)) k))
  · apply congrArg List.ofFn
    funext i
    exact hcoords i
  · simpa only [curveJets, List.ofFn_get, Function.comp_def] using
      (List.map_ofFn (f := ps.get) (g := fun p =>
        ((p k).2, deriv (fun t => (p t).2) k, deriv (deriv (fun t => (p t).2)) k,
          deriv (fun t => (p t).1) k, deriv (deriv (fun t => (p t).1)) k))).symm

theorem exponentialSecondMajorant_logParameters (K : ℝ) (ps : List (ℝ → ℝ × E))
    {k : ℝ} (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k)
    (hpos : ∀ p ∈ ps, 0 < (p k).1) :
    exponentialSecondMajorant K (ParamChain.logParameters ps k)
      (deriv (ParamChain.logParameters ps) k) (deriv (deriv (ParamChain.logParameters ps)) k)
      (ParamChain.coordinateSteps ps.length) = curveSecondMajorant K k ps := by
  rw [(exponentialMajorants_eq_jets K _ _ _ _).2,
    exponentialJets_logParameters ps hreg hpos, (curveMajorants_eq_jets K k ps).2]

theorem qBoundedJets_second_curveChain
    (ps : List (ℝ → ℝ × E)) {k B R K : ℝ} {f : E → ℝ}
    (hf : QPotential 5 B f)
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hpos : ∀ p ∈ ps, 0 < (p k).1)
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient 3 (B + 1) ≤ K)
    (hMass : massSensitivityJetCoefficient 2 (B + 1) ≤ K)
    (hDir : directionSensitivityCoefficient 3 (B + 1) ≤ K)
    (hsource : ∀ A H m dm ddm : ℝ, 0 ≤ A → 0 ≤ H → 0 < m → m⁻¹ ≤ R →
      ∀ v w b : E, secondVariationBound (B + 1) A H m dm ddm v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * secondVariationSource A dm ddm v w b)
    (hgeometry : ∀ p ∈ ps, (p k).1 ≤ 1 ∧ ‖(p k).2‖ ≤ 1 ∧
      (B + 1) * ‖(p k).2‖ ^ 2 ≤ 1 / 2 ∧ ((p k).1)⁻¹ ≤ R)
    (hbudget : (stepStabilityCoefficient 5 (B + 1) + 1) *
      chainEnergy (ps.map (fun p => p k)) ≤ 1)
    (hcurv : (B + 1) * chainEnergy (ps.map (fun p => p k)) ≤ 1 / 2) :
    QBoundedJets 1 (curveSecondMajorant K k ps)
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
      QPotential 5 (B + 1) (vectorIncrementChain (ParamChain.exponentialSteps tail (p k)) f) := by
    intro front tail hsplit
    have hsplit' : ParamChain.exponentialSteps cs (p k) =
        ParamChain.exponentialSteps front (p k) ++ ParamChain.exponentialSteps tail (p k) := by
      simp only [ParamChain.exponentialSteps, hsplit, List.map_append]
    apply qPotential_chain_tail (ParamChain.exponentialSteps front (p k)) _ hf (by norm_num)
    · rw [← hsplit']
      exact hmass
    · rw [← hsplit', hpath]
      exact hbudget
    · rw [← hsplit', hpath]
      exact hcurv
  have H := qBoundedJets_second_exponentialChain cs hp hK hTilt hMass hDir hsource hpot hgeom
  rw [exponentialSecondMajorant_logParameters K ps hreg hpos] at H
  have heq : (fun x => deriv (deriv (fun t => vectorIncrementChain
      (ps.map (fun q => q t)) f x)) k) =
      fun x => deriv (deriv (fun t => vectorIncrementChain
        (ParamChain.exponentialSteps cs (p t)) f x)) k := by
    funext x
    apply Filter.EventuallyEq.deriv_eq
    apply Filter.EventuallyEq.deriv
    filter_upwards [positive_masses_eventually ps hreg hpos] with t ht
    rw [ParamChain.coordinateSteps_apply ps t ht]
  rw [heq]
  exact H

private theorem chainEnergy_le_windowVariation (ps : List (ℝ → ℝ × E)) (k : ℝ) :
    chainEnergy (ps.map (fun p => p k)) ≤ variationEnergy (windowVariationEnergy k) ps := by
  rw [windowVariationEnergy_sum]
  have h₁ : 0 ≤ (ps.map fun p => ‖deriv (fun t => (p t).2) k‖ ^ 2).sum :=
    List.sum_nonneg (fun a ha => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
      exact sq_nonneg _)
  have h₂ : 0 ≤ (ps.map fun p => ‖deriv (deriv (fun t => (p t).2)) k‖ ^ 2).sum :=
    List.sum_nonneg (fun a ha => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
      exact sq_nonneg _)
  simp only [chainEnergy, List.map_map, Function.comp_def]
  linarith

theorem scalarData_window_second_variation {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ N : ℕ, 1 ≤ N →
      ∀ k : ℝ, |k| ≤ 1 / 2 →
        QBoundedJets 1 (C * h)
          (fun x => deriv (deriv (fun t => vectorIncrementChain
            ((windowKCurves β (cdf (D.μ : Measure ℝ)) (r - h) h N).map (fun p => p t))
            (cornerTerminal β (cdf (D.μ : Measure ℝ)) r h) x)) k) := by
  obtain ⟨A, h₁, hA, hh₁, hvariation⟩ := scalarData_window_variation_budget D hl hlu hu
  obtain ⟨P, h₂, _, hh₂, hparam⟩ := scalarData_window_parameter_budget D hl hlu hu
  obtain ⟨a₀, h₃, ha₀, hh₃, hmass⟩ := scalarData_window_mass_floor D hl hu
  let B := terminalJetBound D 5
  have hB : 0 ≤ B := terminalJetBound_nonneg D 5
  obtain ⟨K₀, hK₀, hsource₀⟩ := secondVariationBound_le_source
    (show 0 ≤ B + 1 by positivity) (show 0 ≤ a₀⁻¹ by positivity)
  let K := K₀ + |tiltedStabilityCoefficient 3 (B + 1)| +
    |massSensitivityJetCoefficient 2 (B + 1)| +
    |directionSensitivityCoefficient 3 (B + 1)| + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKK : K₀ ≤ K := by
    dsimp only [K]
    linarith [abs_nonneg (tiltedStabilityCoefficient 3 (B + 1)),
      abs_nonneg (massSensitivityJetCoefficient 2 (B + 1)),
      abs_nonneg (directionSensitivityCoefficient 3 (B + 1))]
  have hTilt : tiltedStabilityCoefficient 3 (B + 1) ≤ K := by
    dsimp only [K]
    linarith [le_abs_self (tiltedStabilityCoefficient 3 (B + 1)),
      abs_nonneg (massSensitivityJetCoefficient 2 (B + 1)),
      abs_nonneg (directionSensitivityCoefficient 3 (B + 1))]
  have hMass : massSensitivityJetCoefficient 2 (B + 1) ≤ K := by
    dsimp only [K]
    linarith [le_abs_self (massSensitivityJetCoefficient 2 (B + 1)),
      abs_nonneg (tiltedStabilityCoefficient 3 (B + 1)),
      abs_nonneg (directionSensitivityCoefficient 3 (B + 1))]
  have hDir : directionSensitivityCoefficient 3 (B + 1) ≤ K := by
    dsimp only [K]
    linarith [le_abs_self (directionSensitivityCoefficient 3 (B + 1)),
      abs_nonneg (tiltedStabilityCoefficient 3 (B + 1)),
      abs_nonneg (massSensitivityJetCoefficient 2 (B + 1))]
  have hsource : ∀ A H m dm ddm : ℝ, 0 ≤ A → 0 ≤ H → 0 < m → m⁻¹ ≤ a₀⁻¹ →
      ∀ v w b : E, secondVariationBound (B + 1) A H m dm ddm v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * secondVariationSource A dm ddm v w b := by
    intro A H m dm ddm hA hH hm hinv v w b
    apply (hsource₀ A H m dm ddm hA hH hm hinv v w b).trans
    have hs : 0 ≤ secondVariationSource A dm ddm v w b := by
      dsimp only [secondVariationSource]
      positivity
    gcongr
  have hS : 0 ≤ stepStabilityCoefficient 5 (B + 1) :=
    stepStabilityCoefficient_nonneg 5 (by positivity)
  let L := stepStabilityCoefficient 5 (B + 1) + 1 + 2 * (B + 1) + 8 * K + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  let h₄ := kStabilityInteriorRadius D.q l u
  have hh₄ : 0 < h₄ := kStabilityInteriorRadius_pos hl hu
  refine ⟨24 * K * A, min (min h₁ h₂) (min h₃ (min h₄ (A * L + 1)⁻¹)),
    by positivity, lt_min (lt_min hh₁ hh₂)
      (lt_min hh₃ (lt_min hh₄ (inv_pos.mpr (by positivity)))), ?_⟩
  intro r hr h hh hh0 N hN k hk
  have hh1 : h ≤ h₁ := hh0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh2 : h ≤ h₂ := hh0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh3 : h ≤ h₃ := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh4 : h ≤ h₄ := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hhinv : h ≤ (A * L + 1)⁻¹ := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let ps := windowKCurves β (cdf (D.μ : Measure ℝ)) (r - h) h N
  obtain ⟨henergy, hmder⟩ := hvariation r hr h hh hh1 N hN k hk
  have he : 0 ≤ variationEnergy (windowVariationEnergy k) ps :=
    variationEnergy_nonneg (fun p _ => windowVariationEnergy_nonneg k p)
  have hLE : L * variationEnergy (windowVariationEnergy k) ps ≤ 1 := by
    have hinv : h * (A * L + 1) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < A * L + 1)).mp (by simpa only [one_div] using hhinv)
    have H := mul_le_mul_of_nonneg_left henergy hL.le
    nlinarith
  have hbudget : (stepStabilityCoefficient 5 (B + 1) + 1) *
      chainEnergy (ps.map (fun p => p k)) ≤ 1 := by
    apply le_trans (mul_le_mul_of_nonneg_left (chainEnergy_le_windowVariation ps k) (by positivity))
    apply le_trans (mul_le_mul_of_nonneg_right (show stepStabilityCoefficient 5 (B + 1) + 1 ≤ L by
      dsimp only [L]; linarith) he) hLE
  have hcurv : (B + 1) * chainEnergy (ps.map (fun p => p k)) ≤ 1 / 2 := by
    have H := mul_le_mul_of_nonneg_right (show 2 * (B + 1) ≤ L by
      dsimp only [L]; linarith) he
    have H' := mul_le_mul_of_nonneg_left (chainEnergy_le_windowVariation ps k)
      (show 0 ≤ B + 1 by positivity)
    nlinarith
  have hsmall : 8 * K * variationEnergy (windowVariationEnergy k) ps ≤ 1 :=
    (mul_le_mul_of_nonneg_right (show 8 * K ≤ L by dsimp only [L]; linarith) he).trans hLE
  have he1 : variationEnergy (windowVariationEnergy k) ps ≤ 1 := by
    have H := mul_le_mul_of_nonneg_right (show 1 ≤ L by dsimp only [L]; linarith) he
    nlinarith
  have hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k :=
    fun p hp => (hparam r hr h hh hh2 N hN p hp k hk).1
  have hpos : ∀ p ∈ ps, 0 < (p k).1 :=
    fun p hp => ha₀.trans_le (hmass r hr h hh hh3 N hN p hp k hk).1
  have hgeometry : ∀ p ∈ ps, (p k).1 ≤ 1 ∧ ‖(p k).2‖ ≤ 1 ∧
      (B + 1) * ‖(p k).2‖ ^ 2 ≤ 1 / 2 ∧ ((p k).1)⁻¹ ≤ a₀⁻¹ := by
    intro p hp
    have hsingle : ‖(p k).2‖ ^ 2 ≤ chainEnergy (ps.map (fun p => p k)) := by
      simp only [chainEnergy, List.map_map, Function.comp_def]
      exact List.single_le_sum (fun a ha => by
        obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
        exact sq_nonneg _) _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hv2 := hsingle.trans (chainEnergy_le_windowVariation ps k)
    refine ⟨(hmass r hr h hh hh3 N hN p hp k hk).2, ?_, ?_, ?_⟩
    · nlinarith [norm_nonneg ((p k).2)]
    · exact (mul_le_mul_of_nonneg_left hsingle (by positivity)).trans hcurv
    · simpa only [one_div] using one_div_le_one_div_of_le ha₀
        (hmass r hr h hh hh3 N hN p hp k hk).1
  have ht := kStability_time_mem hr hh.le hh4 (show (4 : ℝ) ∈ Icc (0 : ℝ) 4 by norm_num)
  have hterminal : QPotential 5 B (cornerTerminal β (cdf (D.μ : Measure ℝ)) r h) :=
    scalarData_terminal_qPotential D 5 (by
      constructor <;> linarith [ht.1, ht.2, D.q_mem.2])
  apply (qBoundedJets_second_curveChain ps hterminal hreg hpos hK.le
    hTilt hMass hDir hsource hgeometry hbudget hcurv).mono
  calc
    curveSecondMajorant K k ps ≤ 24 * K * variationEnergy (windowVariationEnergy k) ps :=
      curveSecondMajorant_le_variation ps k hK.le hmder hsmall
    _ ≤ 24 * K * A * h := by
      nlinarith [mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 24 * K)]

set_option maxHeartbeats 800000 in
private theorem mixed_deriv_commute {F : ℝ × ℝ → ℝ} {k z : ℝ}
    (hF : ContDiffAt ℝ 2 F (k,z)) :
    deriv (fun t => deriv (fun y => F (t,y)) z) k =
      deriv (fun y => deriv (fun t => F (t,y)) k) z := by
  have hevent : ∀ᶠ w in 𝓝 (k,z), DifferentiableAt ℝ F w := by
    filter_upwards [hF.eventually (by norm_num)] with w hw
    exact hw.differentiableAt (by norm_num)
  have hfst : (fun y => deriv (fun t => F (t,y)) k) =ᶠ[𝓝 z]
      fun y => fderiv ℝ F (k,y) (1,0) := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually hevent] with y hy
    exact (hy.hasFDerivAt.comp_hasDerivAt k
      ((hasDerivAt_id k).prodMk (hasDerivAt_const k y))).deriv
  have hsnd : (fun t => deriv (fun y => F (t,y)) z) =ᶠ[𝓝 k]
      fun t => fderiv ℝ F (t,z) (0,1) := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hevent] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt z
      ((hasDerivAt_const z t).prodMk (hasDerivAt_id z))).deriv
  have hdf := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hleft := ((hdf.hasFDerivAt.comp_hasDerivAt k
    ((hasDerivAt_id k).prodMk (hasDerivAt_const k z))).clm_apply
      (hasDerivAt_const k ((0,1) : ℝ × ℝ))).deriv
  have hright := ((hdf.hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z k).prodMk (hasDerivAt_id z))).clm_apply
      (hasDerivAt_const z ((1,0) : ℝ × ℝ))).deriv
  change deriv (fun t => fderiv ℝ F (t,z) (0,1)) k =
    fderiv ℝ (fderiv ℝ F) (k,z) (1,0) (0,1) + fderiv ℝ F (k,z) 0 at hleft
  change deriv (fun y => fderiv ℝ F (k,y) (1,0)) z =
    fderiv ℝ (fderiv ℝ F) (k,z) (0,1) (1,0) + fderiv ℝ F (k,z) 0 at hright
  rw [hsnd.deriv_eq, hfst.deriv_eq, hleft, hright]
  simp only [map_zero, add_zero]
  exact hF.isSymmSndFDerivAt (by norm_num) (1,0) (0,1)

private theorem second_spatial_bound {F : ℝ → ℝ → ℝ} {a b M : ℝ}
    (hab : a < b) (hM : 0 ≤ M)
    (hjoint : ∀ t ∈ Icc a b, ∀ z, ContDiffAt ℝ 2 (Function.uncurry F) (t,z))
    (hspatial : ∀ z, ∀ t ∈ Icc a b,
      ContDiffAt ℝ 2 (fun s => deriv (F s) z) t)
    (hsecond : ∀ t ∈ Icc a b,
      LipschitzWith ⟨M, hM⟩ (fun z => deriv (deriv (fun s => F s z)) t)) :
    ∀ z, ∀ t ∈ Icc a b,
      |deriv (deriv (fun s => deriv (F s) z)) t| ≤ M := by
  let A : ℝ → ℝ → ℝ := fun t z => deriv (fun s => F s z) t
  let G : ℝ → ℝ → ℝ := fun t z => deriv (F t) z
  have hA (t : ℝ) (ht : t ∈ Icc a b) (z : ℝ) : DifferentiableAt ℝ (fun s => A s z) t := by
    have H := (hjoint t ht z).comp t (contDiff_id.prodMk contDiff_const).contDiffAt
    exact (H.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hAz (t : ℝ) (ht : t ∈ Icc a b) (z : ℝ) : DifferentiableAt ℝ (A t) z := by
    have hF := hjoint t ht z
    have heq : A t =ᶠ[𝓝 z] fun y => fderiv ℝ (Function.uncurry F) (t,y) (1,0) := by
      have hevent : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ (Function.uncurry F) (t,y) := by
        filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually
          (hF.eventually (by norm_num))] with y hy
        exact hy.differentiableAt (by norm_num)
      filter_upwards [hevent] with y hy
      exact (hy.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))).deriv
    apply DifferentiableAt.congr_of_eventuallyEq _ heq
    exact (((hF.fderiv_right (m := 1) (by norm_num)).comp z
      (contDiff_const.prodMk contDiff_id).contDiffAt).clm_apply contDiffAt_const).differentiableAt
        (by norm_num)
  have hcomm (t : ℝ) (ht : t ∈ Icc a b) (z : ℝ) :
      deriv (fun s => G s z) t = deriv (A t) z := mixed_deriv_commute (hjoint t ht z)
  have hdiff (t : ℝ) (ht : t ∈ Icc a b) (s : ℝ) (hs : s ∈ Icc a b) :
      LipschitzWith ⟨M * |t - s|, mul_nonneg hM (abs_nonneg _)⟩ (fun z => A t z - A s z) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hder (v : ℝ) (hv : v ∈ Icc a b) :
        deriv (fun w => A w x - A w y) v =
          deriv (deriv (fun w => F w x)) v - deriv (deriv (fun w => F w y)) v :=
      (deriv_fun_sub (hA v hv x) (hA v hv y))
    have H := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (C := M * |x - y|)
      (fun v hv => (hA v hv x).sub (hA v hv y))
      (fun v hv => by
        change ‖deriv (fun w => A w x - A w y) v‖ ≤ M * |x - y|
        rw [hder v hv]
        have Hb := (hsecond v hv).dist_le_mul x y
        change |deriv (deriv (fun w => F w x)) v - deriv (deriv (fun w => F w y)) v| ≤
          M * |x - y| at Hb
        simpa only [Real.norm_eq_abs] using Hb) hs ht
    change ‖(A t x - A t y) - (A s x - A s y)‖ ≤ M * |x - y| * ‖t - s‖ at H
    have heq : (A t x - A s x) - (A t y - A s y) =
        (A t x - A t y) - (A s x - A s y) := by ring
    change |(A t x - A s x) - (A t y - A s y)| ≤ M * |t - s| * |x - y|
    rw [heq]
    simpa only [Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using H
  have hG : ∀ z, LipschitzOnWith ⟨M, hM⟩ (deriv (fun s => G s z)) (Icc a b) := by
    intro z
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht s hs
    have H := (norm_deriv_le_of_lipschitz (x₀ := z) (hdiff t ht s hs))
    change ‖deriv (fun z => A t z - A s z) z‖ ≤ M * |t - s| at H
    rw [deriv_fun_sub (hAz t ht z) (hAz s hs z), ← hcomm t ht z, ← hcomm s hs z] at H
    change |deriv (fun s => G s z) t - deriv (fun s => G s z) s| ≤ M * |t - s|
    simpa only [Real.norm_eq_abs] using H
  intro z t ht
  have hinterior : ∀ v ∈ Ioo a b, |deriv (deriv (fun s => G s z)) v| ≤ M := by
    intro v hv
    have H := norm_deriv_le_of_lipschitzOn (x₀ := v)
      (Icc_mem_nhds hv.1 hv.2) (hG z)
    change ‖deriv (deriv (fun s => G s z)) v‖ ≤ M at H
    simpa only [Real.norm_eq_abs] using H
  have hc : ContinuousWithinAt (fun v => |deriv (deriv (fun s => G s z)) v|) (Ioo a b) t :=
    ((((hspatial z t ht).derivWithin (m := 1) (by norm_num)).derivWithin
      (m := 0) (by norm_num)).continuousAt).abs.continuousWithinAt
  exact ContinuousWithinAt.closure_le (by rwa [closure_Ioo hab.ne]) hc
    (continuousWithinAt_const (b := M)) hinterior

theorem scalarData_boundary_quantitative {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ N : ℕ, 1 ≤ N →
      ∀ z k : ℝ, |k| ≤ 1 / 2 →
        |deriv (deriv (fun t => OW.boundary β (cdf (D.μ : Measure ℝ))
          (1 / 2) (r - h) h t N z)) k| ≤ C * h ∧
        |deriv (deriv (fun t => deriv (OW.boundary β (cdf (D.μ : Measure ℝ))
          (1 / 2) (r - h) h t N) z)) k| ≤ C * h := by
  obtain ⟨C, h₁, hC, hh₁, hsecond⟩ := scalarData_window_second_variation D hl hlu hu
  obtain ⟨P, h₂, _, hh₂, hparam⟩ := scalarData_window_parameter_budget D hl hlu hu
  obtain ⟨a₀, h₃, ha₀, hh₃, hmass⟩ := scalarData_window_mass_floor D hl hu
  obtain ⟨h₄, hh₄, hregular⟩ := scalarData_boundary_parameter_regular D hl hlu hu
  let h₅ := kStabilityInteriorRadius D.q l u
  have hh₅ : 0 < h₅ := kStabilityInteriorRadius_pos hl hu
  refine ⟨C, min (min h₁ h₂) (min h₃ (min h₄ h₅)), hC,
    lt_min (lt_min hh₁ hh₂) (lt_min hh₃ (lt_min hh₄ hh₅)), ?_⟩
  intro r hr h hh hh0 N hN z k hk
  have hh1 : h ≤ h₁ := hh0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh2 : h ≤ h₂ := hh0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh3 : h ≤ h₃ := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh4 : h ≤ h₄ := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hh5 : h ≤ h₅ := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let ps := windowKCurves β (cdf (D.μ : Measure ℝ)) (r - h) h N
  let f := cornerTerminal β (cdf (D.μ : Measure ℝ)) r h
  let F : ℝ → ℝ → ℝ := fun t => OW.boundary β (cdf (D.μ : Measure ℝ))
    (1 / 2) (r - h) h t N
  have hboundary (t : ℝ) : F t = fun y =>
      vectorIncrementChain (ps.map (fun p => p t)) f (fun _ => y) := by
    funext y
    dsimp only [ps]
    rw [windowKCurves_apply β (cdf (D.μ : Measure ℝ)) (r - h) h t N hh.le]
    rfl
  have hid (t y : ℝ) :
      deriv (deriv (fun v => F v y)) t =
        (fun x => deriv (deriv (fun v => vectorIncrementChain
          (ps.map (fun p => p v)) f x)) t) (fun _ => y) := by
    congr 2
    funext v
    exact congrFun (hboundary v) y
  have hjet (t : ℝ) (ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
      QBoundedJets 1 (C * h) (fun x => deriv (deriv (fun v =>
        vectorIncrementChain (ps.map (fun p => p v)) f x)) t) :=
    hsecond r hr h hh hh1 N hN t (abs_le.mpr ht)
  have htime := kStability_time_mem hr hh.le hh5
    (show (4 : ℝ) ∈ Icc (0 : ℝ) 4 by norm_num)
  have hf : QPotential 3 (terminalJetBound D 3) f :=
    scalarData_terminal_qPotential D 3 (by
      constructor <;> linarith [htime.1, htime.2, D.q_mem.2])
  have hjoint : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), ∀ y,
      ContDiffAt ℝ 2 (Function.uncurry F) (t,y) := by
    intro t ht y
    have hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p t :=
      fun p hp => (hparam r hr h hh hh2 N hN p hp t (abs_le.mpr ht)).1
    have hpos : ∀ p ∈ ps, 0 < (p t).1 :=
      fun p hp => ha₀.trans_le (hmass r hr h hh hh3 N hN p hp t (abs_le.mpr ht)).1
    have H := ParamChain.contDiffAt_curveChain ps hf (by norm_num) hreg hpos (fun _ => y)
    have hdiag : ContDiff ℝ 2 (fun w : ℝ × ℝ => (w.1, fun _ : Fin 3 => w.2)) :=
      contDiff_fst.prodMk (contDiff_pi.mpr (fun _ => contDiff_snd))
    convert! H.comp (t,y) hdiag.contDiffAt using 1
    funext w
    exact congrFun (hboundary w.1) w.2
  have hdiagLip : LipschitzWith 1 (fun y : ℝ => (fun _ : Fin 3 => y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖(fun _ : Fin 3 => x) - (fun _ => y)‖ ≤ (1 : ℝ) * |x - y|
    rw [one_mul]
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg (x - y))).mpr
    intro i
    exact le_rfl
  have hLip : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2),
      LipschitzWith ⟨C * h, mul_nonneg hC.le hh.le⟩
        (fun y => deriv (deriv (fun v => F v y)) t) := by
    intro t ht
    have H := ((qBoundedJets_iff_qBddSmooth.mp (hjet t ht)).potential.lipschitzWith le_rfl).comp hdiagLip
    convert! H using 1
    · congr 1
      apply NNReal.eq
      change C * h = C * h * 1
      ring
    · funext y
      exact hid t y
  constructor
  · rw [show (fun t => OW.boundary β (cdf (D.μ : Measure ℝ))
        (1 / 2) (r - h) h t N z) = (fun t => F t z) from rfl, hid]
    simpa only [Real.norm_eq_abs] using (hjet k (abs_le.mp hk)).norm_le (fun _ => z)
  · exact second_spatial_bound (by norm_num) (mul_nonneg hC.le hh.le) hjoint
      (fun y t ht => (hregular r hr h hh hh4 N hN y t (abs_le.mpr ht)).2) hLip z k (abs_le.mp hk)

theorem scalarData_boundaryKSecondBound {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      BoundaryKSecondBound β (cdf (D.μ : Measure ℝ)) (Icc l u) C h₀ := by
  obtain ⟨C, h₁, hC, hh₁, hquant⟩ := scalarData_boundary_quantitative D hl hlu hu
  obtain ⟨h₀, hh₀, _, H⟩ :=
    scalarData_boundaryKSecondBound_of_quantitative D hl hlu hu hh₁ hquant
  exact ⟨C, h₀, hC, hh₀, H⟩

theorem scalarData_crudeC1 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    CrudeC1 β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  by_cases hlu : l ≤ u
  · obtain ⟨C, h₀, hC, hh₀, hquant⟩ := scalarData_boundary_quantitative D hl hlu hu
    exact scalarData_crudeC1_of_quantitative D hl hlu hu hC.le hh₀ hquant
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

end SKBarriers2.Corner
