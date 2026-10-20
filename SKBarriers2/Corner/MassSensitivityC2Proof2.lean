module

public import SKBarriers2.Corner.MassSensitivityC2Proof
public import SKBarriers2.Analysis.ParamStep3
public import SKBarriers2.Main.Final

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set OAI.SK.Analytic

namespace SKBarriers2.ParamChain

local notation "E" => (Fin 3 → ℝ)

section DefectRegularity

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

private theorem smooth_linearParameter (L : P →L[ℝ] ℝ) :
    ParamSmooth (fun z : P × E => L z.1) := by
  let K : P × E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.fst ℝ P E)
  have hD : fderiv ℝ (fun z : P × E => L z.1) = fun _ => K :=
    funext (fun _ => K.fderiv)
  refine ⟨K.contDiff, ?_, ?_, ?_⟩
  · intro R
    refine ⟨‖L‖ * max R 0, 0, by positivity, le_rfl, ?_⟩
    intro p x hp
    simpa only [zero_mul, Real.exp_zero, mul_one] using
      (L.le_opNorm p).trans (mul_le_mul_of_nonneg_left
        (hp.trans (le_max_left _ _)) (norm_nonneg L))
  · rw [hD]
    exact ParamExpGrowth.of_bounded (norm_nonneg K) (fun _ => le_rfl)
  · rw [hD]
    have hDD : fderiv ℝ (fun _ : P × E => K) =
        fun _ => (0 : P × E →L[ℝ] P × E →L[ℝ] ℝ) :=
      funext (fun _ => fderiv_const_apply K)
    rw [hDD]
    exact ParamExpGrowth.of_bounded
      (f := fun _ : P × E => (0 : P × E →L[ℝ] P × E →L[ℝ] ℝ))
      (C := 0) le_rfl (fun _ => le_of_eq ContinuousLinearMap.opNorm_zero)

private theorem apply_eq_coordinate_sum (L : E →L[ℝ] ℝ) (v : E) :
    L v = ∑ i : Fin 3, v i * L (Pi.single i 1) := by
  have hv : v = ∑ i : Fin 3, v i • Pi.single i 1 := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    simp
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

private theorem smooth_movingPairing {A : P × E → E →L[ℝ] ℝ}
    (hA : ∀ i : Fin 3, ParamSmooth (fun z => A z (Pi.single i 1)))
    (V : P →L[ℝ] E) : ParamSmooth (fun z => A z (V z.1)) := by
  have hsum := ParamSmooth.sum Finset.univ
    (fun i : Fin 3 => fun z : P × E => V z.1 i * A z (Pi.single i 1))
    (fun i _ => (smooth_linearParameter ((ContinuousLinearMap.proj i).comp V)).mul (hA i))
  simpa only [← apply_eq_coordinate_sum] using hsum

structure TestJetFamily (G : P × E → ℝ) : Prop where
  value : ParamSmooth G
  first : ∀ i : Fin 3,
    ParamSmooth (fun z => fderiv ℝ (fun y => G (z.1,y)) z.2 (Pi.single i 1))
  second : ∀ i j : Fin 3,
    ParamSmooth (fun z => fderiv ℝ (fderiv ℝ (fun y => G (z.1,y))) z.2
      (Pi.single i 1) (Pi.single j 1))

theorem testJetFamily_fixed {C : ℝ} {g : E → ℝ} (hg : QBoundedJets 4 C g) :
    TestJetFamily (fun z : P × E => g z.2) := by
  refine ⟨(regular_fixedTerminal (qBoundedJets_iff_qBddSmooth.mp hg).potential
    (by norm_num) P).toSmooth, ?_, ?_⟩
  · intro i
    exact (regular_fixedTerminal
      (qBoundedJets_iff_qBddSmooth.mp (hg.derivativeJets.apply_const (Pi.single i 1))).potential
      (by norm_num) P).toSmooth
  · intro i j
    exact (regular_fixedTerminal (qBoundedJets_iff_qBddSmooth.mp
      (hg.derivativeJets.derivativeJets.apply_const (Pi.single i 1) |>.apply_const
        (Pi.single j 1))).potential (by norm_num) P).toSmooth

private theorem smooth_generator {F G : P × E → ℝ}
    (hF : ∀ i : Fin 3,
      ParamSmooth (fun z => fderiv ℝ (fun y => F (z.1,y)) z.2 (Pi.single i 1)))
    (hG : TestJetFamily G)
    (hGs : ∀ p : P, ContDiff ℝ 2 (fun y => G (p,y)))
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) :
    ParamSmooth (fun z => StepCalculus.pathGenerator (Real.exp (M z.1)) (V z.1)
      (fun y => F (z.1,y)) (fun y => G (z.1,y)) z.2) := by
  have hdf := smooth_movingPairing hF V
  have hdg := smooth_movingPairing hG.first V
  have hddg := smooth_movingPairing
    (A := fun z => fderiv ℝ (fderiv ℝ (fun y => G (z.1,y))) z.2 (V z.1))
    (fun j => by
      have H := smooth_movingPairing
        (A := fun z => (ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1)).comp
          (fderiv ℝ (fderiv ℝ (fun y => G (z.1,y))) z.2))
        (fun i => hG.second i j) V
      exact H) V
  have he (z : P × E) : StepCalculus.directionalJet (V z.1) 2 (fun y => G (z.1,y)) z.2 =
      fderiv ℝ (fderiv ℝ (fun y => G (z.1,y))) z.2 (V z.1) (V z.1) := by
    have h := ((ContinuousLinearMap.apply ℝ ℝ (V z.1)).hasFDerivAt.comp z.2
      (((hGs z.1).fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num) z.2).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => fderiv ℝ (fun y => G (z.1,y)) y (V z.1)) z.2 (V z.1) = _
    change fderiv ℝ (fun y => fderiv ℝ (fun y => G (z.1,y)) y (V z.1)) z.2 = _ at h
    rw [h]
    rfl
  have H := (((regular_exp_parameter (X := E) M).toSmooth.mul hdf).mul hdg).add
    (hddg.const_mul (1/2))
  convert H using 1
  funext z
  dsimp only [StepCalculus.pathGenerator]
  rw [he]
  ring

private theorem smooth_chainSpatial {B : ℝ} {f : E → ℝ} (hf : QPotential 3 B f)
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) (i : Fin 3) :
    ParamSmooth (fun z : P × E => fderiv ℝ
      (vectorIncrementChain (exponentialSteps ps z.1) f) z.2 (Pi.single i 1)) := by
  have hd := hf.derivativeJets.apply_const (Pi.single i 1)
  have H := smooth_exponentialAverage ps (regular_fixedTerminal hf (by norm_num) P)
    (regular_fixedTerminal (qBoundedJets_iff_qBddSmooth.mp hd).potential le_rfl P).toSmooth
  have he : (fun z : P × E => fderiv ℝ
      (vectorIncrementChain (exponentialSteps ps z.1) f) z.2 (Pi.single i 1)) =
      exponentialAverage ps (fun z => f z.2) (fun z => fderiv ℝ f z.2 (Pi.single i 1)) := by
    funext z
    exact fderiv_chain_average _ (hf.boundedDerivs (by norm_num)) _ _
  rw [he]
  exact H

private theorem smooth_generatorSum {B : ℝ} {f : E → ℝ} (hf : QPotential 3 B f)
    {G : P × E → ℝ} (hG : TestJetFamily G)
    (hGs : ∀ p : P, ContDiff ℝ 2 (fun y => G (p,y)))
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) :
    ParamSmooth (fun z : P × E => StepCalculus.pathGeneratorSum f
      (fun y => G (z.1,y)) (exponentialSteps ps z.1) z.2) := by
  induction ps with
  | nil => exact paramSmooth_const 0
  | cons p ps ih =>
    have hf' (i : Fin 3) : ParamSmooth (fun z : P × E => fderiv ℝ f z.2 (Pi.single i 1)) :=
      (regular_fixedTerminal (qBoundedJets_iff_qBddSmooth.mp
        (hf.derivativeJets.apply_const (Pi.single i 1))).potential le_rfl P).toSmooth
    exact (smooth_generator (F := fun z => f z.2) hf' hG hGs p.1 p.2).add ih

end DefectRegularity

end SKBarriers2.ParamChain

namespace SKBarriers2.ParamChain

local notation "E" => (Fin 3 → ℝ)

section LocalDefectTerms

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

private theorem smooth_sub {F G : P × E → ℝ}
    (hF : ParamSmooth F) (hG : ParamSmooth G) : ParamSmooth (fun z => F z-G z) := by
  convert hF.add (hG.const_mul (-1)) using 1
  funext z
  ring

theorem smooth_exponentialDefectTerms {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) {G : P × E → ℝ} (hG : TestJetFamily G)
    (p : (P →L[ℝ] ℝ) × (P →L[ℝ] E))
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) (i : Fin 4) :
    ParamSmooth (fun z : P × E => StepCalculus.tiltedPathDefectTerms
      (Real.exp (p.1 z.1),p.2 z.1) (exponentialSteps ps z.1) f
      (fun y => G (z.1,y)) z.2 i) := by
  let F : P × E → ℝ := exponentialChain ps (fun z => f z.2)
  let S : P × E → ℝ := fun z => StepCalculus.pathGeneratorSum f
    (fun y => G (z.1,y)) (exponentialSteps ps z.1) z.2
  have hfR := regular_fixedTerminal hf (by norm_num) P
  have hF : ParamRegular F := regular_exponentialChain ps hfR
  have hGs (q : P) : ContDiff ℝ 2 (fun y => G (q,y)) :=
    hG.value.1.comp (contDiff_const.prodMk contDiff_id)
  have hS : ParamSmooth S := smooth_generatorSum hf hG hGs ps
  have hA : ParamSmooth (exponentialAverage ps (fun z => f z.2) G) :=
    smooth_exponentialAverage ps hfR hG.value
  have hR : ParamSmooth (fun z : P × E => StepCalculus.tiltedPathTaylorDefect
      (exponentialSteps ps z.1) f (fun y => G (z.1,y)) z.2) :=
    smooth_sub (smooth_sub hA hG.value) hS
  have hQ : ParamSmooth (fun z : P × E => StepCalculus.pathGenerator
      (Real.exp (p.1 z.1)) (p.2 z.1) (fun y => F (z.1,y)) (fun y => G (z.1,y)) z.2) :=
    smooth_generator (fun j => smooth_chainSpatial hf ps j) hG hGs p.1 p.2
  have hq : ParamSmooth (fun z : P × E => StepCalculus.pathGenerator
      (Real.exp (p.1 z.1)) (p.2 z.1) f (fun y => G (z.1,y)) z.2) := by
    have hd (j : Fin 3) : ParamSmooth (fun z : P × E => fderiv ℝ f z.2 (Pi.single j 1)) :=
      (regular_fixedTerminal (qBoundedJets_iff_qBddSmooth.mp
        (hf.derivativeJets.apply_const (Pi.single j 1))).potential le_rfl P).toSmooth
    exact smooth_generator (F := fun z => f z.2) hd hG hGs p.1 p.2
  fin_cases i
  · exact smooth_movingAverage hF hR p.1 p.2
  · exact smooth_sub (smooth_sub (smooth_movingAverage hF hG.value p.1 p.2) hG.value) hQ
  · exact smooth_sub hQ hq
  · exact smooth_sub (smooth_movingAverage hF hS p.1 p.2) hS

theorem contDiffAt_parametrizedDefectTerms {B k : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) {G : P × E → ℝ} (hG : TestJetFamily G)
    (p : (P →L[ℝ] ℝ) × (P →L[ℝ] E))
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E)))
    (Q : ℝ → P) (hQ : ContDiffAt ℝ 2 Q k) (x : E) (i : Fin 4) :
    ContDiffAt ℝ 2 (fun t => StepCalculus.tiltedPathDefectTerms
      (Real.exp (p.1 (Q t)),p.2 (Q t)) (exponentialSteps ps (Q t)) f
      (fun y => G (Q t,y)) x i) k := by
  have hcurve : ContDiffAt ℝ 2 (fun t : ℝ => (Q t,x)) k := hQ.prodMk contDiffAt_const
  have hterm : ContDiffAt ℝ 2 (fun z : P × E => StepCalculus.tiltedPathDefectTerms
      (Real.exp (p.1 z.1),p.2 z.1) (exponentialSteps ps z.1) f
      (fun y => G (z.1,y)) z.2 i) (Q k,x) :=
    (smooth_exponentialDefectTerms hf hG p ps i).1.contDiffAt
  exact hterm.comp k hcurve

end LocalDefectTerms

end SKBarriers2.ParamChain

namespace SKBarriers2.ParamChain

local notation "E" => (Fin 3 → ℝ)

section MovingObservables

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem testJetFamily_finite {ι : Type} [Fintype ι] {C : ℝ}
    (a : ι → P → ℝ) (g : ι → E → ℝ)
    (ha : ∀ i, ParamSmooth (fun z : P × E => a i z.1))
    (hg : ∀ i, QBoundedJets 4 C (g i)) :
    TestJetFamily (fun z : P × E => ∑ i, a i z.1*g i z.2) := by
  have hd (p : P) (x : E) :
      fderiv ℝ (fun y => ∑ i, a i p*g i y) x = ∑ i, a i p • fderiv ℝ (g i) x := by
    rw [fderiv_fun_sum (fun i _ => ((hg i).smooth.differentiable (by norm_num) x).const_mul _)]
    exact Finset.sum_congr rfl (fun i _ => fderiv_const_mul
      ((hg i).smooth.differentiable (by norm_num) x) _)
  have hdd (p : P) (x : E) : fderiv ℝ (fderiv ℝ (fun y => ∑ i, a i p*g i y)) x =
      ∑ i, a i p • fderiv ℝ (fderiv ℝ (g i)) x := by
    rw [show fderiv ℝ (fun y => ∑ i, a i p*g i y) =
      fun y => ∑ i, a i p • fderiv ℝ (g i) y from funext (hd p)]
    rw [fderiv_fun_sum (A := fun i y => a i p • fderiv ℝ (g i) y)
      (fun i _ => by
        change DifferentiableAt ℝ (a i p • fderiv ℝ (g i)) x
        exact ((hg i).derivativeJets.smooth.differentiable
          (by norm_num) x).const_smul (a i p))]
    exact Finset.sum_congr rfl (fun i _ => fderiv_fun_const_smul
      ((hg i).derivativeJets.smooth.differentiable (by norm_num) x) _)
  refine ⟨ParamSmooth.sum Finset.univ _ (fun i _ => (ha i).mul
    (testJetFamily_fixed (P := P) (hg i)).value), ?_, ?_⟩
  · intro j
    have he : (fun z : P × E => fderiv ℝ (fun y => ∑ i, a i z.1*g i y) z.2
        (Pi.single j 1)) = fun z => ∑ i, a i z.1*fderiv ℝ (g i) z.2 (Pi.single j 1) := by
      funext z
      rw [hd]
      simp only [sum_apply, smul_apply, smul_eq_mul]
    rw [he]
    exact ParamSmooth.sum Finset.univ _ (fun i _ => (ha i).mul
      ((testJetFamily_fixed (P := P) (hg i)).first j))
  · intro j k
    have he : (fun z : P × E => fderiv ℝ (fderiv ℝ (fun y => ∑ i, a i z.1*g i y)) z.2
        (Pi.single j 1) (Pi.single k 1)) = fun z => ∑ i,
          a i z.1*fderiv ℝ (fderiv ℝ (g i)) z.2 (Pi.single j 1) (Pi.single k 1) := by
      funext z
      rw [hdd]
      simp only [sum_apply, smul_apply, smul_eq_mul]
    rw [he]
    exact ParamSmooth.sum Finset.univ _ (fun i _ => (ha i).mul
      ((testJetFamily_fixed (P := P) (hg i)).second j k))

theorem testJetFamily_terminalGradient {B : ℝ} {f : E → ℝ}
    (hf : QPotential 5 B f) (W : P →L[ℝ] E) :
    TestJetFamily (fun z : P × E => fderiv ℝ f z.2 (W z.1)) := by
  have hg (i : Fin 3) : QBoundedJets 4 B (fun x => fderiv ℝ f x (Pi.single i 1)) := by
    simpa only [Pi.norm_single, norm_one, mul_one] using
      hf.derivativeJets.apply_const (Pi.single i 1)
  have H := testJetFamily_finite (P := P) (fun i p => W p i)
    (fun i x => fderiv ℝ f x (Pi.single i 1))
    (fun i => smooth_linearParameter ((ContinuousLinearMap.proj i).comp W)) hg
  simpa only [← apply_eq_coordinate_sum] using H

theorem testJetFamily_terminalGradient_sq {B : ℝ} {f : E → ℝ}
    (hf : QPotential 5 B f) (W : P →L[ℝ] E) :
    TestJetFamily (fun z : P × E => (fderiv ℝ f z.2 (W z.1))^2) := by
  have hg (i : Fin 3) : QBoundedJets 4 B (fun x => fderiv ℝ f x (Pi.single i 1)) := by
    simpa only [Pi.norm_single, norm_one, mul_one] using
      hf.derivativeJets.apply_const (Pi.single i 1)
  have hprod (i : Fin 3 × Fin 3) : QBoundedJets 4 (16*B*B)
      (fun x => fderiv ℝ f x (Pi.single i.1 1)*fderiv ℝ f x (Pi.single i.2 1)) := by
    simpa only [show (2:ℝ)^4=16 from by norm_num] using (hg i.1).mul (hg i.2)
  have H := testJetFamily_finite (P := P)
    (fun i : Fin 3 × Fin 3 => fun p => W p i.1*W p i.2)
    (fun i x => fderiv ℝ f x (Pi.single i.1 1)*fderiv ℝ f x (Pi.single i.2 1))
    (fun i => (smooth_linearParameter ((ContinuousLinearMap.proj i.1).comp W)).mul
      (smooth_linearParameter ((ContinuousLinearMap.proj i.2).comp W))) hprod
  have he : (fun z : P × E => ∑ i : Fin 3 × Fin 3,
      (W z.1 i.1*W z.1 i.2)*
        (fderiv ℝ f z.2 (Pi.single i.1 1)*fderiv ℝ f z.2 (Pi.single i.2 1))) =
      fun z => (fderiv ℝ f z.2 (W z.1))^2 := by
    funext z
    rw [apply_eq_coordinate_sum, pow_two, Finset.sum_mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at H
  exact H

end MovingObservables

end SKBarriers2.ParamChain

namespace SKBarriers2.ParamChain

local notation "E" => (Fin 3 → ℝ)

private theorem curve_masses_eventually_positive
    (ps : List (ℝ → ℝ × E)) {k : ℝ}
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hpos : ∀ p ∈ ps, 0 < (p k).1) :
    ∀ᶠ t in 𝓝 k, ∀ p ∈ ps, 0 < (p t).1 := by
  have H : ∀ᶠ t in 𝓝 k, ∀ j : Fin ps.length, 0 < (ps.get j t).1 := by
    apply Filter.eventually_all.mpr
    intro j
    exact (hreg _ (List.get_mem ps j)).fst.continuousAt.eventually
      (Ioi_mem_nhds (hpos _ (List.get_mem ps j)))
  filter_upwards [H] with t ht p hp
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hp
  exact ht j

theorem contDiffAt_orderedCurveDefectTerms {B k : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) (ps : List (ℝ → ℝ × E)) (j : Fin ps.length)
    {G : (Coordinates ps.length E × E) × E → ℝ} (hG : TestJetFamily G)
    (w : ℝ → E) (hw : ContDiffAt ℝ 2 w k)
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hpos : ∀ p ∈ ps, 0 < (p k).1)
    (x : E) (i : Fin 4) :
    ContDiffAt ℝ 2 (fun t => StepCalculus.tiltedPathDefectTerms
      (ps.get j t) ((ps.map (fun p => p t)).drop (j.val+1)) f
      (fun y => G ((logParameters ps t,w t),y)) x i) k := by
  let P := Coordinates ps.length E × E
  let L : P →L[ℝ] Coordinates ps.length E := ContinuousLinearMap.fst ℝ _ _
  let liftStep := fun p : (Coordinates ps.length E →L[ℝ] ℝ) ×
      (Coordinates ps.length E →L[ℝ] E) => (p.1.comp L,p.2.comp L)
  let u : (P →L[ℝ] ℝ) × (P →L[ℝ] E) :=
    (((ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.proj j)).comp L,
     ((ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.proj j)).comp L)
  let us := ((coordinateSteps (X := E) ps.length).drop (j.val+1)).map liftStep
  let Q : ℝ → P := fun t => (logParameters ps t,w t)
  have hQ : ContDiffAt ℝ 2 Q k := (logParameters_contDiffAt ps hreg hpos).prodMk hw
  have H := contDiffAt_parametrizedDefectTerms hf hG u us Q hQ x i
  apply H.congr_of_eventuallyEq
  filter_upwards [curve_masses_eventually_positive ps hreg hpos] with t ht
  have hu : (Real.exp (u.1 (Q t)),u.2 (Q t)) = ps.get j t := by
    change (Real.exp (Real.log ((ps.get j t).1)), (ps.get j t).2) = ps.get j t
    rw [Real.exp_log (ht _ (List.get_mem ps j)), Prod.mk.eta]
  have hus : exponentialSteps us (Q t) = (ps.map (fun p => p t)).drop (j.val+1) := by
    have Hs := congrArg (List.drop (j.val+1)) (coordinateSteps_apply ps t ht)
    dsimp only [us, exponentialSteps]
    rw [List.map_map]
    change (((coordinateSteps ps.length).drop (j.val+1)).map
      (fun q => (Real.exp (q.1 (logParameters ps t)),q.2 (logParameters ps t)))) = _
    simpa only [exponentialSteps, List.map_drop] using Hs
  rw [hu, hus]

theorem contDiffAt_orderedCurveDefectTerms_terminal {B k : ℝ} {f : E → ℝ}
    (hf : QPotential 5 B f) (ps : List (ℝ → ℝ × E)) (j : Fin ps.length)
    (w : ℝ → E) (hw : ContDiffAt ℝ 2 w k)
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hpos : ∀ p ∈ ps, 0 < (p k).1)
    (x : E) (i : Fin 4) :
    ContDiffAt ℝ 2 (fun t => StepCalculus.tiltedPathDefectTerms
      (ps.get j t) ((ps.map (fun p => p t)).drop (j.val+1)) f
      (fun y => fderiv ℝ f y (w t)) x i) k ∧
    ContDiffAt ℝ 2 (fun t => StepCalculus.tiltedPathDefectTerms
      (ps.get j t) ((ps.map (fun p => p t)).drop (j.val+1)) f
      (fun y => (fderiv ℝ f y (w t))^2) x i) k := by
  let W : Coordinates ps.length E × E →L[ℝ] E := ContinuousLinearMap.snd ℝ _ _
  exact ⟨contDiffAt_orderedCurveDefectTerms (hf.of_le (by norm_num)) ps j
      (testJetFamily_terminalGradient hf W) w hw hreg hpos x i,
    contDiffAt_orderedCurveDefectTerms (hf.of_le (by norm_num)) ps j
      (testJetFamily_terminalGradient_sq hf W) w hw hreg hpos x i⟩

end SKBarriers2.ParamChain

namespace SKBarriers2.Corner

local notation "E" => (Fin 3 → ℝ)

theorem scalarData_interpolated_window_curve_regular {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0<l) (hlu : l≤u) (hu : u<D.q) :
    ∃ h0 : ℝ, 0<h0 ∧ ∀ r∈Icc l u, ∀ h : ℝ, 0<h → h≤h0 →
      ∀ N : ℕ, 1≤N → ∀ lam∈Icc (0:ℝ) 1,
        ∀ p∈windowKCurves β (interpolatedProfile (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r-h)) lam) (r-h) h N,
          ∀ k : ℝ, |k|≤1/2 → ContDiffAt ℝ 2 p k ∧ (p k).1∈Ioc (0:ℝ) 1 := by
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  obtain ⟨C,hP,_,hhP,hparam⟩ := scalarData_window_parameter_budget D hl hlu hu
  obtain ⟨a0,hF,ha0,hhF,hfloor⟩ := scalarData_window_mass_floor D hl hu
  refine ⟨min (min hP hF) (kStabilityInteriorRadius D.q l u),
    lt_min (lt_min hhP hhF) (kStabilityInteriorRadius_pos hl hu),?_⟩
  intro r hr h hh hh0 N hN lam hlam p hp k hk
  have hhP' := hh0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhF' := hh0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhI := hh0.trans (min_le_right _ _)
  obtain ⟨σ,hσ,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,hj,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  let x := (j:ℝ)/(N:ℝ)
  let p0 : ℝ → ℝ × E := fun t =>
    (kStageMass α (r-h) h x σ t,(β*Real.sqrt (h/(N:ℝ))) • kDirectionShape i t)
  have hp0 : p0∈windowKCurves β α (r-h) h N := by
    apply List.mem_flatMap.mpr
    refine ⟨σ,hσ,List.mem_flatMap.mpr ⟨j,hj,?_⟩⟩
    exact List.mem_map.mpr ⟨i,hi,rfl⟩
  have hp0c := (hparam r hr h hh hhP' N hN p0 hp0 k hk).1
  have hm0 := hfloor r hr h hh hhF' N hN p0 hp0 k hk
  have hc : 1≤kStageMassDivisor σ := by fin_cases σ <;> norm_num [kStageMassDivisor]
  have hc0 : 0<kStageMassDivisor σ := by linarith
  have hs := kStability_time_mem hr hh.le hhI (show (0:ℝ)∈Icc (0:ℝ) 4 by norm_num)
  have hapos : 0<α (r-h)/kStageMassDivisor σ :=
    div_pos (D.cdf_pos (by linarith [hs.1])) hc0
  have ha1 : α (r-h)/kStageMassDivisor σ≤1 :=
    (div_le_self (cdf_nonneg _ _) hc).trans (cdf_le_one _ _)
  have he : kStageMass (interpolatedProfile α (α (r-h)) lam) (r-h) h x σ =
      fun t => (1-lam)*(α (r-h)/kStageMassDivisor σ)+lam*(p0 t).1 := by
    funext t
    dsimp only [kStageMass,quadraticGridMass,interpolatedProfile,p0]
    ring
  constructor
  · change ContDiffAt ℝ 2 (fun t =>
      (kStageMass (interpolatedProfile α (α (r-h)) lam) (r-h) h x σ t,(p0 t).2)) k
    rw [he]
    exact (contDiffAt_const.add (contDiffAt_const.mul hp0c.fst)).prodMk hp0c.snd
  · change kStageMass (interpolatedProfile α (α (r-h)) lam) (r-h) h x σ k∈Ioc (0:ℝ) 1
    rw [he]
    have hlo : min (α (r-h)/kStageMassDivisor σ) a0 ≤
        (1-lam)*(α (r-h)/kStageMassDivisor σ)+lam*(p0 k).1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hlam.2)
        (sub_nonneg.mpr (min_le_left (α (r-h)/kStageMassDivisor σ) a0)),
        mul_nonneg hlam.1 (sub_nonneg.mpr
          ((min_le_right (α (r-h)/kStageMassDivisor σ) a0).trans hm0.1))]
    refine ⟨(lt_min hapos ha0).trans_le hlo,?_⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr hlam.2) (sub_nonneg.mpr ha1),
      mul_nonneg hlam.1 (sub_nonneg.mpr hm0.2)]

theorem massPath_window_drop_masses_mem {β a lam s h : ℝ} {α : ℝ → ℝ}
    (hα : ∀ t, α t∈Icc (0:ℝ) 1) (ha : a∈Icc (0:ℝ) 1) (hlam : lam∈Icc (0:ℝ) 1)
    (N j : ℕ) (k : ℝ) :
    ∀ p∈(massPath (windowMassPath β α a (1/2) s h k N) lam).drop j,
      p.1∈Icc (0:ℝ) 1 := by
  intro p hp
  have hp' := List.mem_of_mem_drop hp
  rw [massPath_window_eq] at hp'
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
  have hprofile (t : ℝ) : interpolatedProfile α a lam t∈Icc (0:ℝ) 1 := by
    dsimp only [interpolatedProfile]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hlam.2) ha.1,
      mul_nonneg hlam.1 (hα t).1,
      mul_le_mul_of_nonneg_left ha.2 (sub_nonneg.mpr hlam.2),
      mul_le_mul_of_nonneg_left (hα t).2 hlam.1]
  exact OW.window_mass_mem _ hprofile _ _ _ _ _ q hq

theorem terminal_observables_eventually_bounded {B k : ℝ} {f : E → ℝ}
    (hf : QPotential 5 B f) {w : ℝ → E} (hw : ContinuousAt w k) :
    (∀ᶠ t in 𝓝 k, QBoundedJets 4 (B*(‖w k‖+1)) (fun y => fderiv ℝ f y (w t))) ∧
    (∀ᶠ t in 𝓝 k, QBoundedJets 4 (16*(B*(‖w k‖+1))^2)
      (fun y => (fderiv ℝ f y (w t))^2)) := by
  have hb : ∀ᶠ t in 𝓝 k, ‖w t‖<‖w k‖+1 :=
    hw.norm.eventually (Iio_mem_nhds (by linarith : ‖w k‖<‖w k‖+1))
  have hg : ∀ᶠ t in 𝓝 k, QBoundedJets 4 (B*(‖w k‖+1))
      (fun y => fderiv ℝ f y (w t)) := by
    filter_upwards [hb] with t ht
    exact (hf.derivativeJets.apply_const (w t)).mono
      (mul_le_mul_of_nonneg_left ht.le hf.nonneg)
  refine ⟨hg,?_⟩
  filter_upwards [hg] with t ht
  convert ht.mul ht using 1
  · norm_num
    ring
  · funext y
    ring

end SKBarriers2.Corner

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def PathDefectRecursionC2At (p : ℝ → ℝ × E) (l : ℝ → List (ℝ × E))
    (f : E → ℝ) (g : ℝ → E → ℝ) (x : E) (k : ℝ) : Prop :=
  ContDiffAt ℝ 2 (fun t => tiltedPathTaylorDefect (p t::l t) f (g t) x) k ∧
    iteratedDeriv 2 (fun t => tiltedPathTaylorDefect (p t::l t) f (g t) x) k =
      ∑ i : Fin 4, iteratedDeriv 2 (fun t => tiltedPathDefectTerms (p t) (l t) f (g t) x i) k

theorem orderedCurve_pathDefect_recursion_c2 {B k : ℝ} {f : E → ℝ}
    (hf : QPotential 5 B f) (ps : List (ℝ → ℝ × E)) (j : Fin ps.length)
    (w : ℝ → E) (hw : ContDiffAt ℝ 2 w k)
    (hreg : ∀ p∈ps, ContDiffAt ℝ 2 p k) (hpos : ∀ p∈ps, 0<(p k).1)
    (hmass : ∀ t : ℝ, ∀ p∈ps.map (fun q => q t), p.1∈Icc (0:ℝ) 1)
    (x : E) (square : Bool) :
    PathDefectRecursionC2At (ps.get j) (fun t => (ps.map (fun p => p t)).drop (j.val+1)) f
      (fun t y => if square then (fderiv ℝ f y (w t))^2 else fderiv ℝ f y (w t)) x k := by
  have hterms (i : Fin 4) := ParamChain.contDiffAt_orderedCurveDefectTerms_terminal
    hf ps j w hw hreg hpos x i
  obtain ⟨hg,hgsq⟩ := Corner.terminal_observables_eventually_bounded hf hw.continuousAt
  cases square
  · apply tiltedPathTaylorDefect_cons_iteratedDeriv_two (C := B*(‖w k‖+1)) hf (ps.get j)
      (fun t => (ps.map (fun p => p t)).drop (j.val+1))
      (fun t y => fderiv ℝ f y (w t)) _ x (fun i => (hterms i).1)
    filter_upwards [hg] with t ht
    exact ⟨ht,fun p hp => hmass t p (List.mem_of_mem_drop hp)⟩
  · apply tiltedPathTaylorDefect_cons_iteratedDeriv_two
      (C := 16*(B*(‖w k‖+1))^2) hf (ps.get j)
      (fun t => (ps.map (fun p => p t)).drop (j.val+1))
      (fun t y => (fderiv ℝ f y (w t))^2) _ x (fun i => (hterms i).2)
    filter_upwards [hgsq] with t ht
    exact ⟨ht,fun p hp => hmass t p (List.mem_of_mem_drop hp)⟩

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

local notation "E" => (Fin 3 → ℝ)

theorem scalarData_window_pathDefect_recursion_c2 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0<l) (hlu : l≤u) (hu : u<D.q) :
    ∃ h0 : ℝ, 0<h0 ∧ ∀ r∈Icc l u, ∀ h : ℝ, 0<h → h≤h0 →
      ∀ N : ℕ, 1≤N → ∀ lam∈Icc (0:ℝ) 1, ∀ j b : Fin (12*N),
        ∀ k : ℝ, |k|≤1/2 → ∀ x : E, ∀ square : Bool,
          StepCalculus.PathDefectRecursionC2At
            (orderedWindowCurve β (cdf (D.μ : Measure ℝ))
              (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h N lam j)
            (fun t => (massPath (windowMassPath β (cdf (D.μ : Measure ℝ))
              (cdf (D.μ : Measure ℝ) (r-h)) (1/2) (r-h) h t N) lam).drop (j.val+1))
            (massVariationTerminal β (cdf (D.μ : Measure ℝ)) (r-h) h)
            (fun t y => if square then
              (fderiv ℝ (massVariationTerminal β (cdf (D.μ : Measure ℝ)) (r-h) h) y
                (orderedWindowCurve β (cdf (D.μ : Measure ℝ))
                  (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h N lam b t).2)^2
              else fderiv ℝ (massVariationTerminal β (cdf (D.μ : Measure ℝ)) (r-h) h) y
                (orderedWindowCurve β (cdf (D.μ : Measure ℝ))
                  (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h N lam b t).2) x k := by
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  obtain ⟨hP,hhP,hparam⟩ := scalarData_interpolated_window_curve_regular D hl hlu hu
  refine ⟨min hP (kStabilityInteriorRadius D.q l u),
    lt_min hhP (kStabilityInteriorRadius_pos hl hu),?_⟩
  intro r hr h hh hh0 N hN lam hlam j b k hk x square
  have hhP' := hh0.trans (min_le_left _ _)
  have hhI := hh0.trans (min_le_right _ _)
  have htime := kStability_time_mem hr hh.le hhI (show (4:ℝ)∈Icc (0:ℝ) 4 by norm_num)
  have ht : (r-h)+4*h∈Icc (0:ℝ) 1 := by
    constructor <;> linarith [htime.1,htime.2,D.q_mem.2]
  let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
  let jj : Fin ps.length := ⟨j.val,by rw [windowKCurves_length]; exact j.isLt⟩
  let w : ℝ → E := fun t => (orderedWindowCurve β α (α (r-h)) (r-h) h N lam b t).2
  have hreg : ∀ p∈ps, ContDiffAt ℝ 2 p k :=
    fun p hp => (hparam r hr h hh hhP' N hN lam hlam p hp k hk).1
  have hpos : ∀ p∈ps, 0<(p k).1 :=
    fun p hp => (hparam r hr h hh hhP' N hN lam hlam p hp k hk).2.1
  have hw : ContDiffAt ℝ 2 w k :=
    (hreg _ (orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam b)).snd
  have hpath (t : ℝ) : ps.map (fun p => p t) =
      massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N) lam := by
    dsimp only [ps]
    rw [windowKCurves_apply β _ (r-h) h t N hh.le, massPath_window_eq]
  have hmass (t : ℝ) : ∀ p∈ps.map (fun q => q t), p.1∈Icc (0:ℝ) 1 := by
    rw [hpath]
    simpa only [List.drop_zero] using massPath_window_drop_masses_mem
      (β := β) (fun t => ⟨cdf_nonneg _ t,cdf_le_one _ t⟩)
      ⟨cdf_nonneg _ _,cdf_le_one _ _⟩ hlam N 0 t
  have H := StepCalculus.orderedCurve_pathDefect_recursion_c2
    (scalarData_massVariationTerminal_qPotential D 5 ht) ps jj w hw hreg hpos hmass x square
  have he : (fun t => (ps.map (fun p => p t)).drop (jj.val+1)) =
      fun t => (massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N) lam).drop (j.val+1) := by
    funext t
    rw [hpath]
  rw [he] at H
  exact H

end SKBarriers2.Corner

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

theorem abs_direction_deriv_quadratic_remainder_le {B m k : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (hm : m∈Icc (0:ℝ) 1)
    {v : ℝ → E} {w : E} (hv : HasDerivAt v w k) (x : E) (hsize : ‖v k‖≤1) :
    |deriv (fun t => vectorStep m (v t) f x) k-directionSource m (v k) w f x| ≤
      ((B+4*B^2)*(1+B)^2)*‖v k‖^3*‖w‖ := by
  rw [(hasDerivAt_direction_curve hf (by norm_num) hv m x).deriv]
  have hs : QBoundedJets 2 ((B+4*B^2)*‖v k‖*‖w‖) (directionSource m (v k) w f) := by
    simpa only [show (2:ℝ)^2=4 from by norm_num] using qBoundedJets_directionSource hf hm (v k) w
  have H := abs_noiseMean_sub_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hs).potential le_rfl hm (v k) x hsize
  change |tiltedAverage m (v k) f (directionSource m (v k) w f) x-
    directionSource m (v k) w f x| ≤ _ at H
  exact H.trans_eq (by ring)

theorem abs_paramStep_deriv_quadratic_remainder_le {B a0 k dm : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (ha0 : 0<a0)
    {mass : ℝ → ℝ} {v : ℝ → E} {w : E}
    (hm : HasDerivAt mass dm k) (hv : HasDerivAt v w k)
    (hmrange : mass k∈Icc a0 1) (x : E) (hsize : ‖v k‖≤1) :
    |deriv (fun t => vectorStep (mass t) (v t) f x) k-
      dm*(fderiv ℝ f x (v k))^2/2-directionSource (mass k) (v k) w f x| ≤
      (2*B*pathExpansionConstant B/a0)*|dm| *‖v k‖^4+
        ((B+4*B^2)*(1+B)^2)*‖v k‖^3*‖w‖ := by
  have hmp : 0 < mass k := ha0.trans_le hmrange.1
  have hmass := abs_mass_deriv_remainder_le hf le_rfl ha0 hmrange (v k) x hsize
  have hdir := abs_direction_deriv_quadratic_remainder_le hf ⟨hmp.le,hmrange.2⟩ hv x hsize
  rw [(hasDerivAt_paramStep hf (by norm_num) hm hv hmp.ne' x).deriv]
  rw [(hasDerivAt_direction_curve hf (by norm_num) hv (mass k) x).deriv] at hdir
  have he : dm*deriv (fun m => vectorStep m (v k) f x) (mass k)+
      tiltedAverage (mass k) (v k) f (directionSource (mass k) (v k) w f) x-
      dm*(fderiv ℝ f x (v k))^2/2-directionSource (mass k) (v k) w f x =
      dm*(deriv (fun m => vectorStep m (v k) f x) (mass k)-(fderiv ℝ f x (v k))^2/2)+
        (tiltedAverage (mass k) (v k) f (directionSource (mass k) (v k) w f) x-
          directionSource (mass k) (v k) w f x) := by ring
  rw [he]
  calc
    _ ≤ |dm| *|deriv (fun m => vectorStep m (v k) f x) (mass k)-(fderiv ℝ f x (v k))^2/2|+
        |tiltedAverage (mass k) (v k) f (directionSource (mass k) (v k) w f) x-
          directionSource (mass k) (v k) w f x| := by
      have H := abs_add_le
        (dm*(deriv (fun m => vectorStep m (v k) f x) (mass k)-(fderiv ℝ f x (v k))^2/2))
        (tiltedAverage (mass k) (v k) f (directionSource (mass k) (v k) w f) x-
          directionSource (mass k) (v k) w f x)
      rw [abs_mul] at H
      exact H
    _ ≤ _ := (add_le_add (mul_le_mul_of_nonneg_left hmass (abs_nonneg dm)) hdir).trans_eq (by ring)

end SKBarriers2.StepCalculus
