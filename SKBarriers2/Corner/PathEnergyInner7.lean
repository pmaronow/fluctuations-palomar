module

public import SKBarriers2.Corner.PathEnergyInner6
public import SKBarriers2.Corner.PathEnergyInner5

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def chainHeadRemainder (f : E → ℝ) (p : ℝ → ℝ × E)
    (ps : List (ℝ → ℝ × E)) (x : E) (t : ℝ) : ℝ :=
  vectorIncrementChain ((p::ps).map (fun q => q t)) f x-
    vectorIncrementChain (ps.map (fun q => q t)) f x-
    stepQuadraticIncrement (p t).1 (p t).2 f x

def innerLocalTaylorCoefficient (B R a0 : ℝ) : ℝ :=
  B*pathExpansionConstant B+firstVariationValueCoefficient B R a0+
    |mixedStepUniformDefectCoefficient B R a0|

theorem innerLocalTaylorCoefficient_nonneg {B R a0 : ℝ}
    (hB : 0 ≤ B) (hR : 0 ≤ R) (ha0 : 0 < a0) :
    0 ≤ innerLocalTaylorCoefficient B R a0 := by
  have hP := pathExpansionConstant_nonneg hB
  have hF := firstVariationValueCoefficient_nonneg hB hR ha0
  dsimp only [innerLocalTaylorCoefficient]
  positivity

theorem abs_chainHeadRemainder_jets_le {B R a0 h d k : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (hR : 0 ≤ R) (ha0 : 0 < a0)
    (hh : 0 < h) (hh1 : h ≤ 1) (hRh : R*h ≤ 1) (hd : 0 ≤ d)
    (p : ℝ → ℝ × E) (ps : List (ℝ → ℝ × E))
    (hreg : ∀ q ∈ p::ps, ContDiffAt ℝ 2 q k)
    (hpos : ∀ q ∈ p::ps, 0 < (q k).1)
    (hF : QPotential 4 B (vectorIncrementChain (ps.map (fun q => q k)) f))
    (hδ : QBoundedJets 3 (R*h) (fun y =>
      vectorIncrementChain (ps.map (fun q => q k)) f y-f y))
    (hg : QBoundedJets 4 (R*h) (fun y => deriv (fun t =>
      vectorIncrementChain (ps.map (fun q => q t)) f y) k))
    (hq : QBoundedJets 4 (R*h) (fun y => deriv (deriv (fun t =>
      vectorIncrementChain (ps.map (fun q => q t)) f y)) k))
    (hm : (p k).1 ∈ Icc a0 1)
    (hdm : |deriv (fun t => (p t).1) k| ≤ 1)
    (hddm : |deriv (deriv (fun t => (p t).1)) k| ≤ 1)
    (hv : ‖(p k).2‖ ≤ d) (hw : ‖deriv (fun t => (p t).2) k‖ ≤ d)
    (hb : ‖deriv (deriv (fun t => (p t).2)) k‖ ≤ d)
    (hv1 : ‖(p k).2‖ ≤ 1) (x : E) (c : ℕ) (hc : c ≤ 2) :
    |iteratedDeriv c (chainHeadRemainder f p ps x) k| ≤
      (21*B+6)*R*h*d^2+innerLocalTaylorCoefficient B R a0*d^4 := by
  let F := vectorIncrementChain (ps.map (fun q => q k)) f
  let G := fun y => deriv (fun t => vectorIncrementChain (ps.map (fun q => q t)) f y) k
  let Q := fun y => deriv (deriv (fun t => vectorIncrementChain (ps.map (fun q => q t)) f y)) k
  let m := (p k).1
  let v := (p k).2
  let dm := deriv (fun t => (p t).1) k
  let ddm := deriv (deriv (fun t => (p t).1)) k
  let w := deriv (fun t => (p t).2) k
  let b := deriv (deriv (fun t => (p t).2)) k
  have hB := hf.nonneg
  have hmcc : m ∈ Icc (0:ℝ) 1 := ⟨(ha0.trans_le hm.1).le,hm.2⟩
  have hAR : R*h ≤ R := mul_le_of_le_one_right hR hh1
  have hP := pathExpansionConstant_nonneg hB
  have hV := firstVariationValueCoefficient_nonneg hB hR ha0
  have hchain : ContDiffAt ℝ 2 (fun t =>
      vectorIncrementChain ((p::ps).map (fun q => q t)) f x) k :=
    (ParamChain.contDiffAt_curveChain (p::ps) hf (by norm_num) hreg hpos x).comp k
      (contDiffAt_id.prodMk contDiffAt_const)
  have htail : ContDiffAt ℝ 2 (fun t =>
      vectorIncrementChain (ps.map (fun q => q t)) f x) k :=
    (ParamChain.contDiffAt_curveChain ps hf (by norm_num)
      (fun q hq => hreg q (by simp [hq]))
      (fun q hq => hpos q (by simp [hq])) x).comp k
        (contDiffAt_id.prodMk contDiffAt_const)
  have hpoly := contDiffAt_stepQuadraticIncrement (hf.of_le (by norm_num))
    (hreg p (by simp)) x
  have ht := curveChain_cons_twoJet hf p ps hreg hpos (hF.of_le (by norm_num))
    (hg.of_le (by norm_num)) (hq.of_le (by norm_num)) x
  have hp := stepQuadraticIncrement_twoJet (hf.of_le (by norm_num)) (hreg p (by simp)) x
  interval_cases c
  · rw [iteratedDeriv_zero]
    have hlocal := abs_step_generator_remainder_le hF le_rfl hmcc v x hv1
    have hcomp := abs_stepQuadraticIncrement_sub_le (hf.of_le (by norm_num))
      (hF.of_le (by norm_num)) (hδ.of_le (by norm_num)) hmcc v x
    have he : chainHeadRemainder f p ps x k =
        (vectorStep m v F x-F x-stepQuadraticIncrement m v F x)+
          (stepQuadraticIncrement m v F x-stepQuadraticIncrement m v f x) := by
      simp only [chainHeadRemainder,vectorIncrementChain,List.map_cons,F,m,v]
      ring
    rw [he]
    have hlocal' : |vectorStep m v F x-F x-stepQuadraticIncrement m v F x| ≤
        B*pathExpansionConstant B*d^4 := by
      convert hlocal.trans (by gcongr : B*pathExpansionConstant B*‖v‖^4 ≤
        B*pathExpansionConstant B*d^4) using 1
      congr 1
      dsimp only [stepQuadraticIncrement]
      ring
    calc
      _ ≤ B*pathExpansionConstant B*d^4+(B+1)*(R*h)*d^2 :=
        (abs_add_le _ _).trans (add_le_add hlocal' (hcomp.trans (by gcongr)))
      _ ≤ _ := by
        dsimp only [innerLocalTaylorCoefficient]
        nlinarith only [mul_nonneg (by positivity : 0 ≤ (20*B+5)*R*h) (sq_nonneg d),
          mul_nonneg hV (pow_nonneg hd 4),
          mul_nonneg (abs_nonneg (mixedStepUniformDefectCoefficient B R a0)) (pow_nonneg hd 4)]
  · have he : iteratedDeriv 1 (chainHeadRemainder f p ps x) k =
        firstVariationStep m v F G dm w x-G x-
          stepQuadraticFirstSource m v f (fun _ => 0) dm w x := by
      rw [iteratedDeriv_one]
      change deriv (fun t => vectorIncrementChain ((p::ps).map (fun q => q t)) f x-
        vectorIncrementChain (ps.map (fun q => q t)) f x-
        stepQuadraticIncrement (p t).1 (p t).2 f x) k = _
      rw [deriv_fun_sub
        (f := fun t => vectorIncrementChain ((p::ps).map (fun q => q t)) f x-
          vectorIncrementChain (ps.map (fun q => q t)) f x)
        (g := fun t => stepQuadraticIncrement (p t).1 (p t).2 f x)
        ((hchain.differentiableAt (by norm_num)).sub
          (htail.differentiableAt (by norm_num))) (hpoly.differentiableAt (by norm_num)),
        deriv_fun_sub (hchain.differentiableAt (by norm_num)) (htail.differentiableAt (by norm_num)),
        ht.1,hp.1]
    rw [he]
    have hlocal := abs_firstVariationTaylorDefect_le hF hg hAR ha0 hm hdm hd v w x hv hw hv1
    have hcomp := abs_stepQuadraticFirstSource_sub_terminal_le hf hF hδ hg hmcc hdm hd x v w hv hw
    have he' : firstVariationStep m v F G dm w x-G x-
        stepQuadraticFirstSource m v f (fun _ => 0) dm w x =
        firstVariationTaylorDefect m v F G dm w x+
          (stepQuadraticFirstSource m v F G dm w x-G x-
            stepQuadraticFirstSource m v f (fun _ => 0) dm w x) := by
      dsimp only [firstVariationTaylorDefect]
      ring
    rw [he']
    calc
      _ ≤ firstVariationValueCoefficient B R a0*d^4+
          ((4*B+1)*(R*h)+(1+3*B)*(R*h))*d^2 :=
        (abs_add_le _ _).trans (add_le_add hlocal hcomp)
      _ ≤ _ := by
        dsimp only [innerLocalTaylorCoefficient]
        nlinarith only [mul_nonneg (by positivity : 0 ≤ (14*B+4)*R*h) (sq_nonneg d),
          mul_nonneg (mul_nonneg hB hP) (pow_nonneg hd 4),
          mul_nonneg (abs_nonneg (mixedStepUniformDefectCoefficient B R a0)) (pow_nonneg hd 4)]
  · have he : iteratedDeriv 2 (chainHeadRemainder f p ps x) k =
        secondVariationStep m v F G Q dm ddm w b x-Q x-
          stepQuadraticSecondSource m v f (fun _ => 0) (fun _ => 0) dm ddm w b x := by
      change iteratedDeriv 2 (fun t => vectorIncrementChain ((p::ps).map (fun q => q t)) f x-
        vectorIncrementChain (ps.map (fun q => q t)) f x-
        stepQuadraticIncrement (p t).1 (p t).2 f x) k = _
      rw [iteratedDeriv_fun_sub
        (f := fun t => vectorIncrementChain ((p::ps).map (fun q => q t)) f x-
          vectorIncrementChain (ps.map (fun q => q t)) f x)
        (g := fun t => stepQuadraticIncrement (p t).1 (p t).2 f x)
        (hchain.sub htail) hpoly,
        iteratedDeriv_fun_sub hchain htail]
      simp only [iteratedDeriv_succ,iteratedDeriv_zero]
      rw [ht.2,hp.2]
    rw [he]
    have hlocal := abs_secondVariationStep_sub_quadratic_le hF hg hq ha0 hm
      dm ddm v w b x hv1
    have hbound := mixedStepDefectSecondBound_le hB hR hg.nonneg hq.nonneg hAR hAR
      ha0 hm.1 hdm hddm hd v w b hv hw hb
    have hlocal' : |secondVariationStep m v F G Q dm ddm w b x-
        stepQuadraticSecondSource m v F G Q dm ddm w b x| ≤
        |mixedStepUniformDefectCoefficient B R a0| * d^4 :=
      (hlocal.trans hbound).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hd 4))
    have hcomp := abs_stepQuadraticSecondSource_sub_terminal_le hf hF hδ hg hq hRh
      hmcc hdm hddm hd x v w b hv hw hb
    have he' : secondVariationStep m v F G Q dm ddm w b x-Q x-
        stepQuadraticSecondSource m v f (fun _ => 0) (fun _ => 0) dm ddm w b x =
        (secondVariationStep m v F G Q dm ddm w b x-
          stepQuadraticSecondSource m v F G Q dm ddm w b x)+
        (stepQuadraticSecondSource m v F G Q dm ddm w b x-Q x-
          stepQuadraticSecondSource m v f (fun _ => 0) (fun _ => 0) dm ddm w b x) := by ring
    rw [he']
    calc
      _ ≤ |mixedStepUniformDefectCoefficient B R a0| * d^4+(21*B+6)*(R*h)*d^2 :=
        (abs_add_le _ _).trans (add_le_add hlocal' hcomp)
      _ ≤ _ := by
        dsimp only [innerLocalTaylorCoefficient]
        nlinarith only [mul_nonneg (mul_nonneg hB hP) (pow_nonneg hd 4),
          mul_nonneg hV (pow_nonneg hd 4)]

theorem contDiffAt_chainFirstOrderRemainder {B : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (ps : List (ℝ → ℝ × E)) {k : ℝ}
    (hreg : ∀ q ∈ ps, ContDiffAt ℝ 2 q k)
    (hpos : ∀ q ∈ ps, 0 < (q k).1) (x : E) :
    ContDiffAt ℝ 2 (fun t => chainFirstOrderRemainder f (ps.map (fun q => q t)) x) k := by
  have hchain := (ParamChain.contDiffAt_curveChain ps hf (by norm_num)
    hreg hpos x).comp k (contDiffAt_id.prodMk contDiffAt_const)
  exact (hchain.sub contDiffAt_const).sub
    (contDiffAt_pathQuadraticSum (hf.of_le (by norm_num)) ps hreg x)

theorem abs_chainFirstOrderRemainder_jets_le_of_local {B J k : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (ps : List (ℝ → ℝ × E))
    (hreg : ∀ q ∈ ps, ContDiffAt ℝ 2 q k)
    (hpos : ∀ q ∈ ps, 0 < (q k).1)
    (hlocal : ∀ front p tail, ps = front++p::tail → ∀ x : E,
      ∀ c : ℕ, c ≤ 2 → |iteratedDeriv c (chainHeadRemainder f p tail x) k| ≤ J)
    (x : E) (c : ℕ) (hc : c ≤ 2) :
    |iteratedDeriv c (fun t => chainFirstOrderRemainder f (ps.map (fun q => q t)) x) k| ≤
      (ps.length:ℝ)*J := by
  induction ps with
  | nil =>
    have he : (fun t => chainFirstOrderRemainder f ([].map (fun q : ℝ → ℝ × E => q t)) x) =
        fun _ => (0:ℝ) := by
      funext t
      simp [chainFirstOrderRemainder,pathQuadraticSum,vectorIncrementChain]
    rw [he]
    simp
  | cons p ps ih =>
    have hregT : ∀ q ∈ ps, ContDiffAt ℝ 2 q k := fun q hq => hreg q (by simp [hq])
    have hposT : ∀ q ∈ ps, 0 < (q k).1 := fun q hq => hpos q (by simp [hq])
    have hlocalT : ∀ front q tail, ps = front++q::tail → ∀ x : E,
        ∀ c : ℕ, c ≤ 2 → |iteratedDeriv c (chainHeadRemainder f q tail x) k| ≤ J := by
      intro front q tail he y a ha
      apply hlocal (p::front) q tail
      · simpa only [List.cons_append] using congrArg (List.cons p) he
      · exact ha
    have htail := ih hregT hposT hlocalT
    have hhead := hlocal [] p ps rfl x c hc
    have hchain : ContDiffAt ℝ 2 (fun t =>
        vectorIncrementChain ((p::ps).map (fun q => q t)) f x) k :=
      (ParamChain.contDiffAt_curveChain (p::ps) hf (by norm_num)
        hreg hpos x).comp k (contDiffAt_id.prodMk contDiffAt_const)
    have hchainT : ContDiffAt ℝ 2 (fun t =>
        vectorIncrementChain (ps.map (fun q => q t)) f x) k :=
      (ParamChain.contDiffAt_curveChain ps hf (by norm_num)
        hregT hposT x).comp k (contDiffAt_id.prodMk contDiffAt_const)
    have hH : ContDiffAt ℝ 2 (chainHeadRemainder f p ps x) k :=
      (hchain.sub hchainT).sub
        (contDiffAt_stepQuadraticIncrement (hf.of_le (by norm_num)) (hreg p (by simp)) x)
    have hT := contDiffAt_chainFirstOrderRemainder hf ps hregT hposT x
    have he : (fun t => chainFirstOrderRemainder f ((p::ps).map (fun q => q t)) x) =
        fun t => chainHeadRemainder f p ps x t+
          chainFirstOrderRemainder f (ps.map (fun q => q t)) x := by
      funext t
      simp only [chainFirstOrderRemainder,chainHeadRemainder,List.map_cons,pathQuadraticSum]
      ring
    rw [he,iteratedDeriv_fun_add (hH.of_le (by exact_mod_cast hc))
      (hT.of_le (by exact_mod_cast hc))]
    calc
      _ ≤ |iteratedDeriv c (chainHeadRemainder f p ps x) k|+
          |iteratedDeriv c (fun t => chainFirstOrderRemainder f (ps.map (fun q => q t)) x) k| :=
        abs_add_le _ _
      _ ≤ J+(ps.length:ℝ)*J := add_le_add hhead htail
      _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

end SKBarriers2.StepCalculus
