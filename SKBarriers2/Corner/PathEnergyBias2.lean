module

public import SKBarriers2.Corner.PathEnergyBias
public import SKBarriers2.Corner.PathEnergyRecursions3

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.Corner

open StepCalculus ParamChain
local notation "E" => (Fin 3 → ℝ)
local notation "Curve" => (ℝ → ℝ × E)

def curveInnerCorrection (middle : List Curve) (f : E → ℝ) (w : ℝ → E)
    (t : ℝ) (x : E) : ℝ :=
  (fderiv ℝ (vectorIncrementChain ((middle.drop 1).map (fun q => q t)) f) x (w t))^2-
    (fderiv ℝ f x (w t))^2

def curveInnerBias (front middle : List Curve) (f : E → ℝ) (w : ℝ → E)
    (t : ℝ) (x : E) : ℝ :=
  vectorIncrementAverage (front.map (fun q => q t))
    (vectorIncrementChain (middle.map (fun q => q t)) f)
    (curveInnerCorrection middle f w t) x-curveInnerCorrection middle f w t x

private theorem familyJet_congr {F G : ℝ → E → ℝ} {k : ℝ}
    (h : F =ᶠ[𝓝 k] G) (n : ℕ) :
    (fun x => iteratedDeriv n (fun t => F t x) k) =
      fun x => iteratedDeriv n (fun t => G t x) k := by
  funext x
  exact Filter.EventuallyEq.iteratedDeriv_eq n (h.mono (fun _ ht => congrFun ht x))

private theorem curveMasses_eventually_positive (ps : List Curve) {k : ℝ}
    (hreg : ∀ q ∈ ps, ContDiffAt ℝ 2 q k) (hpos : ∀ q ∈ ps, 0 < (q k).1) :
    ∀ᶠ t in 𝓝 k, ∀ q ∈ ps, 0 < (q t).1 := by
  have hget : ∀ᶠ t in 𝓝 k, ∀ i : Fin ps.length, 0 < (ps.get i t).1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hreg _ (List.get_mem ps i)).fst.continuousAt.eventually
      (Ioi_mem_nhds (hpos _ (List.get_mem ps i)))
  filter_upwards [hget] with t ht q hq
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hq
  exact ht i

set_option maxHeartbeats 800000 in
theorem curveInnerBias_step_jets {f : E → ℝ} {B₀ B R K D e a b c k Cδ Aδ : ℝ}
    (hf : QPotential 5 B₀ f) (q : Curve) (tail middle : List Curve) (w : ℝ → E)
    (hreg : ∀ p ∈ (q::tail)++middle, ContDiffAt ℝ 2 p k)
    (hpos : ∀ p ∈ (q::tail)++middle, 0 < (p k).1) (hw : ContDiffAt ℝ 2 w k)
    (hK : 0 ≤ K)
    (hK₄ : |tiltedStabilityCoefficient 4 B| ≤ K)
    (hK₂ : |tiltedStabilityCoefficient 2 B| ≤ K)
    (hK₁ : firstTiltedTransportCoefficient B R ≤ K)
    (hKS : secondAverageTransportCoefficient (secondMovingAverageScale B R R)
      (defectNoiseMomentBound 1 B) (defectNoiseMomentBound 2 B) (defectNoiseMomentBound 3 B) ≤ K)
    (hbase : QPotential 5 B (fun x => vectorIncrementChain ((tail++middle).map (fun q => q k)) f x))
    (hbase₁ : QBoundedJets 3 R (fun x => deriv (fun t => vectorIncrementChain
      ((tail++middle).map (fun q => q t)) f x) k))
    (hbase₂ : QBoundedJets 1 R (fun x => deriv (deriv (fun t => vectorIncrementChain
      ((tail++middle).map (fun q => q t)) f x)) k))
    (hm : (q k).1 ≤ 1) (hdm : |deriv (fun t => (q t).1) k| ≤ 1)
    (hddm : |deriv (deriv (fun t => (q t).1)) k| ≤ 1)
    (hv : ‖(q k).2‖ ≤ 1) (hsmall : (q k).1*(B*‖(q k).2‖^2) ≤ 1/2)
    (henergy : ‖(q k).2‖^2+‖deriv (fun t => (q t).2) k‖^2+
      ‖deriv (deriv (fun t => (q t).2)) k‖^2 ≤ e) (he1 : e ≤ 1)
    (htail : QBoundedJets 4 a (curveInnerBias tail middle f w k))
    (htail₁ : QBoundedJets 2 b (fun x => deriv (fun t => curveInnerBias tail middle f w t x) k))
    (htail₂ : QBoundedJets 0 c (fun x => deriv (deriv (fun t => curveInnerBias tail middle f w t x)) k))
    (hdelta : QBoundedJets 3 Cδ (curveInnerCorrection middle f w k))
    (hdelta₁ : QBoundedJets 1 Aδ (fun x => deriv (fun t => curveInnerCorrection middle f w t x) k))
    (hsource :
      let H := fun t x => vectorIncrementChain ((tail++middle).map (fun p => p t)) f x
      let H₁ := fun x => deriv (fun t => H t x) k
      let H₂ := fun x => deriv (deriv (fun t => H t x)) k
      let g := curveInnerCorrection middle f w k
      let a := fun x => deriv (fun t => curveInnerCorrection middle f w t x) k
      let d := fun x => deriv (deriv (fun t => curveInnerCorrection middle f w t x)) k
      let dm := deriv (fun t => (q t).1) k
      let ddm := deriv (deriv (fun t => (q t).1)) k
      let v := (q k).2
      let v₁ := deriv (fun t => (q t).2) k
      let v₂ := deriv (deriv (fun t => (q t).2)) k
      QBoundedJets 4 (D*e) (fun x => tiltedAverage (q k).1 v (H k) g x-g x) ∧
        QBoundedJets 2 (D*e) (fun x => firstTiltedAverageSource (q k).1 v (H k) H₁ g a dm v₁ x-a x) ∧
        ∀ x, |secondMovingAverageSource (q k).1 dm ddm v v₁ v₂ (H k) H₁ H₂ g a d x-d x| ≤ D*e) :
    (∀ x, ContDiffAt ℝ 2 (fun t => curveInnerBias (q::tail) middle f w t x) k) ∧
    QBoundedJets 4 ((1+K*e)*a+D*e) (curveInnerBias (q::tail) middle f w k) ∧
      QBoundedJets 2 ((1+K*e)*b+K*e*a+D*e)
        (fun x => deriv (fun t => curveInnerBias (q::tail) middle f w t x) k) ∧
      QBoundedJets 0 ((1+K*e)*c+K*e*(a+b)+D*e)
        (fun x => deriv (deriv (fun t => curveInnerBias (q::tail) middle f w t x)) k) := by
  let ss := (q::tail)++middle
  let P := Coordinates ss.length E × E
  let L : P →L[ℝ] Coordinates ss.length E := ContinuousLinearMap.fst ℝ _ _
  let W : P →L[ℝ] E := ContinuousLinearMap.snd ℝ _ _
  let liftStep := fun p : (Coordinates ss.length E →L[ℝ] ℝ) ×
      (Coordinates ss.length E →L[ℝ] E) => (p.1.comp L,p.2.comp L)
  let us := (coordinateSteps (X := E) ss.length).map liftStep
  let Q : ℝ → P := fun t => (logParameters ss t,w t)
  have hQ : ContDiffAt ℝ 2 Q k := (logParameters_contDiffAt ss hreg hpos).prodMk hw
  have hnear := curveMasses_eventually_positive ss hreg hpos
  have hus (t : ℝ) (ht : ∀ p ∈ ss, 0 < (p t).1) :
      exponentialSteps us (Q t) = ss.map (fun p => p t) := by
    have H := coordinateSteps_apply ss t ht
    dsimp only [us,exponentialSteps]
    rw [List.map_map]
    exact H
  have hlen : us.length = ss.length := by simp only [us,List.length_map,coordinateSteps,List.length_ofFn]
  have husne : us ≠ [] := by
    intro h
    have H := congrArg List.length h
    rw [hlen] at H
    simp only [ss,List.length_append,List.length_cons,List.length_nil] at H
    omega
  obtain ⟨z,zs,huz⟩ := List.exists_cons_of_ne_nil husne
  let F := exponentialChain (zs.drop tail.length) (fun z : P × E => f z.2)
  let G := fun z : P × E =>
    (fderiv ℝ (vectorIncrementChain (exponentialSteps (zs.drop (tail.length+1)) z.1) f)
      z.2 (W z.1))^2-(fderiv ℝ f z.2 (W z.1))^2
  have hF : ParamRegular F := regular_exponentialChain _ (regular_fixedTerminal hf (by norm_num) P)
  have hG : ParamSmooth G := smooth_exponentialGradientCorrection hf W _
  have hgeom : ∀ᶠ t in 𝓝 k,
      (Real.exp (z.1 (Q t)),z.2 (Q t)) = q t ∧
      exponentialSteps (zs.take tail.length) (Q t) = tail.map (fun p => p t) ∧
      exponentialSteps (zs.drop tail.length) (Q t) = middle.map (fun p => p t) ∧
      exponentialSteps (zs.drop (tail.length+1)) (Q t) = (middle.drop 1).map (fun p => p t) := by
    filter_upwards [hnear] with t ht
    have H := hus t ht
    rw [huz] at H
    simp only [ss,exponentialSteps,List.map_cons,List.map_append,List.cons_append] at H
    have hh := congrArg (fun l : List (ℝ × E) => l.headD (0,0)) H
    have htl := congrArg List.tail H
    simp only [List.headD_cons,List.tail_cons] at hh htl
    refine ⟨hh,?_,?_,?_⟩
    · have HH := congrArg (List.take tail.length) htl
      rw [show tail.length = (tail.map (fun p => p t)).length by simp,List.take_left] at HH
      simpa only [List.map_take,List.length_map,exponentialSteps] using HH
    · have HH := congrArg (List.drop tail.length) htl
      rw [show tail.length = (tail.map (fun p => p t)).length by simp,List.drop_left] at HH
      simpa only [List.map_drop,List.length_map,exponentialSteps] using HH
    · have HH := congrArg (List.drop (tail.length+1)) htl
      have HR : ((tail.map (fun p => p t))++middle.map (fun p => p t)).drop (tail.length+1) =
          (middle.drop 1).map (fun p => p t) := by
        rw [List.drop_append,List.drop_eq_nil_iff.mpr (by simp)]
        simp only [List.length_map,show tail.length+1-tail.length=1 by omega,List.nil_append,List.map_drop]
      rw [HR] at HH
      simpa only [List.map_drop,exponentialSteps] using HH
  have hbackground : (fun t x => exponentialChain (zs.take tail.length) F (Q t,x)) =ᶠ[𝓝 k]
      fun t x => vectorIncrementChain ((tail++middle).map (fun p => p t)) f x := by
    filter_upwards [hgeom] with t ht
    funext x
    dsimp only [F,exponentialChain]
    rw [ht.2.1,ht.2.2.1,List.map_append,vectorIncrementChain_append]
  have hcorrection : (fun t x => G (Q t,x)) =ᶠ[𝓝 k] curveInnerCorrection middle f w := by
    filter_upwards [hgeom] with t ht
    funext x
    dsimp only [G,curveInnerCorrection,W,Q]
    rw [ht.2.2.2]
    rfl
  have htailRep : (fun t x => exponentialBias (zs.take tail.length) F G (Q t,x)) =ᶠ[𝓝 k]
      curveInnerBias tail middle f w := by
    filter_upwards [hgeom,hcorrection] with t ht hct
    funext x
    dsimp only [exponentialBias,exponentialAverage,curveInnerBias,F,exponentialChain]
    rw [ht.2.1,ht.2.2.1,hct,congrFun hct x]
  have hconsRep : (fun t x => exponentialBias (z::zs.take tail.length) F G (Q t,x)) =ᶠ[𝓝 k]
      curveInnerBias (q::tail) middle f w := by
    filter_upwards [hgeom,hcorrection] with t ht hct
    funext x
    have HP : exponentialSteps (z::zs.take tail.length) (Q t) =
        (q t)::tail.map (fun p => p t) := by
      simp only [exponentialSteps,List.map_cons]
      change (Real.exp (z.1 (Q t)),z.2 (Q t))::exponentialSteps (zs.take tail.length) (Q t) = _
      rw [ht.1,ht.2.1]
    dsimp only [exponentialBias,exponentialAverage,curveInnerBias,F,exponentialChain]
    rw [HP,ht.2.2.1,hct,congrFun hct x]
    rfl
  have hmass : (fun t => Real.exp (z.1 (Q t))) =ᶠ[𝓝 k] fun t => (q t).1 :=
    hgeom.mono (fun _ ht => congrArg Prod.fst ht.1)
  have hdir : (fun t => z.2 (Q t)) =ᶠ[𝓝 k] fun t => (q t).2 :=
    hgeom.mono (fun _ ht => congrArg Prod.snd ht.1)
  have hm0 : Real.exp (z.1 (Q k)) = (q k).1 := hmass.self_of_nhds
  have hv0 : z.2 (Q k) = (q k).2 := hdir.self_of_nhds
  have hbg0 : (fun x => exponentialChain (zs.take tail.length) F (Q k,x)) =
      vectorIncrementChain ((tail++middle).map (fun p => p k)) f := hbackground.self_of_nhds
  have hcor0 : (fun x => G (Q k,x)) = curveInnerCorrection middle f w k :=
    hcorrection.self_of_nhds
  have hmass₂ := hmass.iteratedDeriv_eq 2
  have hdir₂ := hdir.iteratedDeriv_eq 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hmass₂ hdir₂
  have hbg₁ := familyJet_congr hbackground 1
  have hbg₂ := familyJet_congr hbackground 2
  have htail₁eq := familyJet_congr htailRep 1
  have htail₂eq := familyJet_congr htailRep 2
  have hcons₁eq := familyJet_congr hconsRep 1
  have hcons₂eq := familyJet_congr hconsRep 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hbg₁ hbg₂ htail₁eq htail₂eq hcons₁eq hcons₂eq
  have hlocal : (fun t x => tiltedAverage (Real.exp (z.1 (Q t))) (z.2 (Q t))
      (fun y => exponentialChain (zs.take tail.length) F (Q t,y)) (fun y => G (Q t,y)) x-G (Q t,x)) =ᶠ[𝓝 k]
      fun t x => tiltedAverage (q t).1 (q t).2
        (vectorIncrementChain ((tail++middle).map (fun p => p t)) f)
        (curveInnerCorrection middle f w t) x-curveInnerCorrection middle f w t x := by
    filter_upwards [hgeom,hbackground,hcorrection] with t ht hbt hct
    funext x
    have hm' : Real.exp (z.1 (Q t)) = (q t).1 := congrArg Prod.fst ht.1
    have hv' : z.2 (Q t) = (q t).2 := congrArg Prod.snd ht.1
    rw [hm',hv',hbt,hct,congrFun hct x]
  have hcor₁ := familyJet_congr hcorrection 1
  have hcor₂ := familyJet_congr hcorrection 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hcor₁ hcor₂
  let H := exponentialChain (zs.take tail.length) F
  have hH : ParamRegular H := regular_exponentialChain _ hF
  have haverage (x : E) := chartAverage_twoJet hH hG z.1 z.2
    (p := Q) (k := k) (B := B) (A := R) (C := Cδ) (D := Aδ) hQ
    (by simpa only [H,hbackground.self_of_nhds] using hbase.of_le (by norm_num : 4 ≤ 5))
    (by simpa only [H,hbg₁] using hbase₁)
    (by simpa only [hcorrection.self_of_nhds] using hdelta)
    (by simpa only [hcor₁] using hdelta₁)
    (by simpa only [hmass.self_of_nhds] using hm) x
  dsimp only at haverage
  let J := fun z' : P × E => tiltedAverage (Real.exp (z.1 z'.1)) (z.2 z'.1)
    (fun y => H (z'.1,y)) (fun y => G (z'.1,y)) z'.2-G z'
  have hJ : ParamSmooth J := by
    convert (smooth_movingAverage hH hG z.1 z.2).add (hG.const_mul (-1)) using 1
    funext z'
    simp only [J,tiltedAverage_eq_vectorStepAverage_fun]
    ring
  have hGc (x : E) : ContDiffAt ℝ 2 (fun t => G (Q t,x)) k :=
    (hG.1.contDiffAt (x := (Q k,x))).comp (f := fun t : ℝ => (Q t,x)) k
      (hQ.prodMk (contDiffAt_const (c := x)))
  have hlocalFirst (x : E) : deriv (fun t => J (Q t,x)) k =
      firstTiltedAverageSource (q k).1 (q k).2
        (vectorIncrementChain ((tail++middle).map (fun p => p k)) f)
        (fun y => deriv (fun t => vectorIncrementChain ((tail++middle).map (fun p => p t)) f y) k)
        (curveInnerCorrection middle f w k)
        (fun y => deriv (fun t => curveInnerCorrection middle f w t y) k)
        (deriv (fun t => (q t).1) k) (deriv (fun t => (q t).2) k) x-
      deriv (fun t => curveInnerCorrection middle f w t x) k := by
    rw [show (fun t => J (Q t,x)) = fun t =>
      tiltedAverage (Real.exp (z.1 (Q t))) (z.2 (Q t))
        (fun y => H (Q t,y)) (fun y => G (Q t,y)) x-G (Q t,x) from rfl,
      deriv_fun_sub ((haverage x).1.differentiableAt (by norm_num)) ((hGc x).differentiableAt (by norm_num)),
      (haverage x).2.1]
    dsimp only [H]
    rw [congrFun hcor₁ x,hm0,hmass.deriv_eq,hv0,hdir.deriv_eq,
      hbg0,hbg₁,hcor0,hcor₁]
  have hlocalSecond (x : E) : deriv (deriv (fun t => J (Q t,x))) k =
      secondMovingAverageSource (q k).1 (deriv (fun t => (q t).1) k)
        (deriv (deriv (fun t => (q t).1)) k) (q k).2
        (deriv (fun t => (q t).2) k) (deriv (deriv (fun t => (q t).2)) k)
        (vectorIncrementChain ((tail++middle).map (fun p => p k)) f)
        (fun y => deriv (fun t => vectorIncrementChain ((tail++middle).map (fun p => p t)) f y) k)
        (fun y => deriv (deriv (fun t => vectorIncrementChain ((tail++middle).map (fun p => p t)) f y)) k)
        (curveInnerCorrection middle f w k)
        (fun y => deriv (fun t => curveInnerCorrection middle f w t y) k)
        (fun y => deriv (deriv (fun t => curveInnerCorrection middle f w t y)) k) x-
      deriv (deriv (fun t => curveInnerCorrection middle f w t x)) k := by
    have HS := iteratedDeriv_fun_sub (haverage x).1 (hGc x)
    simp only [iteratedDeriv_succ,iteratedDeriv_zero] at HS
    rw [show (fun t => J (Q t,x)) = fun t =>
      tiltedAverage (Real.exp (z.1 (Q t))) (z.2 (Q t))
        (fun y => H (Q t,y)) (fun y => G (Q t,y)) x-G (Q t,x) from rfl,HS,(haverage x).2.2]
    dsimp only [H]
    rw [congrFun hcor₂ x,hm0,hmass.deriv_eq,hmass₂,hv0,hdir.deriv_eq,hdir₂,
      hbg0,hbg₁,hbg₂,hcor0,hcor₁,hcor₂]
  have hlocalBound : QBoundedJets 4 (D*e) (fun x => J (Q k,x)) ∧
      QBoundedJets 2 (D*e) (fun x => deriv (fun t => J (Q t,x)) k) ∧
      QBoundedJets 0 (D*e) (fun x => deriv (deriv (fun t => J (Q t,x))) k) := by
    refine ⟨?_,?_,?_⟩
    · simpa only [J,H,hlocal.self_of_nhds] using hsource.1
    · simpa only [funext hlocalFirst] using hsource.2.1
    · refine ⟨hsource.1.nonneg,contDiff_zero.mpr (continuous_second_parameter_curve hJ.1 hQ),?_⟩
      intro n hn x
      have hn0 : n = 0 := by omega
      subst n
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,hlocalSecond] using hsource.2.2 x
  have H := exponentialBias_step_jets hF hG z (zs.take tail.length) hQ hK hK₄ hK₂ hK₁ hKS
    (by simpa only [hbackground.self_of_nhds] using hbase)
    (by simpa only [hbg₁] using hbase₁) (by simpa only [hbg₂] using hbase₂)
    (by simpa only [hmass.self_of_nhds] using hm)
    (by simpa only [hmass.deriv_eq] using hdm) (by simpa only [hmass₂] using hddm)
    (by simpa only [hdir.self_of_nhds] using hv)
    (by simpa only [hmass.self_of_nhds,hdir.self_of_nhds] using hsmall)
    (by simpa only [hdir.self_of_nhds,hdir.deriv_eq,hdir₂] using henergy) he1
    (by simpa only [htailRep.self_of_nhds] using htail)
    (by simpa only [htail₁eq] using htail₁) (by simpa only [htail₂eq] using htail₂)
    hlocalBound
  refine ⟨?_,?_⟩
  · intro x
    have HC := ((smooth_exponentialBias hF hG (z::zs.take tail.length)).1.contDiffAt
      (x := (Q k,x))).comp (f := fun t : ℝ => (Q t,x)) k
      (hQ.prodMk (contDiffAt_const (c := x)))
    exact HC.congr_of_eventuallyEq (Filter.EventuallyEq.symm (hconsRep.mono (fun _ ht => congrFun ht x)))
  · simpa only [hconsRep.self_of_nhds,hcons₁eq,hcons₂eq] using H

theorem movingPrefix_c2BoundAt_of_regular_steps (qs : List Curve)
    (R : List Curve → ℝ → E → ℝ) (e : Curve → ℝ) {K D k : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (he : ∀ q ∈ qs, 0 ≤ e q)
    (hzero : ∀ t x, R [] t x = 0)
    (hsmall : 2*K*variationEnergy e qs ≤ 1)
    (hstep : ∀ front q tail, qs = front++q::tail → ∀ a b c : ℝ,
      QBoundedJets 4 a (R tail k) →
      QBoundedJets 2 b (fun x => deriv (fun t => R tail t x) k) →
      QBoundedJets 0 c (fun x => deriv (deriv (fun t => R tail t x)) k) →
      (∀ x, ContDiffAt ℝ 2 (fun t => R (q::tail) t x) k) ∧
      QBoundedJets 4 ((1+K*e q)*a+D*e q) (R (q::tail) k) ∧
        QBoundedJets 2 ((1+K*e q)*b+K*e q*a+D*e q)
          (fun x => deriv (fun t => R (q::tail) t x) k) ∧
        QBoundedJets 0 ((1+K*e q)*c+K*e q*(a+b)+D*e q)
          (fun x => deriv (deriv (fun t => R (q::tail) t x)) k)) :
    ∀ x, C2BoundAt (8*D*variationEnergy e qs) (fun t => R qs t x) k := by
  let env := fun tail : List Curve => tail.foldr (fun q (v : ℝ × ℝ × ℝ) =>
    ((1+K*e q)*v.1+D*e q,(1+K*e q)*v.2.1+K*e q*v.1+D*e q,
      (1+K*e q)*v.2.2+K*e q*(v.1+v.2.1)+D*e q)) (0,0,0)
  let a := fun tail => (env tail).1
  let b := fun tail => (env tail).2.1
  let c := fun tail => (env tail).2.2
  have hrec (q : Curve) (tail : List Curve) :
      a (q::tail) = (1+K*e q)*a tail+D*e q ∧
      b (q::tail) = (1+K*e q)*b tail+K*e q*a tail+D*e q ∧
      c (q::tail) = (1+K*e q)*c tail+K*e q*(a tail+b tail)+D*e q := ⟨rfl,rfl,rfl⟩
  have hzeroJets (n : ℕ) : QBoundedJets n 0 (fun _ : E => (0:ℝ)) := by
    refine ⟨le_rfl,contDiff_const,?_⟩
    intro j hj x
    simp
  have hz : R [] = fun _ _ => (0:ℝ) := funext (fun t => funext (fun x => hzero t x))
  have hjets (tail : List Curve) : ∀ front, qs = front++tail →
      (∀ x, ContDiffAt ℝ 2 (fun t => R tail t x) k) ∧
      QBoundedJets 4 (a tail) (R tail k) ∧
      QBoundedJets 2 (b tail) (fun x => deriv (fun t => R tail t x) k) ∧
      QBoundedJets 0 (c tail) (fun x => deriv (deriv (fun t => R tail t x)) k) := by
    induction tail with
    | nil =>
      intro front hfront
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [hz] using fun _ : E => (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ => (0:ℝ)) k)
      · simpa only [a,env,List.foldr_nil,hz] using hzeroJets 4
      · simpa only [b,env,List.foldr_nil,hz,deriv_const'] using hzeroJets 2
      · simpa only [c,env,List.foldr_nil,hz,deriv_const'] using hzeroJets 0
    | cons q tail ih =>
      intro front hfront
      have ht : qs = (front++[q])++tail := by simpa only [List.append_assoc,List.singleton_append] using hfront
      obtain ⟨_,ha,hb,hc⟩ := ih (front++[q]) ht
      exact hstep front q tail hfront (a tail) (b tail) (c tail) ha hb hc
  have hn := pathEnergy_three_level_recursion_le hK hD a b c qs he le_rfl le_rfl le_rfl
    (fun _ q tail _ => (hrec q tail).1.le)
    (fun _ q tail _ => (hrec q tail).2.1.le)
    (fun _ q tail _ => (hrec q tail).2.2.le) hsmall
  obtain ⟨hreg,ha,hb,hc⟩ := hjets qs [] (by simp)
  have hE : 0 ≤ variationEnergy e qs := List.sum_nonneg (by
    intro z hz
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
    exact he q hq)
  intro x
  refine ⟨by positivity,hreg x,?_⟩
  intro n hn2
  interval_cases n
  · simpa only [iteratedDeriv_zero,← Real.norm_eq_abs] using
      (ha.norm_le x).trans (hn.1.trans (by nlinarith only [mul_nonneg hD hE]))
  · simpa only [iteratedDeriv_one,← Real.norm_eq_abs] using
      (hb.norm_le x).trans (hn.2.1.trans (by nlinarith only [mul_nonneg hD hE]))
  · simpa only [iteratedDeriv_succ,iteratedDeriv_zero,← Real.norm_eq_abs] using
      (hc.norm_le x).trans hn.2.2

end SKBarriers2.Corner
