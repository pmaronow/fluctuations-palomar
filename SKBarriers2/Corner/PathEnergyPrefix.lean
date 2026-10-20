module

public import SKBarriers2.Corner.PathEnergyTransport
public import SKBarriers2.Corner.PathEnergyBias2

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
namespace SKBarriers2.ParamChain
open StepCalculus
local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem smooth_exponentialGeneratorSum {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) {G : P × E → ℝ} (hG : TestJetFamily G)
    (front middle : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) :
    ParamSmooth (fun z : P × E => pathGeneratorSum
      (vectorIncrementChain (exponentialSteps middle z.1) f)
      (fun y => G (z.1,y)) (exponentialSteps front z.1) z.2) := by
  have hF := regular_exponentialChain middle (regular_fixedTerminal hf (by norm_num) P)
  have hA := smooth_exponentialAverage front hF hG.value
  have hR := smooth_exponentialPrefixDefect hf hG front middle
  convert (hA.add (hG.value.const_mul (-1))).add (hR.const_mul (-1)) using 1
  funext z
  dsimp only [exponentialAverage,exponentialChain,tiltedPathTaylorDefect]
  ring

theorem exponentialPrefixSource_eq {F G : P × E → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    (q : (P →L[ℝ] ℝ) × (P →L[ℝ] E))
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E)))
    (hJ : ParamSmooth (fun z : P × E => pathGeneratorSum (fun y => F (z.1,y))
      (fun y => G (z.1,y)) (exponentialSteps ps z.1) z.2)) (p : P) (x : E) :
    let f := fun y => F (p,y)
    let g := fun y => G (p,y)
    let m := Real.exp (q.1 p)
    let v := q.2 p
    let H := vectorIncrementChain (exponentialSteps ps p) f
    let J := pathGeneratorSum f g (exponentialSteps ps p)
    tiltedPathTaylorDefect (exponentialSteps (q::ps) p) f g x-
      tiltedAverage m v H (tiltedPathTaylorDefect (exponentialSteps ps p) f g) x =
      (tiltedAverage m v H g x-g x-pathGenerator m v f g x)+
      (tiltedAverage m v H J x-J x) := by
  dsimp only
  have hH := regular_exponentialChain ps hF
  have hA := smooth_exponentialAverage ps hF hG
  have hiA := integrable_movingAverage_test hH hA q.1 q.2 p x
  have hiG := integrable_movingAverage_test hH hG q.1 q.2 p x
  have hiJ := integrable_movingAverage_test hH hJ q.1 q.2 p x
  have HI := integral_sub (hiA.sub hiG) hiJ
  simp only [Pi.sub_apply] at HI
  rw [integral_sub hiA hiG] at HI
  change tiltedAverage (Real.exp (q.1 p)) (q.2 p)
    (fun y => exponentialChain ps F (p,y))
    (fun y => exponentialAverage ps F G (p,y)-G (p,y)-
      pathGeneratorSum (fun z => F (p,z)) (fun z => G (p,z)) (exponentialSteps ps p) y) x =
    tiltedAverage (Real.exp (q.1 p)) (q.2 p)
      (fun y => exponentialChain ps F (p,y)) (fun y => exponentialAverage ps F G (p,y)) x-
    tiltedAverage (Real.exp (q.1 p)) (q.2 p)
      (fun y => exponentialChain ps F (p,y)) (fun y => G (p,y)) x-
    tiltedAverage (Real.exp (q.1 p)) (q.2 p)
      (fun y => exponentialChain ps F (p,y))
      (pathGeneratorSum (fun y => F (p,y)) (fun y => G (p,y)) (exponentialSteps ps p)) x at HI
  change
    (tiltedAverage (Real.exp (q.1 p)) (q.2 p)
      (fun y => exponentialChain ps F (p,y))
      (fun y => exponentialAverage ps F G (p,y)) x-G (p,x)-
      (pathGenerator (Real.exp (q.1 p)) (q.2 p) (fun y => F (p,y)) (fun y => G (p,y)) x+
        pathGeneratorSum (fun y => F (p,y)) (fun y => G (p,y)) (exponentialSteps ps p) x))-
    tiltedAverage (Real.exp (q.1 p)) (q.2 p)
      (fun y => exponentialChain ps F (p,y))
      (fun y => exponentialAverage ps F G (p,y)-G (p,y)-
        pathGeneratorSum (fun z => F (p,z)) (fun z => G (p,z)) (exponentialSteps ps p) y) x = _
  rw [HI]
  dsimp only [exponentialChain]
  ring

end SKBarriers2.ParamChain

namespace SKBarriers2.Corner
open StepCalculus ParamChain
local notation "E" => (Fin 3 → ℝ)
local notation "Curve" => (ℝ → ℝ × E)

def curvePrefixDefect (front middle : List Curve) (f : E → ℝ) (w : ℝ → E)
    (t : ℝ) (x : E) : ℝ :=
  tiltedPathTaylorDefect (front.map (fun q => q t))
    (vectorIncrementChain (middle.map (fun q => q t)) f)
    (fun y => (fderiv ℝ f y (w t))^2) x

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
theorem curvePrefixDefect_step_jets {f : E → ℝ} {B₀ B R K D e a b c k : ℝ}
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
    (htail : QBoundedJets 4 a (curvePrefixDefect tail middle f w k))
    (htail₁ : QBoundedJets 2 b (fun x => deriv (fun t => curvePrefixDefect tail middle f w t x) k))
    (htail₂ : QBoundedJets 0 c (fun x => deriv (deriv (fun t => curvePrefixDefect tail middle f w t x)) k))
    (hsource :
      let T := fun t x => tiltedAverage (q t).1 (q t).2
        (vectorIncrementChain ((tail++middle).map (fun p => p t)) f)
        (curvePrefixDefect tail middle f w t) x
      let S := fun t x => curvePrefixDefect (q::tail) middle f w t x-T t x
      QBoundedJets 4 (D*e) (S k) ∧
      QBoundedJets 2 (D*e) (fun x => deriv (fun t => S t x) k) ∧
      QBoundedJets 0 (D*e) (fun x => deriv (deriv (fun t => S t x)) k)) :
    (∀ x, ContDiffAt ℝ 2 (fun t => curvePrefixDefect (q::tail) middle f w t x) k) ∧
    QBoundedJets 4 ((1+K*e)*a+D*e) (curvePrefixDefect (q::tail) middle f w k) ∧
    QBoundedJets 2 ((1+K*e)*b+K*e*a+D*e)
      (fun x => deriv (fun t => curvePrefixDefect (q::tail) middle f w t x) k) ∧
    QBoundedJets 0 ((1+K*e)*c+K*e*(a+b)+D*e)
      (fun x => deriv (deriv (fun t => curvePrefixDefect (q::tail) middle f w t x)) k) := by
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
  let U := fun z : P × E => tiltedPathTaylorDefect
    (exponentialSteps (zs.take tail.length) z.1)
    (vectorIncrementChain (exponentialSteps (zs.drop tail.length) z.1) f)
    (fun y => (fderiv ℝ f y (W z.1))^2) z.2
  have hF : ParamRegular F := regular_exponentialChain _ (regular_fixedTerminal hf (by norm_num) P)
  have hU : ParamSmooth U := smooth_exponentialPrefixDefect
    (hf.of_le (by norm_num : 3 ≤ 5)) (testJetFamily_terminalGradient_sq hf W) _ _
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
  have hfull : (fun t x => exponentialChain (zs.take tail.length) F (Q t,x)) =ᶠ[𝓝 k]
      fun t x => vectorIncrementChain ((tail++middle).map (fun p => p t)) f x := by
    filter_upwards [hgeom] with t ht
    funext x
    dsimp only [F,exponentialChain]
    rw [ht.2.1,ht.2.2.1,List.map_append,vectorIncrementChain_append]
  have hURep : (fun t x => U (Q t,x)) =ᶠ[𝓝 k] curvePrefixDefect tail middle f w := by
    filter_upwards [hgeom] with t ht
    funext x
    dsimp only [U,curvePrefixDefect,W,Q]
    rw [ht.2.1,ht.2.2.1]
    rfl
  have hmass : (fun t => Real.exp (z.1 (Q t))) =ᶠ[𝓝 k] fun t => (q t).1 :=
    hgeom.mono (fun _ ht => congrArg Prod.fst ht.1)
  have hdir : (fun t => z.2 (Q t)) =ᶠ[𝓝 k] fun t => (q t).2 :=
    hgeom.mono (fun _ ht => congrArg Prod.snd ht.1)
  have hmass₂ := hmass.iteratedDeriv_eq 2
  have hdir₂ := hdir.iteratedDeriv_eq 2
  have hfull₁ := familyJet_congr hfull 1
  have hfull₂ := familyJet_congr hfull 2
  have hU₁ := familyJet_congr hURep 1
  have hU₂ := familyJet_congr hURep 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hmass₂ hdir₂ hfull₁ hfull₂ hU₁ hU₂
  have H := chartAverage_energy_jets (regular_exponentialChain (zs.take tail.length) hF) hU z hQ
    hK hK₄ hK₂ hK₁ hKS
    (by simpa only [hfull.self_of_nhds] using hbase)
    (by simpa only [hfull₁] using hbase₁) (by simpa only [hfull₂] using hbase₂)
    (by simpa only [hmass.self_of_nhds] using hm)
    (by simpa only [hmass.deriv_eq] using hdm) (by simpa only [hmass₂] using hddm)
    (by simpa only [hdir.self_of_nhds] using hv)
    (by simpa only [hmass.self_of_nhds,hdir.self_of_nhds] using hsmall)
    (by simpa only [hdir.self_of_nhds,hdir.deriv_eq,hdir₂] using henergy) he1
    (by simpa only [hURep.self_of_nhds] using htail)
    (by simpa only [hU₁] using htail₁) (by simpa only [hU₂] using htail₂)
  dsimp only at H
  let T := fun t x => tiltedAverage (q t).1 (q t).2
    (vectorIncrementChain ((tail++middle).map (fun p => p t)) f)
    (curvePrefixDefect tail middle f w t) x
  let S := fun t x => curvePrefixDefect (q::tail) middle f w t x-T t x
  have hTRep : (fun t x => tiltedAverage (Real.exp (z.1 (Q t))) (z.2 (Q t))
      (fun y => exponentialChain (zs.take tail.length) F (Q t,y)) (fun y => U (Q t,y)) x)
      =ᶠ[𝓝 k] T := by
    filter_upwards [hgeom,hfull,hURep] with t ht hft hut
    funext x
    have hm' : Real.exp (z.1 (Q t)) = (q t).1 := congrArg Prod.fst ht.1
    have hv' : z.2 (Q t) = (q t).2 := congrArg Prod.snd ht.1
    rw [hm',hv',hft,hut]
  have hT₁ := familyJet_congr hTRep 1
  have hT₂ := familyJet_congr hTRep 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hT₁ hT₂
  have hTc (x : E) : ContDiffAt ℝ 2 (fun t => T t x) k :=
    (H.1 x).congr_of_eventuallyEq (Filter.EventuallyEq.symm (hTRep.mono (fun _ ht => congrFun ht x)))
  have hval : QBoundedJets 4 ((1+K*e)*a) (T k) := by
    simpa only [hTRep.self_of_nhds] using H.2.1
  have hfirst : QBoundedJets 2 ((1+K*e)*b+K*e*a) (fun x => deriv (fun t => T t x) k) := by
    simpa only [hT₁] using H.2.2.1
  have hsecond : QBoundedJets 0 ((1+K*e)*c+K*e*(a+b))
      (fun x => deriv (deriv (fun t => T t x)) k) := by
    simpa only [hT₂] using H.2.2.2
  have hRc (x : E) : ContDiffAt ℝ 2 (fun t => curvePrefixDefect (q::tail) middle f w t x) k :=
    contDiffAt_curvePrefixDefect hf (q::tail) middle w hw hreg hpos x
  have heq₀ : curvePrefixDefect (q::tail) middle f w k = fun x => T k x+S k x := by
    funext x
    dsimp only [S]
    ring
  have heq₁ : (fun x => deriv (fun t => curvePrefixDefect (q::tail) middle f w t x) k) =
      fun x => deriv (fun t => T t x) k+deriv (fun t => S t x) k := by
    funext x
    rw [show (fun t => S t x) = fun t => curvePrefixDefect (q::tail) middle f w t x-T t x from rfl,
      deriv_fun_sub ((hRc x).differentiableAt (by norm_num)) ((hTc x).differentiableAt (by norm_num))]
    ring
  have heq₂ : (fun x => deriv (deriv (fun t => curvePrefixDefect (q::tail) middle f w t x)) k) =
      fun x => deriv (deriv (fun t => T t x)) k+deriv (deriv (fun t => S t x)) k := by
    funext x
    have HS := iteratedDeriv_fun_sub (hRc x) (hTc x)
    simp only [iteratedDeriv_succ,iteratedDeriv_zero] at HS
    rw [show (fun t => S t x) = fun t => curvePrefixDefect (q::tail) middle f w t x-T t x from rfl,HS]
    ring
  refine ⟨hRc,?_⟩
  rw [heq₀,heq₁,heq₂]
  exact ⟨hval.add hsource.1,hfirst.add hsource.2.1,hsecond.add hsource.2.2⟩

end SKBarriers2.Corner
