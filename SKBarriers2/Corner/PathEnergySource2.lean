module

public import SKBarriers2.Corner.PathEnergySource

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
namespace SKBarriers2.Corner
open StepCalculus ParamChain
local notation "E" => (Fin 3 → ℝ)
local notation "Curve" => (ℝ → ℝ × E)

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
theorem curvePrefixSource_twoJet {f : E → ℝ} {B₀ B A C D CJ DJ k : ℝ}
    (hf : QPotential 5 B₀ f) (q : Curve) (tail middle : List Curve) (w : ℝ → E)
    (hreg : ∀ p ∈ (q::tail)++middle, ContDiffAt ℝ 2 p k)
    (hpos : ∀ p ∈ (q::tail)++middle, 0 < (p k).1) (hw : ContDiffAt ℝ 2 w k)
    (hbase : QPotential 4 B (vectorIncrementChain ((tail++middle).map (fun q => q k)) f))
    (hbase₁ : QBoundedJets 3 A (fun x => deriv (fun t => vectorIncrementChain
      ((tail++middle).map (fun q => q t)) f x) k))
    (hg : QBoundedJets 3 C (fun y => (fderiv ℝ f y (w k))^2))
    (hg₁ : QBoundedJets 1 D (fun y => deriv (fun t => (fderiv ℝ f y (w t))^2) k))
    (hj : QBoundedJets 3 CJ (pathGeneratorSum
      (vectorIncrementChain (middle.map (fun p => p k)) f)
      (fun y => (fderiv ℝ f y (w k))^2) (tail.map (fun p => p k))))
    (hj₁ : QBoundedJets 1 DJ (fun y => deriv (fun t => pathGeneratorSum
      (vectorIncrementChain (middle.map (fun p => p t)) f)
      (fun y => (fderiv ℝ f y (w t))^2) (tail.map (fun p => p t)) y) k))
    (hm : (q k).1 ≤ 1) :
    let F := fun t => vectorIncrementChain (middle.map (fun p => p t)) f
    let H := fun t => vectorIncrementChain ((tail++middle).map (fun p => p t)) f
    let H₁ := fun y => deriv (fun t => H t y) k
    let H₂ := fun y => deriv (deriv (fun t => H t y)) k
    let g := fun t y => (fderiv ℝ f y (w t))^2
    let a := fun y => deriv (fun t => g t y) k
    let d := fun y => deriv (deriv (fun t => g t y)) k
    let J := fun t => pathGeneratorSum (F t) (g t) (tail.map (fun p => p t))
    let J₁ := fun y => deriv (fun t => J t y) k
    let J₂ := fun y => deriv (deriv (fun t => J t y)) k
    let m := fun t => (q t).1
    let v := fun t => (q t).2
    let K := fun t y => pathGenerator (m t) (v t) (F t) (g t) y
    let S := curvePrefixSource q tail middle f w
    (∀ x, ContDiffAt ℝ 2 (fun t => S t x) k) ∧
    Continuous (fun x => deriv (deriv (fun t => S t x)) k) ∧
    ∀ x,
    deriv (fun t => S t x) k =
      firstTiltedAverageSource (m k) (v k) (H k) H₁ (g k) a
        (deriv m k) (deriv v k) x-a x-deriv (fun t => K t x) k+
        (firstTiltedAverageSource (m k) (v k) (H k) H₁ (J k) J₁
          (deriv m k) (deriv v k) x-J₁ x) ∧
    deriv (deriv (fun t => S t x)) k =
      secondMovingAverageSource (m k) (deriv m k) (deriv (deriv m) k)
        (v k) (deriv v k) (deriv (deriv v) k) (H k) H₁ H₂ (g k) a d x-d x-
        deriv (deriv (fun t => K t x)) k+
        (secondMovingAverageSource (m k) (deriv m k) (deriv (deriv m) k)
          (v k) (deriv v k) (deriv (deriv v) k) (H k) H₁ H₂ (J k) J₁ J₂ x-J₂ x) := by
  dsimp only
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
  let G := fun z : P × E => (fderiv ℝ f z.2 (W z.1))^2
  let J := fun z : P × E => pathGeneratorSum (fun y => F (z.1,y))
    (fun y => G (z.1,y)) (exponentialSteps (zs.take tail.length) z.1) z.2
  let K := fun u : P × E => pathGenerator (Real.exp (z.1 u.1)) (z.2 u.1)
    (fun y => F (u.1,y)) (fun y => G (u.1,y)) u.2
  have hF : ParamRegular F := regular_exponentialChain _ (regular_fixedTerminal hf (by norm_num) P)
  have hG : ParamSmooth G := (testJetFamily_terminalGradient_sq hf W).value
  have hJ : ParamSmooth J := smooth_exponentialGeneratorSum
    (hf.of_le (by norm_num : 3 ≤ 5)) (testJetFamily_terminalGradient_sq hf W) _ _
  have hK : ParamSmooth K := by
    have H := smooth_exponentialGeneratorSum
      (hf.of_le (by norm_num : 3 ≤ 5)) (testJetFamily_terminalGradient_sq hf W)
      [z] (zs.drop tail.length)
    simpa only [K,F,G,exponentialChain,exponentialSteps,List.map_cons,List.map_nil,
      pathGeneratorSum,add_zero] using H
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
  have hGRep : (fun t x => G (Q t,x)) =ᶠ[𝓝 k] fun t x => (fderiv ℝ f x (w t))^2 := by
    filter_upwards [] with t
    rfl
  have hJRep : (fun t x => J (Q t,x)) =ᶠ[𝓝 k] fun t x => pathGeneratorSum
      (vectorIncrementChain (middle.map (fun p => p t)) f)
      (fun y => (fderiv ℝ f y (w t))^2) (tail.map (fun p => p t)) x := by
    filter_upwards [hgeom] with t ht
    funext x
    dsimp only [J,F,exponentialChain,G,W,Q]
    rw [ht.2.1,ht.2.2.1]
    rfl
  have hKRep : (fun t x => K (Q t,x)) =ᶠ[𝓝 k] fun t x => pathGenerator
      (q t).1 (q t).2 (vectorIncrementChain (middle.map (fun p => p t)) f)
      (fun y => (fderiv ℝ f y (w t))^2) x := by
    filter_upwards [hgeom] with t ht
    funext x
    dsimp only [K,F,exponentialChain,G,W,Q]
    have hm' : Real.exp (z.1 (Q t)) = (q t).1 := congrArg Prod.fst ht.1
    have hv' : z.2 (Q t) = (q t).2 := congrArg Prod.snd ht.1
    rw [hm',hv',ht.2.2.1]
    rfl
  let R := fun z' : P × E => tiltedPathTaylorDefect
    (exponentialSteps (zs.take tail.length) z'.1)
    (vectorIncrementChain (exponentialSteps (zs.drop tail.length) z'.1) f)
    (fun y => G (z'.1,y)) z'.2
  let S := fun z' : P × E => tiltedPathTaylorDefect
    (exponentialSteps (z::zs.take tail.length) z'.1)
    (vectorIncrementChain (exponentialSteps (zs.drop tail.length) z'.1) f)
    (fun y => G (z'.1,y)) z'.2-
    tiltedAverage (Real.exp (z.1 z'.1)) (z.2 z'.1)
      (fun y => exponentialChain (zs.take tail.length) F (z'.1,y)) (fun y => R (z'.1,y)) z'.2
  have hR : ParamSmooth R := smooth_exponentialPrefixDefect
    (hf.of_le (by norm_num : 3 ≤ 5)) (testJetFamily_terminalGradient_sq hf W) _ _
  have hS : ParamSmooth S := by
    have HA := smooth_exponentialPrefixDefect
      (hf.of_le (by norm_num : 3 ≤ 5)) (testJetFamily_terminalGradient_sq hf W)
      (z::zs.take tail.length) (zs.drop tail.length)
    convert HA.add ((smooth_movingAverage
      (regular_exponentialChain (zs.take tail.length) hF) hR z.1 z.2).const_mul (-1)) using 1
    funext z'
    simp only [S,tiltedAverage_eq_vectorStepAverage_fun]
    ring
  have hSRep : (fun t x => S (Q t,x)) =ᶠ[𝓝 k] curvePrefixSource q tail middle f w := by
    filter_upwards [hgeom] with t ht
    funext x
    have HP : exponentialSteps (z::zs.take tail.length) (Q t) =
        (q t)::tail.map (fun p => p t) := by
      simp only [exponentialSteps,List.map_cons]
      change (Real.exp (z.1 (Q t)),z.2 (Q t))::exponentialSteps (zs.take tail.length) (Q t) = _
      rw [ht.1,ht.2.1]
    dsimp only [S,R,curvePrefixSource,curvePrefixDefect,F,exponentialChain,G,W,Q]
    have hm' : Real.exp (z.1 (Q t)) = (q t).1 := congrArg Prod.fst ht.1
    have hv' : z.2 (Q t) = (q t).2 := congrArg Prod.snd ht.1
    rw [HP,ht.2.1,ht.2.2.1,hm',hv']
    simp only [List.map_cons,List.map_append,vectorIncrementChain_append]
    rfl
  have hmass : (fun t => Real.exp (z.1 (Q t))) =ᶠ[𝓝 k] fun t => (q t).1 :=
    hgeom.mono (fun _ ht => congrArg Prod.fst ht.1)
  have hdir : (fun t => z.2 (Q t)) =ᶠ[𝓝 k] fun t => (q t).2 :=
    hgeom.mono (fun _ ht => congrArg Prod.snd ht.1)
  have hm0 : Real.exp (z.1 (Q k)) = (q k).1 := hmass.self_of_nhds
  have hv0 : z.2 (Q k) = (q k).2 := hdir.self_of_nhds
  have hH0 : (fun x => exponentialChain (zs.take tail.length) F (Q k,x)) =
      vectorIncrementChain ((tail++middle).map (fun p => p k)) f := hfull.self_of_nhds
  have hG0 : (fun x => G (Q k,x)) = fun x => (fderiv ℝ f x (w k))^2 :=
    hGRep.self_of_nhds
  have hJ0 : pathGeneratorSum (fun y => F (Q k,y)) (fun y => G (Q k,y))
      (exponentialSteps (zs.take tail.length) (Q k)) =
        pathGeneratorSum (vectorIncrementChain (middle.map (fun p => p k)) f)
          (fun y => (fderiv ℝ f y (w k))^2) (tail.map (fun p => p k)) := hJRep.self_of_nhds
  have hm₂ := hmass.iteratedDeriv_eq 2
  have hv₂ := hdir.iteratedDeriv_eq 2
  have hH₁ := familyJet_congr hfull 1
  have hH₂ := familyJet_congr hfull 2
  have hG₁ := familyJet_congr hGRep 1
  have hG₂ := familyJet_congr hGRep 2
  have hJ₁ := familyJet_congr hJRep 1
  have hJ₂ := familyJet_congr hJRep 2
  have hK₁ := familyJet_congr hKRep 1
  have hK₂ := familyJet_congr hKRep 2
  have hS₁ := familyJet_congr hSRep 1
  have hS₂ := familyJet_congr hSRep 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hm₂ hv₂ hH₁ hH₂ hG₁ hG₂ hJ₁ hJ₂ hK₁ hK₂ hS₁ hS₂
  simp only [J] at hJ₁ hJ₂
  refine ⟨fun x => ((hS.1.contDiffAt (x := (Q k,x))).comp (f := fun t : ℝ => (Q t,x)) k (hQ.prodMk (contDiffAt_const (c := x)))).congr_of_eventuallyEq
    (Filter.EventuallyEq.symm (hSRep.mono (fun _ ht => congrFun ht x))),?_,?_⟩
  · rw [← hS₂]
    exact continuous_second_parameter_curve hS.1 hQ
  · intro x
    have H := exponentialPrefixSource_twoJet hF hG z (zs.take tail.length) hJ hK
      (p := Q) (k := k) (B := B) (A := A) (C := C) (D := D) (CJ := CJ) (DJ := DJ) hQ
      (by simpa only [hfull.self_of_nhds] using hbase)
      (by simpa only [hH₁] using hbase₁)
      (by simpa only [hGRep.self_of_nhds] using hg)
      (by simpa only [hG₁] using hg₁)
      (by simpa only [hJ0] using hj)
      (by simpa only [hJ₁] using hj₁)
      (by simpa only [hmass.self_of_nhds] using hm)
      (fun x => congrFun hK₁ x) (fun x => congrFun hK₂ x) x
    dsimp only at H
    change ContDiffAt ℝ 2 (fun t => S (Q t,x)) k ∧
      deriv (fun t => S (Q t,x)) k = _ ∧
      deriv (deriv (fun t => S (Q t,x))) k = _ at H
    rw [congrFun hS₁ x,congrFun hS₂ x,congrFun hG₁ x,congrFun hG₂ x,
      congrFun hJ₁ x,congrFun hJ₂ x,hm0,hmass.deriv_eq,hm₂,
      hv0,hdir.deriv_eq,hv₂,hH0,hH₁,hH₂,hJ0,hJ₁,hJ₂,hG0,hG₁,hG₂] at H
    exact H.2

end SKBarriers2.Corner
