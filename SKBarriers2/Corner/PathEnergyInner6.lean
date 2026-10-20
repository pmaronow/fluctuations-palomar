module

public import SKBarriers2.Analysis.ParamStep4

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

private theorem inner_positive_masses_eventually (ps : List (ℝ → ℝ × E)) {k : ℝ}
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

private theorem inner_second_exp_linear_parameter
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) (M : P →L[ℝ] ℝ) :
    deriv (deriv (fun t => Real.exp (M (p t)))) k =
      Real.exp (M (p k))*((M (deriv p k))^2+M (deriv (deriv p) k)) := by
  have hd := (hp.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hp.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have he : deriv (fun t => Real.exp (M (p t))) =ᶠ[𝓝 k]
      fun t => Real.exp (M (p t))*M (deriv p t) := by
    filter_upwards [hp.eventually (by norm_num)] with t ht
    exact ((M.hasFDerivAt.comp_hasDerivAt t
      (ht.differentiableAt (by norm_num)).hasDerivAt).exp).deriv
  rw [he.deriv_eq]
  have H := (((M.hasFDerivAt.comp_hasDerivAt k hd).exp).mul
    (M.hasFDerivAt.comp_hasDerivAt k hdd)).deriv
  convert H using 1
  · rfl
  · dsimp only [Function.comp_def]
    ring

private theorem inner_linear_parameter_jets
    {P Y : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) (L : P →L[ℝ] Y) :
    deriv (fun t => L (p t)) k = L (deriv p k) ∧
      deriv (deriv (fun t => L (p t))) k = L (deriv (deriv p) k) := by
  have hfirst := (L.hasFDerivAt.comp_hasDerivAt k
    (hp.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hnear : deriv (fun t => L (p t)) =ᶠ[𝓝 k] fun t => L (deriv p t) := by
    filter_upwards [hp.eventually (by norm_num)] with t ht
    exact (L.hasFDerivAt.comp_hasDerivAt t
      (ht.differentiableAt (by norm_num)).hasDerivAt).deriv
  refine ⟨hfirst, ?_⟩
  rw [hnear.deriv_eq]
  exact (L.hasFDerivAt.comp_hasDerivAt k
    ((hp.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt).deriv

theorem curveChain_cons_twoJet {B C A H : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (p : ℝ → ℝ × E) (ps : List (ℝ → ℝ × E)) {k : ℝ}
    (hreg : ∀ q ∈ p::ps, ContDiffAt ℝ 2 q k)
    (hpos : ∀ q ∈ p::ps, 0 < (q k).1)
    (hF : QPotential 3 C (vectorIncrementChain (ps.map (fun q => q k)) f))
    (hG : QBoundedJets 3 A (fun y => deriv (fun t =>
      vectorIncrementChain (ps.map (fun q => q t)) f y) k))
    (hQ : QBoundedJets 1 H (fun y => deriv (deriv (fun t =>
      vectorIncrementChain (ps.map (fun q => q t)) f y)) k)) (x : E) :
    let F := vectorIncrementChain (ps.map (fun q => q k)) f
    let G := fun y => deriv (fun t => vectorIncrementChain (ps.map (fun q => q t)) f y) k
    let Q := fun y => deriv (deriv (fun t => vectorIncrementChain (ps.map (fun q => q t)) f y)) k
    let m := (p k).1
    let v := (p k).2
    let dm := deriv (fun t => (p t).1) k
    let ddm := deriv (deriv (fun t => (p t).1)) k
    let w := deriv (fun t => (p t).2) k
    let b := deriv (deriv (fun t => (p t).2)) k
    deriv (fun t => vectorIncrementChain ((p::ps).map (fun q => q t)) f x) k =
      firstVariationStep m v F G dm w x ∧
    deriv (deriv (fun t => vectorIncrementChain ((p::ps).map (fun q => q t)) f x)) k =
      secondVariationStep m v F G Q dm ddm w b x := by
  dsimp only
  let zs := ParamChain.logParameters (p::ps)
  let cs := ParamChain.coordinateSteps (X := E) (p::ps).length
  have hz : ContDiffAt ℝ 2 zs k := ParamChain.logParameters_contDiffAt _ hreg hpos
  have hnear := inner_positive_masses_eventually (p::ps) hreg hpos
  have hpath (t : ℝ) (ht : ∀ q ∈ p::ps, 0 < (q t).1) :
      ParamChain.exponentialSteps cs (zs t) = (p::ps).map (fun q => q t) :=
    ParamChain.coordinateSteps_apply _ t ht
  have hcsne : cs ≠ [] := by
    intro h
    have H := congrArg List.length (hpath k hpos)
    simp [h,ParamChain.exponentialSteps] at H
  obtain ⟨c,ds,hcs⟩ := List.exists_cons_of_ne_nil hcsne
  have hparts : ∀ᶠ t in 𝓝 k,
      (Real.exp (c.1 (zs t)),c.2 (zs t)) = p t ∧
      ParamChain.exponentialSteps ds (zs t) = ps.map (fun q => q t) := by
    filter_upwards [hnear] with t ht
    have H := hpath t ht
    rw [hcs] at H
    exact List.cons.inj H
  let F := ParamChain.exponentialChain ds (fun z => f z.2)
  have hFr : ParamRegular F := ParamChain.regular_exponentialChain ds
    (ParamChain.regular_fixedTerminal hf (by norm_num) _)
  have heF (y : E) : (fun t => F (zs t,y)) =ᶠ[𝓝 k]
      (fun t => vectorIncrementChain (ps.map (fun q => q t)) f y) := by
    filter_upwards [hparts] with t ht
    dsimp only [F,ParamChain.exponentialChain]
    rw [ht.2]
  have hFid : (fun y => F (zs k,y)) = vectorIncrementChain (ps.map (fun q => q k)) f :=
    funext (fun y => (heF y).self_of_nhds)
  have hGid : (fun y => fderiv ℝ F (zs k,y) (deriv zs k,0)) = fun y =>
      deriv (fun t => vectorIncrementChain (ps.map (fun q => q t)) f y) k := by
    funext y
    have H := ((hFr.1.differentiable (by norm_num) (zs k,y)).hasFDerivAt.comp_hasDerivAt k
      ((hz.differentiableAt (by norm_num)).hasDerivAt.prodMk (hasDerivAt_const k y))).deriv
    exact H.symm.trans (heF y).deriv_eq
  have hQid : (fun y => fderiv ℝ (fderiv ℝ F) (zs k,y) (deriv zs k,0) (deriv zs k,0)+
      fderiv ℝ F (zs k,y) (deriv (deriv zs) k,0)) = fun y =>
      deriv (deriv (fun t => vectorIncrementChain (ps.map (fun q => q t)) f y)) k := by
    funext y
    exact (ParamChain.second_parameter_curve hFr.1 hz y).symm.trans (heF y).deriv.deriv_eq
  have hm : (fun t => Real.exp (c.1 (zs t))) =ᶠ[𝓝 k] (fun t => (p t).1) := by
    filter_upwards [hparts] with t ht
    exact congrArg Prod.fst ht.1
  have hv : (fun t => c.2 (zs t)) =ᶠ[𝓝 k] (fun t => (p t).2) := by
    filter_upwards [hparts] with t ht
    exact congrArg Prod.snd ht.1
  have hdm : Real.exp (c.1 (zs k))*c.1 (deriv zs k) = deriv (fun t => (p t).1) k :=
    (((c.1.hasFDerivAt.comp_hasDerivAt k
      (hz.differentiableAt (by norm_num)).hasDerivAt).exp).deriv).symm.trans hm.deriv_eq
  have hddm : Real.exp (c.1 (zs k))*((c.1 (deriv zs k))^2+c.1 (deriv (deriv zs) k)) =
      deriv (deriv (fun t => (p t).1)) k :=
    (inner_second_exp_linear_parameter hz c.1).symm.trans hm.deriv.deriv_eq
  have hw : c.2 (deriv zs k) = deriv (fun t => (p t).2) k :=
    (inner_linear_parameter_jets hz c.2).1.symm.trans hv.deriv_eq
  have hb : c.2 (deriv (deriv zs) k) = deriv (deriv (fun t => (p t).2)) k :=
    (inner_linear_parameter_jets hz c.2).2.symm.trans hv.deriv.deriv_eq
  have heChain : (fun t => vectorIncrementChain ((p::ps).map (fun q => q t)) f x) =ᶠ[𝓝 k]
      fun t => vectorStep (Real.exp (c.1 (zs t))) (c.2 (zs t)) (fun y => F (zs t,y)) x := by
    filter_upwards [hparts] with t ht
    rw [List.map_cons,vectorIncrementChain,← ht.1]
    dsimp only [F,ParamChain.exponentialChain]
    rw [ht.2]
  have hFs : QPotential 3 C (fun y => F (zs k,y)) := by rw [hFid]; exact hF
  have hGs : QBoundedJets 3 A (fun y => fderiv ℝ F (zs k,y) (deriv zs k,0)) := by
    rw [hGid]
    exact hG
  have hQs : QBoundedJets 1 H (fun y => fderiv ℝ (fderiv ℝ F) (zs k,y)
      (deriv zs k,0) (deriv zs k,0)+fderiv ℝ F (zs k,y) (deriv (deriv zs) k,0)) := by
    rw [hQid]
    exact hQ
  have hfirst := (hasDerivAt_exponential_movingStep hFr c.1 c.2
    (hz.differentiableAt (by norm_num)).hasDerivAt (hFs.of_le (by norm_num))
    (qBoundedJets_iff_qBddSmooth.mp (hGs.of_le (by norm_num))) x).deriv
  have hsecond := second_deriv_exponential_movingStep hFr c.1 c.2 hz hFs hGs hQs x
  have hm₀ : Real.exp (c.1 (zs k)) = (p k).1 := hm.self_of_nhds
  have hv₀ : c.2 (zs k) = (p k).2 := hv.self_of_nhds
  rw [hFid,hGid,hdm,hw,hm₀,hv₀] at hfirst
  rw [hFid,hGid,hQid,hdm,hddm,hw,hb,hm₀,hv₀] at hsecond
  exact ⟨heChain.deriv_eq.trans hfirst,heChain.deriv.deriv_eq.trans hsecond⟩

end SKBarriers2.StepCalculus
