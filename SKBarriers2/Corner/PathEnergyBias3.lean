module

public import SKBarriers2.Corner.PathEnergyBias2

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.Corner

open StepCalculus ParamChain
local notation "E" => (Fin 3 → ℝ)
local notation "Curve" => (ℝ → ℝ × E)

private theorem curveInnerCorrection_fun (middle : List Curve) (f : E → ℝ)
    (w : ℝ → E) (t : ℝ) : curveInnerCorrection middle f w t = fun x =>
      (fderiv ℝ (vectorIncrementChain ((middle.drop 1).map (fun p => p t)) f) x (w t))^2-
        (fderiv ℝ f x (w t))^2 := rfl

theorem curveInnerBias_window_eq_term (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ)
    (N : ℕ) (lam : ℝ) (j : Fin (12*N)) (hh : 0 ≤ h) (x : E) :
    (fun t => curveInnerBias
      ((windowKCurves β (interpolatedProfile α a lam) s h N).take j.val)
      ((windowKCurves β (interpolatedProfile α a lam) s h N).drop j.val)
      (massVariationTerminal β α s h)
      (fun t => (orderedWindowCurve β α a s h N lam j t).2) t x) =
      orderedEnergyAssemblyTerm β α a s h N lam j x 3 := by
  funext t
  let ps := windowKCurves β (interpolatedProfile α a lam) s h N
  have hL : ps.map (fun p => p t) = massPath (windowMassPath β α a (1/2) s h t N) lam := by
    dsimp only [ps]
    rw [windowKCurves_apply β _ s h t N hh,massPath_window_eq]
  have hd : (ps.drop j.val).drop 1 = ps.drop (j.val+1) := by
    rw [List.drop_drop]
  change curveInnerBias (ps.take j.val) (ps.drop j.val) (massVariationTerminal β α s h)
    (fun t => (orderedWindowCurve β α a s h N lam j t).2) t x = _
  simp only [curveInnerBias,curveInnerCorrection_fun,hd,List.map_take,List.map_drop,hL,
    orderedEnergyAssemblyTerm,pathEnergyAssemblyTerms]
  rw [orderedWindowCurve_apply β α a s h N lam j hh t]
  rfl

set_option maxHeartbeats 800000 in
theorem scalarData_windowInnerBiasC2 {β : ℝ} (D₀ : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D₀.q) : WindowInnerBiasC2 D₀ (Icc l u) := by
  by_cases hlu : l ≤ u
  · obtain ⟨Cδ,hδ,kapδ,hCδ,hhδ,hkapδ,hcorrection⟩ :=
      scalarData_orderedInnerCorrection_spatialJets D₀ hl hu
    obtain ⟨C,hS,kapS,hC,hhS,hkapS,hsources⟩ :=
      scalarData_window_innerCorrection_weakBias_sources D₀ hl hu
    obtain ⟨V,a0,hV,hV0,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D₀ hl hlu hu
    obtain ⟨B,aE,S,hE,kapE,hB,_,_,hhE,hkapE,hentropy⟩ :=
      scalarData_uniformWindowEntropyInputs D₀ hl hu
    obtain ⟨R,hJ,hR,hhJ,hjets⟩ := scalarData_orderedInnerVariations_c6_c4 D₀ hl hu
    let T₁ := firstTiltedTransportCoefficient B R
    let T₂ := secondAverageTransportCoefficient (secondMovingAverageScale B R R)
      (defectNoiseMomentBound 1 B) (defectNoiseMomentBound 2 B) (defectNoiseMomentBound 3 B)
    have hT₁ : 0 ≤ T₁ := by dsimp only [T₁,firstTiltedTransportCoefficient]; positivity
    have hT₂ : 0 ≤ T₂ := by
      dsimp only [T₂,secondAverageTransportCoefficient,secondMovingAverageScale,defectNoiseMomentBound]
      positivity
    let K := 1+|tiltedStabilityCoefficient 4 B|+|tiltedStabilityCoefficient 2 B|+T₁+T₂
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hK₄ : |tiltedStabilityCoefficient 4 B| ≤ K := by dsimp only [K]; linarith [abs_nonneg (tiltedStabilityCoefficient 2 B)]
    have hK₂ : |tiltedStabilityCoefficient 2 B| ≤ K := by dsimp only [K]; linarith [abs_nonneg (tiltedStabilityCoefficient 4 B)]
    have hK₁ : T₁ ≤ K := by dsimp only [K]; linarith [abs_nonneg (tiltedStabilityCoefficient 4 B),abs_nonneg (tiltedStabilityCoefficient 2 B)]
    have hKS : T₂ ≤ K := by dsimp only [K]; linarith [abs_nonneg (tiltedStabilityCoefficient 4 B),abs_nonneg (tiltedStabilityCoefficient 2 B)]
    let Z := V*(2*B+1)+1
    have hZ : 0 < Z := by dsimp only [Z]; positivity
    have hden : 0 < 2*K*V+1 := by positivity
    refine ⟨8*V*C,min hδ (min hS (min hV (min hE (min hJ
      (min 1 (min (1/Z) (1/(2*K*V+1)))))))),min kapδ (min kapS (min kapE (1/4))),
      by positivity,by positivity,by positivity,?_⟩
    intro r hr h hh hh0 eps heps
    obtain ⟨hhδ',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhS',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhV',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhE',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhJ',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hh1,hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhZ,hhshort⟩ := le_min_iff.mp hh0
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    intro lam hlam j k hk x
    obtain ⟨hkδ,hk⟩ := le_min_iff.mp hk
    obtain ⟨hkS,hk⟩ := le_min_iff.mp hk
    obtain ⟨hkE,hkquarter⟩ := le_min_iff.mp hk
    have hkhalf : |k| ≤ 1/2 := hkquarter.trans (by norm_num)
    let α := cdf (D₀.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let middle := ps.drop j.val
    let qs := ps.take j.val
    let f := massVariationTerminal β α (r-h) h
    let w := fun t => (orderedWindowCurve β α (α (r-h)) (r-h) h N lam j t).2
    let e := windowVariationEnergy k
    let M := C*h^2/(N:ℝ)
    obtain ⟨henergy,hinputs⟩ := hvar r hr h hh hhV' N hN lam hlam k hkhalf
    have hE : variationEnergy e ps ≤ V*h := henergy
    have he0 : ∀ q ∈ ps, 0 ≤ e q := fun q _ => windowVariationEnergy_nonneg k q
    have he (q : Curve) (hq : q ∈ ps) : e q ≤ V*h := by
      apply le_trans _ hE
      exact List.single_le_sum (fun z hz => by
        obtain ⟨q,_,rfl⟩ := List.mem_map.mp hz
        exact windowVariationEnergy_nonneg k q) _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
    have hprefix : variationEnergy e qs ≤ variationEnergy e ps := by
      have H := congrArg (variationEnergy e) (List.take_append_drop j.val ps)
      rw [variationEnergy_append] at H
      dsimp only [qs]
      linarith only [H,variationEnergy_nonneg (e := e) (l := ps.drop j.val) (fun q hq => he0 q (List.mem_of_mem_drop hq))]
    have hshort : 2*K*variationEnergy e qs ≤ 1 := by
      have H := (le_div_iff₀ hden).mp hhshort
      have HE := mul_le_mul_of_nonneg_left (hprefix.trans hE) (show 0 ≤ 2*K by positivity)
      nlinarith only [H,HE,hh.le]
    have hsmallWindow : Z*h ≤ 1 := by
      have H := (le_div_iff₀ hZ).mp hhZ
      nlinarith only [H]
    have hL (t : ℝ) : ps.map (fun q => q t) =
        massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N) lam := by
      dsimp only [ps]
      rw [windowKCurves_apply β _ (r-h) h t N hh.le,massPath_window_eq]
    have hdelta (t : ℝ) : curveInnerCorrection middle f w t = fun y =>
        (fderiv ℝ (orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j t) y (w t))^2-
          (fderiv ℝ f y (w t))^2 := by
      funext y
      have HD : middle.drop 1 = ps.drop (j.val+1) := by
        dsimp only [middle]
        rw [List.drop_drop]
      dsimp only [curveInnerCorrection]
      rw [HD,List.map_drop,hL]
      rfl
    obtain ⟨_,hg,ha,hq⟩ := hcorrection r hr h hh hhδ' N hN lam hlam j k hkδ
    have hg' : QBoundedJets 3 (Cδ*h^2/(N:ℝ)) (curveInnerCorrection middle f w k) := by
      simpa only [hdelta] using hg.of_le (by norm_num : 3 ≤ 6)
    have ha' : QBoundedJets 1 (Cδ*h^2/(N:ℝ))
        (fun y => deriv (fun t => curveInnerCorrection middle f w t y) k) := by
      simpa only [hdelta] using ha.of_le (by norm_num : 1 ≤ 4)
    obtain ⟨_,hEN⟩ := hentropy r hr h hh hhE' k hkE N hN
    have hinner := (hEN lam hlam).1
    have hf : QPotential 5 B f := by
      have H := hinner (12*N-1) (by rw [windowMassPath_length]; omega)
      have hlen : (massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N) lam).length = 12*N := by
        rw [massPath,List.length_map,windowMassPath_length]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ 12*N)] at H
      have hdrop : (massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N) lam).drop (12*N) = [] :=
        List.drop_eq_nil_iff.mpr (by rw [hlen])
      rw [hdrop] at H
      exact H.of_le (by norm_num : 5 ≤ 10)
    have hw : ContDiffAt ℝ 2 w k :=
      (hinputs _ (orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j)).1.snd
    have hresult := movingPrefix_c2BoundAt_of_regular_steps (k := k) qs
      (fun tail => curveInnerBias tail middle f w) e hK (by dsimp only [M]; positivity : 0 ≤ M)
      (fun q hq => he0 q (List.mem_of_mem_take hq))
      (fun t y => by simp only [curveInnerBias,List.map_nil,vectorIncrementAverage,sub_self]) hshort
    have hsteps : ∀ front q tail, qs = front++q::tail → ∀ a b c : ℝ,
      QBoundedJets 4 a (curveInnerBias tail middle f w k) →
      QBoundedJets 2 b (fun y => deriv (fun t => curveInnerBias tail middle f w t y) k) →
      QBoundedJets 0 c (fun y => deriv (deriv (fun t => curveInnerBias tail middle f w t y)) k) →
      (∀ y, ContDiffAt ℝ 2 (fun t => curveInnerBias (q::tail) middle f w t y) k) ∧
      QBoundedJets 4 ((1+K*e q)*a+M*e q) (curveInnerBias (q::tail) middle f w k) ∧
      QBoundedJets 2 ((1+K*e q)*b+K*e q*a+M*e q)
        (fun y => deriv (fun t => curveInnerBias (q::tail) middle f w t y) k) ∧
      QBoundedJets 0 ((1+K*e q)*c+K*e q*(a+b)+M*e q)
        (fun y => deriv (deriv (fun t => curveInnerBias (q::tail) middle f w t y)) k) := by
      intro front q tail hsplit a b c hva hvb hvc
      have hfull : ps = front++q::(tail++middle) := by
        rw [← List.take_append_drop j.val ps,show ps.take j.val = front++q::tail from hsplit]
        simp only [List.append_assoc,List.cons_append,middle]
      have hn : front.length < 12*N := by
        have H := congrArg List.length hfull
        rw [windowKCurves_length] at H
        simp only [List.length_append,List.length_cons] at H
        omega
      let i : Fin (12*N) := ⟨front.length,hn⟩
      have hqeq : q = orderedWindowCurve β α (α (r-h)) (r-h) h N lam i := by
        have H : ps[front.length]'(by rw [windowKCurves_length]; exact hn) = q := by
          simp [hfull]
        simpa only [ps,orderedWindowCurve,List.get_eq_getElem,i] using H.symm
      have hdrop : ps.drop (front.length+1) = tail++middle := by
        have H : ps = (front++[q])++(tail++middle) := by
          simpa only [List.append_assoc,List.singleton_append] using hfull
        rw [show front.length+1 = (front++[q]).length by simp,H,List.drop_left]
      have hbg (t : ℝ) : vectorIncrementChain ((tail++middle).map (fun q => q t)) f =
          orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam i t := by
        rw [← hdrop,List.map_drop,hL]
        rfl
      have hqmem : q ∈ ps := hfull.symm ▸ List.mem_append_right front (List.mem_cons_self ..)
      have hentry := hinputs q hqmem
      have heq0 := he0 q hqmem
      have heq : e q ≤ 1 := by
        have HV := mul_le_mul_of_nonneg_right
          (show V ≤ Z by dsimp only [Z]; nlinarith [mul_nonneg hV0.le hB]) hh.le
        linarith only [he q hqmem,hsmallWindow,HV]
      have hv2 : ‖(q k).2‖^2 ≤ e q := by
        dsimp only [e,windowVariationEnergy]
        nlinarith only [sq_nonneg ‖deriv (fun t => (q t).2) k‖,
          sq_nonneg ‖deriv (deriv (fun t => (q t).2)) k‖]
      have hv : ‖(q k).2‖ ≤ 1 := by nlinarith only [hv2,heq,norm_nonneg ((q k).2)]
      have hcurv : (q k).1*(B*‖(q k).2‖^2) ≤ 1/2 := by
        have HB := mul_le_mul_of_nonneg_left (hv2.trans (he q hqmem)) hB
        have HM := mul_le_of_le_one_left (mul_nonneg hB (sq_nonneg ‖(q k).2‖)) hentry.2.1.2
        dsimp only [Z] at hsmallWindow
        nlinarith only [HB,HM,hsmallWindow,hh.le,mul_nonneg hV0.le hh.le]
      have hbase : QPotential 5 B (fun y => vectorIncrementChain ((tail++middle).map (fun q => q k)) f y) := by
        rw [hbg]
        simpa only [orderedInnerChain,massPath,List.map_drop,windowEntryIndex] using
          (hinner i.val (by rw [windowMassPath_length]; exact i.isLt)).of_le (by norm_num : 5 ≤ 10)
      obtain ⟨hi₁,hi₂⟩ := hjets r hr h hh hhJ' N hN lam hlam i k hkhalf
      have hRh : R*h ≤ R := mul_le_of_le_one_right hR.le hh1
      have hbase₁ : QBoundedJets 3 R (fun y => deriv (fun t => vectorIncrementChain
          ((tail++middle).map (fun q => q t)) f y) k) := by
        simp_rw [hbg]
        simpa only [orderedInnerVariation_eq_iteratedDeriv_fun,iteratedDeriv_one] using (hi₁.of_le (by norm_num : 3 ≤ 6)).mono hRh
      have hbase₂ : QBoundedJets 1 R (fun y => deriv (deriv (fun t => vectorIncrementChain
          ((tail++middle).map (fun q => q t)) f y)) k) := by
        simp_rw [hbg]
        simpa only [orderedInnerVariation_eq_iteratedDeriv_fun,iteratedDeriv_succ,iteratedDeriv_zero] using
          (hi₂.of_le (by norm_num : 1 ≤ 4)).mono hRh
      have hsub : ∀ p ∈ (q::tail)++middle, p ∈ ps := by
        intro p hp
        rw [hfull]
        exact List.mem_append_right front hp
      apply curveInnerBias_step_jets hf q tail middle w
        (fun p hp => (hinputs p (hsub p hp)).1)
        (fun p hp => ha0.trans_le (hinputs p (hsub p hp)).2.1.1) hw hK hK₄ hK₂ hK₁ hKS
        hbase hbase₁ hbase₂ hentry.2.1.2 hentry.2.2.1 hentry.2.2.2 hv hcurv
        (le_rfl : ‖(q k).2‖^2+‖deriv (fun t => (q t).2) k‖^2+
          ‖deriv (deriv (fun t => (q t).2)) k‖^2 ≤ e q) heq hva hvb hvc hg' ha'
      have HS := hsources r hr h hh hhS' N hN lam hlam i j k hkS
      dsimp only at HS ⊢
      simpa only [hqeq,hbg,hdelta,orderedInnerVariation_eq_iteratedDeriv_fun,
        iteratedDeriv_succ,iteratedDeriv_zero,M,α,f,w,windowVariationEnergy] using HS
    have HC := hresult hsteps x
    rw [curveInnerBias_window_eq_term β α (α (r-h)) (r-h) h N lam j hh.le x] at HC
    apply HC.mono
    have hhsqrt : h ≤ Real.sqrt h := by
      nlinarith only [Real.sq_sqrt hh.le,Real.sqrt_nonneg h,hh1,hh.le]
    calc
      8*M*variationEnergy e qs ≤ 8*(C*h^2/(N:ℝ))*(V*h) := by gcongr; exact hprefix.trans hE
      _ = (8*V*C)*h*h^2/(N:ℝ) := by ring
      _ = (8*V*C)*(h*h^2)/(N:ℝ) := by ring
      _ ≤ (8*V*C)*(Real.sqrt h*h^2)/(N:ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hhsqrt (sq_nonneg h)) (by positivity))
          (Nat.cast_nonneg N)
      _ ≤ (8*V*C)*(Real.sqrt h*h^2)/(N:ℝ)+eps/(N:ℝ) := le_add_of_nonneg_right (by positivity)
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

end SKBarriers2.Corner
