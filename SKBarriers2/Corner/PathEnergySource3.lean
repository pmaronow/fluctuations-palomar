module

public import SKBarriers2.Corner.PathEnergySource2
public import SKBarriers2.Corner.PathEnergyGenerator11
public import SKBarriers2.Corner.PathEnergyGenerator12
public import SKBarriers2.Corner.PathEnergyGeneratorSum6

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
namespace SKBarriers2.Corner
open StepCalculus ParamChain
local notation "E" => (Fin 3 → ℝ)
local notation "Curve" => (ℝ → ℝ × E)

private theorem source_window_direction_bound (β : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (α : ℝ → ℝ) (s h : ℝ), 0 ≤ h → ∀ N : ℕ,
      ∀ p ∈ windowKCurves β α s h N, ∀ k : ℝ, |k| ≤ 1/2 →
      ‖(p k).2‖ ≤ L*Real.sqrt (h/(N : ℝ)) ∧
      ‖deriv (fun t => (p t).2) k‖ ≤ L*Real.sqrt (h/(N : ℝ)) ∧
      ‖deriv (deriv (fun t => (p t).2)) k‖ ≤ L*Real.sqrt (h/(N : ℝ)) := by
  obtain ⟨A,hA,hbound⟩ := window_direction_budget
  refine ⟨A*|β|,by positivity,?_⟩
  intro α s h hh N p hp k hk
  obtain ⟨σ,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact (hbound β h hh N i k hk).2

set_option maxHeartbeats 1600000 in
theorem scalarData_windowPrefixSourceJets {β : ℝ} (D₀ : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D₀.q) : WindowPrefixSourceJets D₀ (Icc l u) := by
  by_cases hlu : l ≤ u
  · obtain ⟨C₀,hG,kapG,hC₀,hhG,hkapG,hobs⟩ := scalarData_window_terminalGradientSquare_jets D₀ hl hu
    obtain ⟨Cₛ,hS,kapS,hCₛ,hhS,hkapS,hsub⟩ := scalarData_orderedInner_sub_c7 D₀ hl hu
    obtain ⟨R,hJ,hR,hhJ,hjets⟩ := scalarData_orderedInnerVariations_c6_c4 D₀ hl hu
    obtain ⟨Kᵦ,hB,kapB,hKᵦ,hhB,hkapB,hbias⟩ := scalarData_window_weakBias_sources D₀ hl hu
    obtain ⟨V,a0,hV,hV0,ha0,hhV,hvar⟩ := scalarData_interpolated_window_variation_inputs D₀ hl hlu hu
    obtain ⟨B,aE,S,hE,kapE,hB0,_,_,hhE,hkapE,hentropy⟩ := scalarData_uniformWindowEntropyInputs D₀ hl hu
    obtain ⟨L,hL,hdir⟩ := source_window_direction_bound β
    let D := 2*Cₛ+2*R
    let Cⱼ := (1024*(B+R+R)+5)*C₀*V
    let C := 256*D*C₀+3*Kᵦ*Cⱼ
    let rad := min (1/2:ℝ) (min kapG (min kapS kapE))
    have hrad : 0 < rad := by dsimp only [rad]; positivity
    have hD : 0 ≤ D := by dsimp only [D]; positivity
    have hCⱼ : 0 ≤ Cⱼ := by dsimp only [Cⱼ]; positivity
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    refine ⟨C,min hG (min hS (min hJ (min hB (min hV (min hE 1))))),
      min kapB (rad/2),hC,by positivity,by positivity,?_⟩
    intro r hr h hh hh0 eps heps
    obtain ⟨hhG',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhS',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhJ',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhB',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhV',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhE',hh1⟩ := le_min_iff.mp hh0
    filter_upwards [eventually_ge_atTop (1:ℕ),
      eventually_weakGeneratorDefect_sources (B := B) (A := R) (H := R) (C₀ := C₀)
        (h := h) (eps := eps) (L := 3*L^2) hB0 hR.le hR.le hC₀ hh heps] with N hN hweak
    intro lam hlam j k hk
    dsimp only
    obtain ⟨hkB,hkr⟩ := le_min_iff.mp hk
    have hkstrict : |k| < rad := by linarith only [hkr,hrad]
    have hkRad : |k| ≤ rad := hkstrict.le
    have hkhalf : |k| ≤ 1/2 := hkRad.trans (min_le_left _ _)
    have hkG : |k| ≤ kapG := hkRad.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hkS : |k| ≤ kapS := hkRad.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hkE : |k| ≤ kapE := hkRad.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hnear : ∀ᶠ t in 𝓝 k, |t| ≤ rad := by
      filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds hkstrict)] with t ht
      exact ht.le
    let α := cdf (D₀.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let middle := ps.drop j.val
    let f := massVariationTerminal β α (r-h) h
    let o := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
    let w := fun t => (o t).2
    let e := windowVariationEnergy k
    let Ctest := C₀*h/(N:ℝ)
    let CJ := Cⱼ*h^2/(N:ℝ)
    let M := (C*(Real.sqrt h*h)+eps)/(N:ℝ)
    obtain ⟨henergy,hinputs⟩ := hvar r hr h hh hhV' N hN lam hlam k hkhalf
    have hEtotal : variationEnergy e ps ≤ V*h := henergy
    have he0 (p : Curve) : 0 ≤ e p := windowVariationEnergy_nonneg k p
    have hL (t : ℝ) : ps.map (fun q => q t) =
        massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N) lam := by
      dsimp only [ps]
      rw [windowKCurves_apply β _ (r-h) h t N hh.le,massPath_window_eq]
    have homem : o ∈ ps := orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j
    have hw : ContDiffAt ℝ 2 w k := (hinputs o homem).1.snd
    have hobsJet (t : ℝ) (ht : |t| ≤ rad) (c : Fin 3) :
        QBoundedJets 8 Ctest (fun x => iteratedDeriv c.val
          (fun z => (fderiv ℝ f x (w z))^2) t) := by
      simpa only [α,Ctest,f,w] using hobs r hr h hh hhG' N hN lam hlam t
        (ht.trans ((min_le_right _ _).trans (min_le_left _ _))) o homem c
    have hg0 : QBoundedJets 8 Ctest (fun y => (fderiv ℝ f y (w k))^2) := by
      simpa only [show (0:Fin 3).val = 0 from rfl,iteratedDeriv_zero] using hobsJet k hkRad 0
    have hg1 : QBoundedJets 8 Ctest (fun y => deriv (fun t => (fderiv ℝ f y (w t))^2) k) := by
      simpa only [show (1:Fin 3).val = 1 from rfl,iteratedDeriv_one] using hobsJet k hkRad 1
    have hg2 : QBoundedJets 8 Ctest (fun y => deriv (deriv (fun t => (fderiv ℝ f y (w t))^2)) k) := by
      simpa only [show (2:Fin 3).val = 2 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] using hobsJet k hkRad 2
    obtain ⟨_,hEN⟩ := hentropy r hr h hh hhE' k hkE N hN
    have hinner := (hEN lam hlam).1
    have hf : QPotential 9 B f := by
      have H := hinner (12*N-1) (by rw [windowMassPath_length]; omega)
      have hlen : (massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N) lam).length = 12*N := by
        rw [massPath,List.length_map,windowMassPath_length]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ 12*N)] at H
      have hdrop : (massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N) lam).drop (12*N) = [] :=
        List.drop_eq_nil_iff.mpr (by rw [hlen])
      rw [hdrop] at H
      exact H.of_le (by norm_num : 9 ≤ 10)
    intro front q tail hsplit
    have hfull : ps = front++q::(tail++middle) := by
      rw [← List.take_append_drop j.val ps,show ps.take j.val = front++q::tail from hsplit]
      simp only [List.append_assoc,List.cons_append,middle]
    have hjpos : 0 < j.val := by
      have H := congrArg List.length hsplit
      simp only [List.length_take,List.length_append,List.length_cons] at H
      omega
    let jp : Fin (12*N) := ⟨j.val-1,by omega⟩
    have hjp : jp.val+1 = j.val := by dsimp only [jp]; omega
    have hn : front.length < 12*N := by
      have H := congrArg List.length hfull
      rw [windowKCurves_length] at H
      simp only [List.length_append,List.length_cons] at H
      omega
    let i : Fin (12*N) := ⟨front.length,hn⟩
    have hqeq : q = orderedWindowCurve β α (α (r-h)) (r-h) h N lam i := by
      have H : ps[front.length]'(by rw [windowKCurves_length]; exact hn) = q := by simp [hfull]
      simpa only [ps,orderedWindowCurve,List.get_eq_getElem,i] using H.symm
    have hdrop : ps.drop (front.length+1) = tail++middle := by
      have H : ps = (front++[q])++(tail++middle) := by simpa only [List.append_assoc,List.singleton_append] using hfull
      rw [show front.length+1 = (front++[q]).length by simp,H,List.drop_left]
    let F := fun t => vectorIncrementChain (middle.map (fun p => p t)) f
    let H := fun t => vectorIncrementChain ((tail++middle).map (fun p => p t)) f
    let g := fun t y => (fderiv ℝ f y (w t))^2
    let F₁ := fun t x => deriv (fun z => F z x) t
    let F₂ := fun t x => deriv (deriv (fun z => F z x)) t
    let H₁ := fun x => deriv (fun t => H t x) k
    let H₂ := fun x => deriv (deriv (fun t => H t x)) k
    let a := fun t x => deriv (fun z => g z x) t
    let d := fun t x => deriv (deriv (fun z => g z x)) t
    let J := fun t => pathGeneratorSum (F t) (g t) (tail.map (fun p => p t))
    let J₁ := fun x => deriv (fun t => J t x) k
    let J₂ := fun x => deriv (deriv (fun t => J t x)) k
    let m := fun t => (q t).1
    let v := fun t => (q t).2
    let GenF := fullGeneratorJet (m k) (deriv m k) (deriv (deriv m) k)
      (F k) (F₁ k) (F₂ k) (g k) (a k) (d k) (v k) (deriv v k) (deriv (deriv v) k)
    let GenH := fullGeneratorJet (m k) (deriv m k) (deriv (deriv m) k)
      (H k) H₁ H₂ (g k) (a k) (d k) (v k) (deriv v k) (deriv (deriv v) k)
    have hFcurve (t : ℝ) : F t = orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam jp t := by
      dsimp only [F,middle]
      rw [List.map_drop,hL]
      simp only [orderedInnerChain,hjp,f]
    have hHcurve (t : ℝ) : H t = orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam i t := by
      dsimp only [H]
      rw [← hdrop,List.map_drop,hL]
      rfl
    have hsubmem : ∀ p ∈ (q::tail)++middle, p ∈ ps := by
      intro p hp
      rw [hfull]
      exact List.mem_append_right front hp
    have hqmem : q ∈ ps := hsubmem q (by simp)
    have hentry := hinputs q hqmem
    have heq0 := he0 q
    have hmass : |m k| ≤ 1 := by rw [abs_of_nonneg (ha0.le.trans hentry.2.1.1)]; exact hentry.2.1.2
    have heMesh : e q ≤ 3*L^2*h/(N:ℝ) := by
      obtain ⟨hv,hw,hb⟩ := hdir _ _ _ hh.le N q hqmem k hkhalf
      have hs : (L*Real.sqrt (h/(N:ℝ)))^2 = L^2*h/(N:ℝ) := by
        rw [mul_pow,Real.sq_sqrt (div_nonneg hh.le (Nat.cast_nonneg N))]
        ring
      have hD0 : 0 ≤ L*Real.sqrt (h/(N:ℝ)) := by positivity
      have HV := (sq_le_sq₀ (norm_nonneg _) hD0).mpr hv
      have HW := (sq_le_sq₀ (norm_nonneg _) hD0).mpr hw
      have HB := (sq_le_sq₀ (norm_nonneg _) hD0).mpr hb
      dsimp only [e,windowVariationEnergy]
      rw [hs] at HV HW HB
      calc
        _ ≤ L^2*h/(N:ℝ)+L^2*h/(N:ℝ)+L^2*h/(N:ℝ) :=
          add_le_add (add_le_add HV HW) HB
        _ = _ := by ring
    have hF0 : QPotential 7 B (F k) := by
      rw [hFcurve]
      simpa only [orderedInnerChain,massPath,List.map_drop,windowEntryIndex] using
        (hinner jp.val (by rw [windowMassPath_length]; exact jp.isLt)).of_le (by norm_num : 7 ≤ 10)
    have hH0 : QPotential 8 B (H k) := by
      rw [hHcurve]
      simpa only [orderedInnerChain,massPath,List.map_drop,windowEntryIndex] using
        (hinner i.val (by rw [windowMassPath_length]; exact i.isLt)).of_le (by norm_num : 8 ≤ 10)
    have hFjets (t : ℝ) (ht : |t| ≤ 1/2) := hjets r hr h hh hhJ' N hN lam hlam jp t ht
    have hHjets := hjets r hr h hh hhJ' N hN lam hlam i k hkhalf
    have hF1 : QBoundedJets 6 (R*h) (F₁ k) := by
      simpa only [F₁,hFcurve,orderedInnerVariation_eq_iteratedDeriv_fun,iteratedDeriv_one] using (hFjets k hkhalf).1
    have hF2 : QBoundedJets 4 (R*h) (F₂ k) := by
      simpa only [F₂,hFcurve,orderedInnerVariation_eq_iteratedDeriv_fun,iteratedDeriv_succ,iteratedDeriv_zero] using (hFjets k hkhalf).2
    have hH1 : QBoundedJets 6 (R*h) H₁ := by
      simpa only [H₁,hHcurve,orderedInnerVariation_eq_iteratedDeriv_fun,iteratedDeriv_one] using hHjets.1
    have hH2 : QBoundedJets 4 (R*h) H₂ := by
      simpa only [H₂,hHcurve,orderedInnerVariation_eq_iteratedDeriv_fun,iteratedDeriv_succ,iteratedDeriv_zero] using hHjets.2
    have hRh : R*h ≤ R := mul_le_of_le_one_right hR.le hh1
    have hnearhalf (t : ℝ) (ht : |t| ≤ rad) : |t| ≤ 1/2 := ht.trans (min_le_left _ _)
    have hregAt (t : ℝ) (ht : |t| ≤ rad) :=
      (hvar r hr h hh hhV' N hN lam hlam t (hnearhalf t ht)).2
    have hFparam : ∀ᶠ t in 𝓝 k, ∀ x, ContDiffAt ℝ 2 (fun z => F z x) t := by
      filter_upwards [hnear] with t ht x
      have HH := contDiffAt_curveChain middle hf (by norm_num)
        (fun p hp => (hregAt t ht p (List.mem_of_mem_drop hp)).1)
        (fun p hp => ha0.trans_le (hregAt t ht p (List.mem_of_mem_drop hp)).2.1.1) x
      exact HH.comp (f := fun z : ℝ => (z,x)) t
        (contDiffAt_id.prodMk (contDiffAt_const (c := x)))
    have hFspatial : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (F t) := by
      filter_upwards [hnear] with t ht
      obtain ⟨_,HEN⟩ := hentropy r hr h hh hhE' t
        (ht.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) N hN
      have HP := (HEN lam hlam).1 jp.val (by rw [windowMassPath_length]; exact jp.isLt)
      have HF : QPotential 2 B (F t) := by
        rw [hFcurve]
        simpa only [orderedInnerChain,massPath,List.map_drop,windowEntryIndex] using HP.of_le (by norm_num : 2 ≤ 10)
      exact HF.smooth
    have hGparam : ∀ᶠ t in 𝓝 k, ∀ x, ContDiffAt ℝ 2 (fun z => g z x) t := by
      filter_upwards [hnear] with t ht x
      exact (((fderiv ℝ f x).contDiff.contDiffAt.comp t (hregAt t ht o homem).1.snd).pow 2)
    have hGspatial : ∀ᶠ t in 𝓝 k, ContDiff ℝ 2 (g t) := by
      filter_upwards [hnear] with t ht
      exact ((hobsJet t ht 0).of_le (by norm_num : 2 ≤ 8)).smooth
    have hF1near : ∀ᶠ t in 𝓝 k, QBoundedJets 3 R (F₁ t) := by
      filter_upwards [hnear] with t ht
      have HH := ((hFjets t (hnearhalf t ht)).1.of_le (by norm_num : 3 ≤ 6)).mono hRh
      simpa only [F₁,hFcurve,orderedInnerVariation_eq_iteratedDeriv_fun,iteratedDeriv_one] using HH
    have hF2near : ∀ᶠ t in 𝓝 k, QBoundedJets 3 R (F₂ t) := by
      filter_upwards [hnear] with t ht
      have HH := ((hFjets t (hnearhalf t ht)).2.of_le (by norm_num : 3 ≤ 4)).mono hRh
      simpa only [F₂,hFcurve,orderedInnerVariation_eq_iteratedDeriv_fun,iteratedDeriv_succ,iteratedDeriv_zero] using HH
    have hG1near : ∀ᶠ t in 𝓝 k, QBoundedJets 3 Ctest (a t) := by
      filter_upwards [hnear] with t ht
      simpa only [a,g,show (1:Fin 3).val = 1 from rfl,iteratedDeriv_one]
        using (hobsJet t ht 1).of_le (by norm_num : 3 ≤ 8)
    have hG2near : ∀ᶠ t in 𝓝 k, QBoundedJets 3 Ctest (d t) := by
      filter_upwards [hnear] with t ht
      simpa only [d,g,show (2:Fin 3).val = 2 from rfl,iteratedDeriv_succ,iteratedDeriv_zero]
        using (hobsJet t ht 2).of_le (by norm_num : 3 ≤ 8)
    have htailmem : ∀ p ∈ tail, p ∈ ps := fun p hp => hsubmem p (by simp [hp])
    have htailmass : ∀ p ∈ tail, |(p k).1| ≤ 1 ∧ |deriv (fun t => (p t).1) k| ≤ 1 ∧
        |deriv (deriv (fun t => (p t).1)) k| ≤ 1 := by
      intro p hp
      have HP := hinputs p (htailmem p hp)
      exact ⟨by rw [abs_of_nonneg (ha0.le.trans HP.2.1.1)]; exact HP.2.1.2,HP.2.2.1,HP.2.2.2⟩
    have hsum := actualGeneratorCurveSum_spatialJets tail (fun p hp => (hinputs p (htailmem p hp)).1)
      hFspatial hGspatial hFparam hGparam hF1near hF2near hG1near hG2near
      hF0 ((hF1.of_le (by norm_num : 5 ≤ 6)).mono hRh)
      ((hF2.of_le (by norm_num : 3 ≤ 4)).mono hRh) hg0
      (hg1.of_le (by norm_num : 6 ≤ 8)) (hg2.of_le (by norm_num : 4 ≤ 8)) htailmass
    have hEtail : variationEnergy e tail ≤ V*h := by
      have HE : variationEnergy e ps = variationEnergy e front+e q+
          (variationEnergy e tail+variationEnergy e middle) := by
        rw [hfull,variationEnergy_append]
        simp only [variationEnergy,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
        ring
      have H₁ := variationEnergy_nonneg (e := e) (l := front) (fun p hp => he0 p)
      have H₂ := variationEnergy_nonneg (e := e) (l := middle) (fun p hp => he0 p)
      linarith only [HE,H₁,H₂,he0 q,hEtotal]
    have hsumScale : (1024*(B+R+R)+5)*Ctest*variationEnergy e tail ≤ CJ := by
      calc
        _ ≤ (1024*(B+R+R)+5)*Ctest*(V*h) := by gcongr
        _ = _ := by dsimp only [Ctest,CJ,Cⱼ]; ring
    have hJ0 : QBoundedJets 6 CJ (J k) := hsum.1.mono hsumScale
    have hJ1 : QBoundedJets 4 CJ J₁ := hsum.2.1.mono hsumScale
    have hJ2 : QBoundedJets 2 CJ J₂ := hsum.2.2.mono hsumScale
    have hhead := curveFullGeneratorJet_twoJet q hentry.1 hFspatial hGspatial hFparam hGparam
      hF1near hF2near hG1near hG2near
    have hGen (c : Fin 3) (x : E) : GenF c x = iteratedDeriv c.val
        (fun t => pathGenerator (m t) (v t) (F t) (g t) x) k := by
      have HI := fullGeneratorCurveSumJet_eq_iteratedDeriv [q] hGspatial
        (fun p hp => by obtain rfl := List.mem_singleton.mp hp; exact hhead.1)
        (fun p hp => by obtain rfl := List.mem_singleton.mp hp; exact hhead.2) c x
      simpa only [fullGeneratorCurveSumJet,List.map_cons,List.map_nil,pathGeneratorSum,add_zero] using HI
    have hsources := curvePrefixSource_twoJet (hf.of_le (by norm_num : 5 ≤ 9)) q tail middle w
      (fun p hp => (hinputs p (hsubmem p hp)).1)
      (fun p hp => ha0.trans_le (hinputs p (hsubmem p hp)).2.1.1) hw
      (hH0.of_le (by norm_num : 4 ≤ 8)) ((hH1.of_le (by norm_num : 3 ≤ 6)).mono hRh)
      (hg0.of_le (by norm_num : 3 ≤ 8)) (hg1.of_le (by norm_num : 1 ≤ 8))
      (hJ0.of_le (by norm_num : 3 ≤ 6)) (hJ1.of_le (by norm_num : 1 ≤ 4)) hentry.2.1.2
    dsimp only at hsources
    have hweakS := hweak (H k) H₁ H₂ (g k) (a k) (d k) (m k) (deriv m k)
      (deriv (deriv m) k) (v k) (deriv v k) (deriv (deriv v) k) (e q)
      hH0 ((hH1.of_le (by norm_num : 4 ≤ 6)).mono hRh)
      ((hH2.of_le (by norm_num : 2 ≤ 4)).mono hRh) hg0
      (hg1.of_le (by norm_num : 5 ≤ 8)) (hg2.of_le (by norm_num : 4 ≤ 8))
      ⟨ha0.le.trans hentry.2.1.1,hentry.2.1.2⟩ hentry.2.2.1 hentry.2.2.2 le_rfl heMesh
    have hdiff0 : QBoundedJets 5 (D*h) (fun y => H k y-F k y) := by
      have HH := (hsub r hr h hh hhS' N hN lam hlam i k hkS).of_le (by norm_num : 5 ≤ 7)
      have HF := (hsub r hr h hh hhS' N hN lam hlam jp k hkS).of_le (by norm_num : 5 ≤ 7)
      change QBoundedJets 5 (Cₛ*h) (fun y =>
        orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam i k y-f y) at HH
      change QBoundedJets 5 (Cₛ*h) (fun y =>
        orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam jp k y-f y) at HF
      rw [← hHcurve k] at HH
      rw [← hFcurve k] at HF
      have HD := HH.sub HF
      convert HD.mono (show Cₛ*h+Cₛ*h ≤ D*h by dsimp only [D]; nlinarith only [mul_nonneg hR.le hh.le]) using 1
      funext y
      ring
    have hdiff1 := (hH1.of_le (by norm_num : 3 ≤ 6)).sub (hF1.of_le (by norm_num : 3 ≤ 6))
    have hdiff2 := (hH2.of_le (by norm_num : 1 ≤ 4)).sub (hF2.of_le (by norm_num : 1 ≤ 4))
    have hRD : R*h+R*h ≤ D*h := by dsimp only [D]; nlinarith only [mul_nonneg hCₛ hh.le]
    have hcomp := qBoundedJets_fullGeneratorJet_sub
      (hH0.smooth.differentiable (by norm_num)) (hH1.smooth.differentiable (by norm_num))
      (hH2.smooth.differentiable (by norm_num)) (hF0.smooth.differentiable (by norm_num))
      (hF1.smooth.differentiable (by norm_num)) (hF2.smooth.differentiable (by norm_num))
      hdiff0 (hdiff1.mono hRD) (hdiff2.mono hRD)
      (hg0.of_le (by norm_num : 5 ≤ 8)) (hg1.of_le (by norm_num : 3 ≤ 8))
      (hg2.of_le (by norm_num : 1 ≤ 8)) hmass hentry.2.2.1 hentry.2.2.2
      (v k) (deriv v k) (deriv (deriv v) k) (le_rfl : ‖v k‖^2+‖deriv v k‖^2+‖deriv (deriv v) k‖^2 ≤ e q)
    have hJbias := hbias r hr h hh hhB' N hN lam hlam i k hkB CJ CJ CJ
      (J k) J₁ J₂ hJ0 hJ1 hJ2
    dsimp only at hJbias hcomp hweakS
    simp only [α] at hqeq hHcurve
    simp only [← hqeq,← hHcurve,orderedInnerVariation_eq_iteratedDeriv_fun,iteratedDeriv_succ,iteratedDeriv_zero] at hJbias
    have hscale : (eps/(N:ℝ))*(e q)+256*(D*h)*Ctest*(e q)+Kᵦ*(CJ+CJ+CJ)*(e q) ≤ M*(e q) := by
      have hhsqrt : h ≤ Real.sqrt h := by
        nlinarith only [Real.sq_sqrt hh.le,Real.sqrt_nonneg h,hh1,hh.le]
      calc
        _ = (C*h^2/(N:ℝ)+eps/(N:ℝ))*(e q) := by dsimp only [C,Ctest,CJ]; ring
        _ ≤ (C*(Real.sqrt h*h)/(N:ℝ)+eps/(N:ℝ))*(e q) := by
          have hs : h^2 ≤ Real.sqrt h*h := by
            rw [pow_two]
            exact mul_le_mul_of_nonneg_right hhsqrt hh.le
          exact mul_le_mul_of_nonneg_right (add_le_add
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC) (Nat.cast_nonneg N))
            (le_refl (eps/(N:ℝ)))) heq0
        _ = _ := by dsimp only [M]; ring
    have hscale0 : (eps/(N:ℝ))*(e q)+256*(D*h)*Ctest*(e q)+Kᵦ*CJ*(e q) ≤ M*(e q) := by
      apply le_trans _ hscale
      have HK := mul_nonneg hKᵦ (mul_nonneg (show 0 ≤ CJ by dsimp only [CJ]; positivity) (he0 q))
      nlinarith only [HK]
    have hscale1 : (eps/(N:ℝ))*(e q)+256*(D*h)*Ctest*(e q)+Kᵦ*(CJ+CJ)*(e q) ≤ M*(e q) := by
      apply le_trans _ hscale
      have HK := mul_nonneg hKᵦ (mul_nonneg (show 0 ≤ CJ by dsimp only [CJ]; positivity) (he0 q))
      nlinarith only [HK]
    have hgenzero (A A₁ A₂ : E → ℝ) (x : E) : pathGenerator (m k) (v k) A (g k) x =
        fullGeneratorJet (m k) (deriv m k) (deriv (deriv m) k) A A₁ A₂
          (g k) (a k) (d k) (v k) (deriv v k) (deriv (deriv v) k) 0 x :=
      pathGenerator_eq_fullGeneratorJet_zero (hg0.smooth.of_le (by norm_num))
        (m k) (deriv m k) (deriv (deriv m) k) A A₁ A₂ (a k) (d k)
        (v k) (deriv v k) (deriv (deriv v) k) x
    have heq0 : curvePrefixSource q tail middle f w k = fun x =>
        tiltedGeneratorDefect (m k) (v k) (H k) (g k) x+
        (GenH 0 x-GenF 0 x)+(tiltedAverage (m k) (v k) (H k) (J k) x-J k x) := by
      funext x
      rw [curvePrefixSource_eq_terms q tail middle w (hF0.of_le (by norm_num : 5 ≤ 7))
        (hg0.of_le (by norm_num : 4 ≤ 8)) (fun p hp => ⟨ha0.le.trans (hinputs p (htailmem p hp)).2.1.1,
          (hinputs p (htailmem p hp)).2.1.2⟩) x]
      rw [hgenzero (H k) H₁ H₂ x,hgenzero (F k) (F₁ k) (F₂ k) x]
    have heq1 : (fun x => deriv (fun t => curvePrefixSource q tail middle f w t x) k) = fun x =>
        (firstTiltedAverageSource (m k) (v k) (H k) H₁ (g k) (a k) (deriv m k) (deriv v k) x-a k x-GenH 1 x)+
        (GenH 1 x-GenF 1 x)+(firstTiltedAverageSource (m k) (v k) (H k) H₁ (J k) J₁ (deriv m k) (deriv v k) x-J₁ x) := by
      funext x
      rw [(hsources.2.2 x).1,← show deriv (fun t => pathGenerator (m t) (v t) (F t) (g t) x) k = GenF 1 x by
        simpa only [show (1:Fin 3).val = 1 from rfl,iteratedDeriv_one] using (hGen 1 x).symm]
      ring
    have heq2 (x : E) : deriv (deriv (fun t => curvePrefixSource q tail middle f w t x)) k =
        (secondMovingAverageSource (m k) (deriv m k) (deriv (deriv m) k) (v k) (deriv v k) (deriv (deriv v) k)
          (H k) H₁ H₂ (g k) (a k) (d k) x-d k x-GenH 2 x)+
        (GenH 2 x-GenF 2 x)+(secondMovingAverageSource (m k) (deriv m k) (deriv (deriv m) k)
          (v k) (deriv v k) (deriv (deriv v) k) (H k) H₁ H₂ (J k) J₁ J₂ x-J₂ x) := by
      rw [(hsources.2.2 x).2,← show deriv (deriv (fun t => pathGenerator (m t) (v t) (F t) (g t) x)) k = GenF 2 x by
        simpa only [show (2:Fin 3).val = 2 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] using (hGen 2 x).symm]
      ring
    refine ⟨?_,?_,?_⟩
    · rw [heq0]
      exact ((hweakS.1.add hcomp.1).add hJbias.1).mono hscale0
    · rw [heq1]
      exact ((hweakS.2.1.add hcomp.2.1).add hJbias.2.1).mono hscale1
    · refine ⟨mul_nonneg (by positivity) (he0 q),contDiff_zero.mpr hsources.2.1,?_⟩
      intro n hn x
      have hn0 : n = 0 := by omega
      subst n
      simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
      change |deriv (deriv (fun t => curvePrefixSource q tail middle f w t x)) k| ≤ M*e q
      rw [heq2 x]
      exact (((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
        (add_le_add (add_le_add (hweakS.2.2 x) (by
          simpa only [Real.norm_eq_abs,GenH,GenF,m,g,a,d,e,windowVariationEnergy,v]
            using hcomp.2.2.norm_le x))
          (hJbias.2.2 x))).trans hscale
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

theorem scalarData_windowPrefixEnergyRecursions {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) : WindowPrefixEnergyRecursions D (Icc l u) :=
  scalarData_windowPrefixEnergyRecursions_of_sources D hl hu (scalarData_windowPrefixSourceJets D hl hu)

end SKBarriers2.Corner
