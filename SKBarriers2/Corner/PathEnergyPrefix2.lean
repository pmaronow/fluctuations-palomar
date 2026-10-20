module

public import SKBarriers2.Corner.PathEnergyPrefix

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
namespace SKBarriers2.Corner
open StepCalculus ParamChain
local notation "E" => (Fin 3 → ℝ)
local notation "Curve" => (ℝ → ℝ × E)

def curvePrefixSource (q : Curve) (tail middle : List Curve) (f : E → ℝ)
    (w : ℝ → E) (t : ℝ) (x : E) : ℝ :=
  curvePrefixDefect (q::tail) middle f w t x-
    tiltedAverage (q t).1 (q t).2
      (vectorIncrementChain ((tail++middle).map (fun p => p t)) f)
      (curvePrefixDefect tail middle f w t) x

theorem curvePrefixSource_fun (q : Curve) (tail middle : List Curve) (f : E → ℝ)
    (w : ℝ → E) (t : ℝ) : curvePrefixSource q tail middle f w t = fun x =>
      curvePrefixDefect (q::tail) middle f w t x-
        tiltedAverage (q t).1 (q t).2
          (vectorIncrementChain ((tail++middle).map (fun p => p t)) f)
          (curvePrefixDefect tail middle f w t) x := rfl

theorem curvePrefixSource_eq_terms {f : E → ℝ} {B C t : ℝ}
    (q : Curve) (tail middle : List Curve) (w : ℝ → E)
    (hF : QPotential 5 B (vectorIncrementChain (middle.map (fun p => p t)) f))
    (hg : QBoundedJets 4 C (fun y => (fderiv ℝ f y (w t))^2))
    (hm : ∀ p ∈ tail, (p t).1 ∈ Icc (0:ℝ) 1) (x : E) :
    let F := vectorIncrementChain (middle.map (fun p => p t)) f
    let H := vectorIncrementChain ((tail++middle).map (fun p => p t)) f
    let g := fun y => (fderiv ℝ f y (w t))^2
    let J := pathGeneratorSum F g (tail.map (fun p => p t))
    curvePrefixSource q tail middle f w t x =
      tiltedGeneratorDefect (q t).1 (q t).2 H g x+
      (pathGenerator (q t).1 (q t).2 H g x-pathGenerator (q t).1 (q t).2 F g x)+
      (tiltedAverage (q t).1 (q t).2 H J x-J x) := by
  dsimp only
  have H := tiltedPathTaylorDefect_cons_eq_sum hF hg (q t)
    (tail.map (fun p => p t)) (by
      intro p hp
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
      exact hm r hr) x
  norm_num [tiltedPathDefectTerms,Fin.sum_univ_succ] at H
  dsimp only [curvePrefixSource,curvePrefixDefect]
  simp only [List.map_cons,List.map_append,vectorIncrementChain_append]
  have htest : curvePrefixDefect tail middle f w t =
      tiltedPathTaylorDefect (tail.map (fun p => p t))
        (vectorIncrementChain (middle.map (fun p => p t)) f)
        (fun y => (fderiv ℝ f y (w t))^2) := rfl
  rw [htest]
  linear_combination H

def WindowPrefixSourceJets {β : ℝ} (D : ScalarData β) (I : Set ℝ) : Prop :=
  ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N),
      ∀ k : ℝ, |k| ≤ kap →
      let α := cdf (D.μ : Measure ℝ)
      let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
      let middle := ps.drop j.val
      let f := massVariationTerminal β α (r-h) h
      let w := fun t => (orderedWindowCurve β α (α (r-h)) (r-h) h N lam j t).2
      let M := (C*(Real.sqrt h*h)+eps)/(N:ℝ)
      ∀ front q tail, ps.take j.val = front++q::tail →
      QBoundedJets 4 (M*windowVariationEnergy k q) (curvePrefixSource q tail middle f w k) ∧
      QBoundedJets 2 (M*windowVariationEnergy k q)
        (fun x => deriv (fun t => curvePrefixSource q tail middle f w t x) k) ∧
      QBoundedJets 0 (M*windowVariationEnergy k q)
        (fun x => deriv (deriv (fun t => curvePrefixSource q tail middle f w t x)) k)

theorem prefixEnergyDefect_eq_curvePrefixDefect (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ)
    (N : ℕ) (lam : ℝ) (j : Fin (12*N)) (qs : List Curve) (hh : 0 ≤ h) :
    prefixEnergyDefect β α a s h N lam j qs =
      curvePrefixDefect qs ((windowKCurves β (interpolatedProfile α a lam) s h N).drop j.val)
      (massVariationTerminal β α s h)
      (fun t => (orderedWindowCurve β α a s h N lam j t).2) := by
  funext t x
  dsimp only [prefixEnergyDefect,curvePrefixDefect]
  rw [List.map_drop,windowKCurves_apply β _ s h t N hh,massPath_window_eq]

set_option maxHeartbeats 800000 in
theorem scalarData_windowPrefixEnergyRecursions_of_sources {β : ℝ} (D₀ : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D₀.q)
    (hsource : WindowPrefixSourceJets D₀ (Icc l u)) :
    WindowPrefixEnergyRecursions D₀ (Icc l u) := by
  by_cases hlu : l ≤ u
  · obtain ⟨C,hS,kapS,hC,hhS,hkapS,hsources⟩ := hsource
    obtain ⟨V,a0,hV,hV0,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D₀ hl hlu hu
    obtain ⟨B,aE,S,hE,kapE,hB,_,_,hhE,hkapE,hentropy⟩ :=
      scalarData_uniformWindowEntropyInputs D₀ hl hu
    obtain ⟨R,hJ,hR,hhJ,hjets⟩ := scalarData_orderedInnerVariations_c6_c4 D₀ hl hu
    obtain ⟨hP,hhP,hregular⟩ := scalarData_prefixEnergyDefect_contDiffAt D₀ hl hu
    let T₁ := firstTiltedTransportCoefficient B R
    let T₂ := secondAverageTransportCoefficient (secondMovingAverageScale B R R)
      (defectNoiseMomentBound 1 B) (defectNoiseMomentBound 2 B) (defectNoiseMomentBound 3 B)
    have hT₁ : 0 ≤ T₁ := by dsimp only [T₁,firstTiltedTransportCoefficient]; positivity
    have hT₂ : 0 ≤ T₂ := by
      dsimp only [T₂,secondAverageTransportCoefficient,secondMovingAverageScale,defectNoiseMomentBound]
      positivity
    let K := 1+|tiltedStabilityCoefficient 4 B|+|tiltedStabilityCoefficient 2 B|+T₁+T₂
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hK₄ : |tiltedStabilityCoefficient 4 B| ≤ K := by dsimp only [K]; linarith only [hT₁,hT₂,abs_nonneg (tiltedStabilityCoefficient 2 B)]
    have hK₂ : |tiltedStabilityCoefficient 2 B| ≤ K := by dsimp only [K]; linarith only [hT₁,hT₂,abs_nonneg (tiltedStabilityCoefficient 4 B)]
    have hK₁ : T₁ ≤ K := by dsimp only [K]; linarith only [hT₁,hT₂,abs_nonneg (tiltedStabilityCoefficient 4 B),abs_nonneg (tiltedStabilityCoefficient 2 B)]
    have hKS : T₂ ≤ K := by dsimp only [K]; linarith only [hT₁,hT₂,abs_nonneg (tiltedStabilityCoefficient 4 B),abs_nonneg (tiltedStabilityCoefficient 2 B)]
    let Z := V*(2*B+1)+1
    have hZ : 0 < Z := by dsimp only [Z]; positivity
    refine ⟨K,C,min hS (min hV (min hE (min hJ (min hP (min 1 (1/Z)))))),
      min kapS (min kapE (1/2)),hK,hC,by positivity,by positivity,?_⟩
    intro r hr h hh hh0 eps heps
    obtain ⟨hhS',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhV',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhE',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhJ',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hhP',hh0⟩ := le_min_iff.mp hh0
    obtain ⟨hh1,hhZ⟩ := le_min_iff.mp hh0
    filter_upwards [eventually_ge_atTop (1:ℕ),hsources r hr h hh hhS' eps heps] with N hN hs
    intro lam hlam j k hk
    obtain ⟨hkS,hk⟩ := le_min_iff.mp hk
    obtain ⟨hkE,hkhalf⟩ := le_min_iff.mp hk
    let α := cdf (D₀.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let middle := ps.drop j.val
    let qs := ps.take j.val
    let f := massVariationTerminal β α (r-h) h
    let w := fun t => (orderedWindowCurve β α (α (r-h)) (r-h) h N lam j t).2
    let e := windowVariationEnergy k
    let M := (C*(Real.sqrt h*h)+eps)/(N:ℝ)
    obtain ⟨henergy,hinputs⟩ := hvar r hr h hh hhV' N hN lam hlam k hkhalf
    have hE : variationEnergy e ps ≤ V*h := henergy
    have he0 : ∀ q ∈ ps, 0 ≤ e q := fun q _ => windowVariationEnergy_nonneg k q
    have he (q : Curve) (hq : q ∈ ps) : e q ≤ V*h := by
      apply le_trans _ hE
      exact List.single_le_sum (fun z hz => by
        obtain ⟨q,_,rfl⟩ := List.mem_map.mp hz
        exact windowVariationEnergy_nonneg k q) _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
    have hsmallWindow : Z*h ≤ 1 := by
      have H := (le_div_iff₀ hZ).mp hhZ
      nlinarith only [H]
    have hL (t : ℝ) : ps.map (fun q => q t) =
        massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N) lam := by
      dsimp only [ps]
      rw [windowKCurves_apply β _ (r-h) h t N hh.le,massPath_window_eq]
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
    have hDef (tail : List Curve) :
        prefixEnergyDefect β (cdf (D₀.μ : Measure ℝ))
          (cdf (D₀.μ : Measure ℝ) (r-h)) (r-h) h N lam j tail =
            curvePrefixDefect tail middle f w :=
      prefixEnergyDefect_eq_curvePrefixDefect β α (α (r-h)) (r-h) h N lam j tail hh.le
    have hresult := prefixEnergy_envelopes_of_steps qs (fun tail => curvePrefixDefect tail middle f w)
      e K M k (fun t x => by simp [curvePrefixDefect,tiltedPathTaylorDefect,pathGeneratorSum,
        vectorIncrementAverage])
      (fun front tail hsplit x => by
        have H := hregular r hr h hh hhP' N hN lam hlam j k hkhalf front tail hsplit x
        simpa only [hDef] using H)
    have hsteps : ∀ front q tail, qs = front++q::tail → ∀ a b c : ℝ,
      QBoundedJets 4 a (curvePrefixDefect tail middle f w k) →
      QBoundedJets 2 b (fun y => deriv (fun t => curvePrefixDefect tail middle f w t y) k) →
      QBoundedJets 0 c (fun y => deriv (deriv (fun t => curvePrefixDefect tail middle f w t y)) k) →
      QBoundedJets 4 ((1+K*e q)*a+M*e q) (curvePrefixDefect (q::tail) middle f w k) ∧
      QBoundedJets 2 ((1+K*e q)*b+K*e q*a+M*e q)
        (fun y => deriv (fun t => curvePrefixDefect (q::tail) middle f w t y) k) ∧
      QBoundedJets 0 ((1+K*e q)*c+K*e q*(a+b)+M*e q)
        (fun y => deriv (deriv (fun t => curvePrefixDefect (q::tail) middle f w t y)) k) := by
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
      have heq : e q ≤ 1 := by
        have HV := mul_le_mul_of_nonneg_right
          (show V ≤ Z by dsimp only [Z]; nlinarith only [mul_nonneg hV0.le hB]) hh.le
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
      have H := curvePrefixDefect_step_jets hf q tail middle w
        (fun p hp => (hinputs p (hsub p hp)).1)
        (fun p hp => ha0.trans_le (hinputs p (hsub p hp)).2.1.1) hw hK hK₄ hK₂ hK₁ hKS
        hbase hbase₁ hbase₂ hentry.2.1.2 hentry.2.2.1 hentry.2.2.2 hv hcurv
        (le_rfl : ‖(q k).2‖^2+‖deriv (fun t => (q t).2) k‖^2+
          ‖deriv (deriv (fun t => (q t).2)) k‖^2 ≤ e q) heq hva hvb hvc
        (by simpa only [curvePrefixSource_fun,α,ps,middle,f,w,e,M,windowVariationEnergy]
          using hs lam hlam j k hkS front q tail hsplit)
      exact H.2
    have H := hresult hsteps
    dsimp only at H ⊢
    simpa only [hDef,qs,ps,α,e,M] using H
  · refine ⟨0,0,1,1,by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

end SKBarriers2.Corner
