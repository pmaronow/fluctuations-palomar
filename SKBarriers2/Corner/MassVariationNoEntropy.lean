module

public import SKBarriers2.Corner.MassPathRegularity
public import SKBarriers2.Corner.MassSensitivityC2Proof

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

private theorem split_second_difference_le {R E P : ℝ → ℝ} {k A δ : ℝ}
    (hsplit : ∀ t, R t = E t + P t)
    (hp : |P k + P (-k) - 2 * P 0| ≤ A)
    (hek : |E k| ≤ δ) (hen : |E (-k)| ≤ δ) (he0 : |E 0| ≤ δ) :
    |R k + R (-k) - 2 * R 0| ≤ A + 4 * δ := by
  rw [hsplit k, hsplit (-k), hsplit 0]
  have he : (E k + P k) + (E (-k) + P (-k)) - 2 * (E 0 + P 0) =
      (P k + P (-k) - 2 * P 0) + (E k + E (-k) - 2 * E 0) := by ring
  rw [he]
  have hE : |E k + E (-k) - 2 * E 0| ≤ 4 * δ := by
    calc
      _ ≤ (|E k| + |E (-k)|) + |2 * E 0| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (δ + δ) + 2 * δ := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
      _ = _ := by ring
  exact (abs_add_le _ _).trans (add_le_add hp hE)

theorem windowWeightedRemainder_second_difference_le_of_pathEnergy
    (β : ℝ) (α : ℝ → ℝ) (a p s h k lam z M C2 C0 eta kap : ℝ)
    {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h) (hkap : 0 < kap) (hk : |k| ≤ kap)
    (hM : 0 ≤ M) (hC2 : 0 ≤ C2) (heta : 0 ≤ eta)
    (hw : ∀ j : Fin (12*N), |orderedMassWeight β α a p s h N j 0| ≤ M*h)
    (hd : ∀ j : Fin (12*N),
      |orderedMassWeight β α a p s h N j k-orderedMassWeight β α a p s h N j 0| ≤ M*h*k^2)
    (hr : ∀ j : Fin (12*N), ∀ t : ℝ, |t| ≤ kap →
      ContDiffAt ℝ 2 (orderedPathEnergyRemainder β α a p s h N lam j z) t ∧
      |iteratedDeriv 2 (orderedPathEnergyRemainder β α a p s h N lam j z) t| ≤
        C2*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ))
    (hE : ∀ j : Fin (12*N), ∀ t : ℝ, |t| ≤ kap →
      |entropyPathRemainder β α a p s h N lam j z t| ≤ eta/(N:ℝ))
    (hv : ∀ j : Fin (12*N), ∀ t : ℝ, |t| ≤ kap →
      |massSensitivityRemainder β α a p s h N lam j z t| ≤
        C0*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ)) :
    |windowWeightedRemainder β α a p s h k N lam z+
        windowWeightedRemainder β α a p s h (-k) N lam z-
        2*windowWeightedRemainder β α a p s h 0 N lam z| ≤
      24*M*(C2+C0)*(Real.sqrt h*h^3*k^2)+48*M*h*eta*k^2+48*M*h*eta := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hdiff (j : Fin (12*N)) :
      |massSensitivityRemainder β α a p s h N lam j z k+
        massSensitivityRemainder β α a p s h N lam j z (-k)-
        2*massSensitivityRemainder β α a p s h N lam j z 0| ≤
          2*(C2*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ))*k^2+4*eta/(N:ℝ) := by
    have hp : |orderedPathEnergyRemainder β α a p s h N lam j z k+
        orderedPathEnergyRemainder β α a p s h N lam j z (-k)-
        2*orderedPathEnergyRemainder β α a p s h N lam j z 0| ≤
          2*(C2*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ))*k^2 := by
      apply abs_symmetric_second_difference_le hkap (by positivity) hk
      · intro t ht
        exact ((hr j t ht).1.differentiableAt (by norm_num)).hasDerivAt
      · intro t ht
        exact (((hr j t ht).1.derivWithin (m := 1) (by norm_num)).differentiableAt
          (by norm_num)).hasDerivAt
      · intro t ht
        simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using (hr j t ht).2
    have H := split_second_difference_le
      (fun t => congrFun (massSensitivityRemainder_split β α a p s h N lam j z) t)
      hp (hE j k hk) (hE j (-k) (by simpa only [abs_neg] using hk))
      (hE j 0 (by simpa only [abs_zero] using hkap.le))
    convert H using 1; ring
  have H := weighted_symmetric_remainder_sum_le (mul_nonneg hM hh)
    (mul_nonneg (mul_nonneg hM hh) (sq_nonneg k)) hw hd hdiff
    (fun j => hv j k hk) (fun j => hv j (-k) (by simpa only [abs_neg] using hk))
  have he : ((12*N:ℕ):ℝ)*((M*h)*
      (2*(C2*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ))*k^2+4*eta/(N:ℝ))+
      2*(M*h*k^2)*(C0*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ))) =
      24*M*(C2+C0)*(Real.sqrt h*h^3*k^2)+48*M*h*eta*k^2+48*M*h*eta := by
    push_cast
    field_simp
    ring
  rw [he] at H
  simp_rw [windowWeightedRemainder_eq_ordered, orderedMassWeight_neg]
  convert H using 1
  congr 1
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

private theorem abs_even_integral_increment_le {R : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    {k B : ℝ} (hp : R k = ∫ lam in (0:ℝ)..1, F k lam-F 0 lam)
    (hm : R (-k) = ∫ lam in (0:ℝ)..1, F (-k) lam-F 0 lam)
    (heven : R (-k)=R k)
    (hip : IntervalIntegrable (fun lam => F k lam-F 0 lam) volume 0 1)
    (him : IntervalIntegrable (fun lam => F (-k) lam-F 0 lam) volume 0 1)
    (hb : ∀ lam ∈ Icc (0:ℝ) 1, |F k lam+F (-k) lam-2*F 0 lam| ≤ B) :
    |R k| ≤ B/2 := by
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun lam => (F k lam-F 0 lam)+(F (-k) lam-F 0 lam)) (C := B) (by
      intro lam hlam
      have hlam' : lam ∈ Ioc (0:ℝ) 1 := by
        simpa only [uIoc_of_le zero_le_one] using hlam
      have H := hb lam ⟨hlam'.1.le,hlam'.2⟩
      have he : (F k lam-F 0 lam)+(F (-k) lam-F 0 lam) =
          F k lam+F (-k) lam-2*F 0 lam := by ring
      simpa only [Real.norm_eq_abs, he] using H)
  rw [intervalIntegral.integral_add hip him, ← hp, ← hm, heven] at H
  have he : R k+R k=2*R k := by ring
  rw [he, norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)] at H
  norm_num at H
  linarith only [H]

theorem aggregateMassRemainderBound_of_pathEnergyInputs
    {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hsecond : PathEnergyC2 β α I) (hvalue : MassSensitivityValueBound β α I)
    (hentropy : UniformWindowEntropyInputs β α I)
    (hweights : WindowMassWeightBounds β α I)
    (hregular : UniformMassVariationRegularity β α I) :
    AggregateMassRemainderBound β α I := by
  obtain ⟨C2,h20,kap2,hC2,hh2,hkap2,hsecond⟩ := hsecond
  obtain ⟨C0,hv0,kapv,hC0,hhv,hkapv,hvalue⟩ := hvalue
  obtain ⟨hE0,kapE,hhE,hkapE,hentropy⟩ :=
    entropyPathRemainder_value_small_of_entropyInputs hentropy
  obtain ⟨M,hw0,kapw,hM,hhw,hkapw,hweights⟩ := hweights
  obtain ⟨hR0,kapR,hhR,hkapR,hregular⟩ := hregular
  let h0 := min h20 (min hv0 (min hw0 (min hR0 (min hE0 1))))
  let kap := min kap2 (min kapv (min kapw (min kapR (min kapE (1/2)))))
  have hkap : 0 < kap :=
    lt_min hkap2 (lt_min hkapv (lt_min hkapw (lt_min hkapR (lt_min hkapE (by norm_num)))))
  refine ⟨12*M*(C2+C0),h0,kap,by positivity,
    lt_min hh2 (lt_min hhv (lt_min hhw (lt_min hhR (lt_min hhE (by norm_num))))),hkap,?_⟩
  intro r hr h hh hh0 k hk eps heps
  have hh2' : h ≤ h20 := hh0.trans (min_le_left _ _)
  have hhv' : h ≤ hv0 := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhw' : h ≤ hw0 := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hhR' : h ≤ hR0 := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hhrest : h ≤ min hE0 1 := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hhE' : h ≤ hE0 := hhrest.trans (min_le_left _ _)
  have hh1 : h ≤ 1 := hhrest.trans (min_le_right _ _)
  have hk2 : kap ≤ kap2 := min_le_left _ _
  have hkv : kap ≤ kapv := (min_le_right _ _).trans (min_le_left _ _)
  have hkw : kap ≤ kapw := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hkR : kap ≤ kapR := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hkrest : kap ≤ min kapE (1/2) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hkE : kap ≤ kapE := hkrest.trans (min_le_left _ _)
  have hkhalf : |k| ≤ 1/2 := hk.trans (hkrest.trans (min_le_right _ _))
  let eta := eps/(48*M+1)
  have heta : 0 < eta := by positivity
  filter_upwards [hsecond r hr h hh hh2' eta heta, hvalue r hr h hh hhv' eta heta,
    hentropy r hr h hh hhE' eta heta, eventually_ge_atTop (1:ℕ)] with N hN2 hNv hNE hN
  intro z
  have hNpos : 0 < N := hN
  obtain ⟨hPhi,hreg⟩ := hregular r hr h hh hhR'
  have hf := massVariationTerminal_regular β α (r-h) h hPhi
  have hregk := hreg N hN k (hk.trans hkR)
  have hregn := hreg N hN (-k) (by simpa only [abs_neg] using hk.trans hkR)
  have hreg0 := hreg N hN 0 (by simpa only [abs_zero] using hkapR.le)
  let F := fun t lam => windowWeightedRemainder β α (α (r-h)) (1/2) (r-h) h t N lam z
  have hi (t : ℝ) (ht : |t| ≤ 1/2)
      (hregt : WindowMassRegularity β α (α (r-h)) (1/2) (r-h) h t N) :
      IntervalIntegrable (F t) volume 0 1 :=
    windowWeightedRemainder_intervalIntegrable β α _ _ _ _ _ hNpos hh.le (by norm_num)
      (OW.repairLength_mem (by norm_num) ht) hf hregt z
  have hip := (hi k hkhalf hregk).sub (hi 0 (by norm_num) hreg0)
  have him := (hi (-k) (by simpa only [abs_neg] using hkhalf) hregn).sub (hi 0 (by norm_num) hreg0)
  have H := abs_even_integral_increment_le
    (R := fun t => cornerMassRemainder β α r h t N z) (F := F)
    (cornerMassRemainder_eq_integral β α r h k hNpos hh.le
      (OW.repairLength_mem (by norm_num) hkhalf) hf hregk hreg0 z)
    (cornerMassRemainder_eq_integral β α r h (-k) hNpos hh.le
      (OW.repairLength_mem (by norm_num) (by simpa only [abs_neg] using hkhalf)) hf hregn hreg0 z)
    (cornerMassRemainder_neg β α r h k hNpos hh.le hkhalf hPhi z) hip him (by
      intro lam hlam
      exact windowWeightedRemainder_second_difference_le_of_pathEnergy
        β α _ _ _ _ k lam z M C2 C0 eta kap hNpos hh.le hkap hk hM hC2 heta.le
        (fun j => (hweights r hr h hh hhw' N hN j k (hk.trans hkw)).1)
        (fun j => (hweights r hr h hh hhw' N hN j k (hk.trans hkw)).2)
        (fun j t ht => hN2 lam hlam z j t (ht.trans hk2))
        (fun j t ht => hNE lam hlam z j t (ht.trans hkE))
        (fun j t ht => hNv lam hlam z j t (ht.trans hkv)))
  have hkSq : k^2 ≤ 1 := by
    have hkabs : |k| ≤ 1 := hkhalf.trans (by norm_num)
    have H := (sq_le_sq₀ (abs_nonneg k) (by norm_num : (0:ℝ)≤1)).mpr hkabs
    simpa only [sq_abs, one_pow] using H
  have hsmall : 24*M*h*eta*k^2+24*M*h*eta ≤ eps := by
    calc
      _ ≤ 24*M*1*eta*1+24*M*1*eta := by gcongr
      _ ≤ (48*M+1)*eta := by nlinarith only [heta.le]
      _ = eps := by dsimp only [eta]; field_simp
  have he : (24*M*(C2+C0)*(Real.sqrt h*h^3*k^2)+48*M*h*eta*k^2+48*M*h*eta)/2 =
      (12*M*(C2+C0))*(Real.sqrt h*h^3*k^2)+(24*M*h*eta*k^2+24*M*h*eta) := by ring
  rw [he] at H
  exact H.trans (add_le_add le_rfl hsmall)

theorem massVariationBound_of_scalarData_pathEnergyC2 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (hpath : PathEnergyC2 β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    MassVariationBound β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  have hA := scalarData_uniformWindowEntropyInputs D hl hu
  exact massVariationBound_of_remainder_of_leading
    (aggregateMassRemainderBound_of_pathEnergyInputs hpath
      (scalarData_massSensitivityValueBound D hl hu hA) hA
      (scalarData_windowMassWeightBounds D hl hu)
      (scalarData_uniformMassVariationRegularity D hl hu
        (scalarData_uniformMassPathRegularity D hl hu)))
    (massVariationLeadingBound_of_scalarInputs (scalarData_massVariationScalarInputs D hl hu))

theorem massVariationBound_of_scalarData_pathEnergy {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (hfirst : FirstOrderPathEnergyC2 β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    MassVariationBound β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  exact massVariationBound_of_scalarData_pathEnergyC2 D hl hu
    (pathEnergyC2_of_firstOrderPathEnergyC2 D hl hu hfirst)

end SKBarriers2.Corner
