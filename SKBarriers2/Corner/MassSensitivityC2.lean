module

public import SKBarriers2.Corner.PathEnergy

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def windowEntryIndex (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ)
    (j : Fin (12*N)) : Fin (windowMassPath β α a p s h k N).length :=
  ⟨j.val, by rw [windowMassPath_length]; exact j.isLt⟩

def orderedMassSensitivity (β : ℝ) (α : ℝ → ℝ) (a p s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (z k : ℝ) : ℝ :=
  massPathSensitivity (windowMassPath β α a p s h k N)
    (massVariationTerminal β α s h) lam (windowEntryIndex β α a p s h k N j) (fun _ => z)

def massSensitivityRemainder (β : ℝ) (α : ℝ → ℝ) (a p s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (z k : ℝ) : ℝ :=
  orderedMassSensitivity β α a p s h N lam j z k -
    (β^2/2)*windowMassEnergyEntry β α a p s h k N lam
      (windowEntryIndex β α a p s h k N j) z

def orderedMassWeight (β : ℝ) (α : ℝ → ℝ) (a p s h : ℝ) (N : ℕ)
    (j : Fin (12*N)) (k : ℝ) : ℝ :=
  ((windowMassPath β α a p s h k N).get (windowEntryIndex β α a p s h k N j)).2.1

def MassSensitivityC2 (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0:ℝ) 1, ∀ z : ℝ, ∀ j : Fin (12*N),
        let rho := massSensitivityRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z
        ∀ k : ℝ, |k| ≤ kap → ContDiffAt ℝ 2 rho k ∧
          |iteratedDeriv 2 rho k| ≤ C*(Real.sqrt h*h^2)/(N:ℝ)+eps/(N:ℝ)

def MassSensitivityValueBound (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0:ℝ) 1, ∀ z : ℝ, ∀ j : Fin (12*N),
        ∀ k : ℝ, |k| ≤ kap →
          |massSensitivityRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z k| ≤
            C*(Real.sqrt h*h^2)/(N:ℝ)+eps/(N:ℝ)

def KStabilityInputs (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ B h0 kap : ℝ, 0 ≤ B ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0:ℝ) 1,
        WindowTiltJets β α (α (r-h)) (1/2) (r-h) h N lam B kap ∧
        ∀ j : ℕ, j < 12*N → ∀ ell : ℕ, ell ≤ 8 →
          ∀ k : ℝ, |k| ≤ kap → ∀ x : Vec3,
            ContDiffAt ℝ 2 (fun q : ℝ × Vec3 => iteratedFDeriv ℝ ell
              (vectorIncrementChain
                ((massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h q.1 N) lam).drop (j+1))
                (massVariationTerminal β α (r-h) h)) q.2) (k,x)

def entropyPathRemainder (β : ℝ) (α : ℝ → ℝ) (a p s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (z k : ℝ) : ℝ :=
  orderedMassSensitivity β α a p s h N lam j z k-
    (1/2:ℝ)*windowGradientEnergy β α a p s h k N lam
      (windowEntryIndex β α a p s h k N j) z

theorem massSensitivityRemainder_split (β : ℝ) (α : ℝ → ℝ)
    (a p s h : ℝ) (N : ℕ) (lam : ℝ) (j : Fin (12*N)) (z : ℝ) :
    massSensitivityRemainder β α a p s h N lam j z =
      entropyPathRemainder β α a p s h N lam j z+
        orderedPathEnergyRemainder β α a p s h N lam j z := by
  funext k
  unfold massSensitivityRemainder entropyPathRemainder orderedPathEnergyRemainder windowEntryIndex
  simp only [Pi.add_apply]
  ring

def EntropyPathC2Small (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ K h0 kap : ℝ, 0 ≤ K ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ᶠ N : ℕ in atTop,
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ z : ℝ, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap →
        let E := entropyPathRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z
        ContDiffAt ℝ 2 E k ∧ |iteratedDeriv 2 E k| ≤ K*h^2/(N:ℝ)^2

def PathEnergyC2 (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0:ℝ) 1, ∀ z : ℝ, ∀ j : Fin (12*N),
        ∀ k : ℝ, |k| ≤ kap →
          let P := orderedPathEnergyRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z
          ContDiffAt ℝ 2 P k ∧ |iteratedDeriv 2 P k| ≤
            C*(Real.sqrt h*h^2)/(N:ℝ)+eps/(N:ℝ)

theorem massSensitivityC2_of_pathEnergyC2_of_entropyPathC2Small
    {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hpath : PathEnergyC2 β α I) (hentropy : EntropyPathC2Small β α I) :
    MassSensitivityC2 β α I := by
  obtain ⟨C,hP0,kapP,hC,hhP,hkapP,hpath⟩ := hpath
  obtain ⟨K,hE0,kapE,hK,hhE,hkapE,hentropy⟩ := hentropy
  refine ⟨C,min hP0 hE0,min kapP kapE,hC,lt_min hhP hhE,lt_min hkapP hkapE,?_⟩
  intro r hr h hh hh0 eps heps
  have hlim : Tendsto (fun N : ℕ => K*h^2/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hpath r hr h hh (hh0.trans (min_le_left _ _)) (eps/2) (by positivity),
    hentropy r hr h hh (hh0.trans (min_le_right _ _)),
    hlim.eventually (eventually_le_nhds (by positivity : (0:ℝ)<eps/2)),
    eventually_ge_atTop (1:ℕ)] with N hPN hEN hsmall hN
  intro lam hlam z j
  dsimp only
  intro k hk
  obtain ⟨hPc,hPb⟩ := hPN lam hlam z j k (hk.trans (min_le_left _ _))
  obtain ⟨hEc,hEb⟩ := hEN lam hlam z j k (hk.trans (min_le_right _ _))
  rw [massSensitivityRemainder_split]
  refine ⟨hEc.add hPc,?_⟩
  rw [iteratedDeriv_add hEc hPc]
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hEsmall : K*h^2/(N:ℝ)^2 ≤ (eps/2)/(N:ℝ) := by
    have H := (div_le_div_iff_of_pos_right hn).mpr hsmall
    simpa only [div_div, ← pow_two] using H
  exact (abs_add_le _ _).trans ((add_le_add (hEb.trans hEsmall) hPb).trans_eq (by ring))

theorem entropyPathRemainder_value_small_of_entropyInputs
    {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ} (hA : UniformWindowEntropyInputs β α I) :
    ∃ h0 kap : ℝ, 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ eps : ℝ, 0 < eps →
        ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0:ℝ) 1, ∀ z : ℝ, ∀ j : Fin (12*N),
          ∀ k : ℝ, |k| ≤ kap →
            |entropyPathRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z k| ≤ eps/(N:ℝ) := by
  obtain ⟨B,a0,D,hA0,kap,hB,ha0,hD,hhA,hkap,hA⟩ := hA
  refine ⟨hA0,kap,hhA,hkap,?_⟩
  intro r hr h hh hh0 eps heps
  let K := 2*B*StepCalculus.pathExpansionConstant B/a0
  have hK : 0 ≤ K := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hB) (StepCalculus.pathExpansionConstant_nonneg hB)) ha0.le
  have hlim : Tendsto (fun N : ℕ => K*D^2*h^2/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hvlim : Tendsto (fun N : ℕ => D*h/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_le_nhds heps),
    hvlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1)),
    eventually_ge_atTop (1:ℕ)] with N hsmall hvsmall hN
  intro lam hlam z j k hk
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  obtain ⟨hf,hjets⟩ := hA r hr h hh hh0 k hk N hN
  obtain ⟨hinner,hstep⟩ := hjets lam hlam
  let jj := windowEntryIndex β α (α (r-h)) (1/2) (r-h) h k N j
  let v := ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get jj).2.2
  have hinner' : QPotential 4 B (vectorIncrementChain
      (massPath ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).drop (jj.val+1)) lam)
      (massVariationTerminal β α (r-h) h)) := by
    simpa only [massPath, List.map_drop] using (hinner jj.val jj.isLt).of_le (by norm_num : 4≤10)
  have hdir : ‖v‖^2 ≤ D*h/(N:ℝ) := (hstep jj).2
  have hv : ‖v‖ ≤ 1 := by nlinarith [norm_nonneg v]
  have H := massPathSensitivity_first_order _ hf lam jj hinner' ha0 (hstep jj).1 hv (fun _ => z)
  change |entropyPathRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z k| ≤ K*‖v‖^4 at H
  have hfour : ‖v‖^4 ≤ (D*h/(N:ℝ))^2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hdir 2
  calc
    _ ≤ K*‖v‖^4 := H
    _ ≤ K*(D*h/(N:ℝ))^2 := mul_le_mul_of_nonneg_left hfour hK
    _ = (K*D^2*h^2/(N:ℝ))/(N:ℝ) := by field_simp
    _ ≤ eps/(N:ℝ) := (div_le_div_iff_of_pos_right hn).mpr hsmall

private theorem windowMassPath_weights_neg (β : ℝ) (α : ℝ → ℝ)
    (a p s h k : ℝ) (N : ℕ) :
    (windowMassPath β α a p s h (-k) N).map (fun q => q.2.1) =
      (windowMassPath β α a p s h k N).map (fun q => q.2.1) := by
  simp only [windowMassPath, windowMassSamples, List.map_append,
    List.map_flatMap, List.map_cons, List.map_nil, neg_sq]

theorem orderedMassWeight_neg (β : ℝ) (α : ℝ → ℝ) (a p s h : ℝ) (N : ℕ)
    (j : Fin (12*N)) (k : ℝ) :
    orderedMassWeight β α a p s h N j (-k) = orderedMassWeight β α a p s h N j k := by
  have H := congrArg (fun l : List ℝ => l.getD j.val 0)
    (windowMassPath_weights_neg β α a p s h k N)
  have hn (t : ℝ) : j.val < ((windowMassPath β α a p s h t N).map (fun q => q.2.1)).length := by
    rw [List.length_map, windowMassPath_length]
    exact j.isLt
  simpa only [List.getD_eq_getElem _ _ (hn (-k)), List.getD_eq_getElem _ _ (hn k),
    List.getElem_map, orderedMassWeight, windowEntryIndex, List.get_eq_getElem] using H

theorem windowWeightedRemainder_eq_ordered (β : ℝ) (α : ℝ → ℝ)
    (a p s h k : ℝ) (N : ℕ) (lam z : ℝ) :
    windowWeightedRemainder β α a p s h k N lam z =
      ∑ j : Fin (12*N), orderedMassWeight β α a p s h N j k *
        massSensitivityRemainder β α a p s h N lam j z k := by
  unfold windowWeightedRemainder
  apply Fintype.sum_equiv (finCongr (windowMassPath_length β α a p s h k N))
  intro j
  rfl

def WindowMassWeightBounds (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ M h0 kap : ℝ, 0 ≤ M ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap →
        |orderedMassWeight β α (α (r-h)) (1/2) (r-h) h N j 0| ≤ M*h ∧
        |orderedMassWeight β α (α (r-h)) (1/2) (r-h) h N j k-
          orderedMassWeight β α (α (r-h)) (1/2) (r-h) h N j 0| ≤ M*h*k^2

def UniformMassVariationRegularity (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ h0 kap : ℝ, 0 < h0 ∧ 0 < kap ∧ ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 →
    BoundedDerivs (Phi β α ((r-h)+4*h)) ∧
    ∀ N : ℕ, 1 ≤ N → ∀ k : ℝ, |k| ≤ kap →
      WindowMassRegularity β α (α (r-h)) (1/2) (r-h) h k N

theorem windowWeightedRemainder_second_difference_le
    (β : ℝ) (α : ℝ → ℝ) (a p s h k lam z M C2 C0 eta kap : ℝ)
    {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h) (hkap : 0 < kap) (hk : |k| ≤ kap)
    (hM : 0 ≤ M) (hC2 : 0 ≤ C2) (_hC0 : 0 ≤ C0) (heta : 0 ≤ eta)
    (hw : ∀ j : Fin (12*N), |orderedMassWeight β α a p s h N j 0| ≤ M*h)
    (hd : ∀ j : Fin (12*N),
      |orderedMassWeight β α a p s h N j k-orderedMassWeight β α a p s h N j 0| ≤ M*h*k^2)
    (hr : ∀ j : Fin (12*N), ∀ t : ℝ, |t| ≤ kap →
      ContDiffAt ℝ 2 (massSensitivityRemainder β α a p s h N lam j z) t ∧
      |iteratedDeriv 2 (massSensitivityRemainder β α a p s h N lam j z) t| ≤
        C2*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ))
    (hv : ∀ j : Fin (12*N), ∀ t : ℝ, |t| ≤ kap →
      |massSensitivityRemainder β α a p s h N lam j z t| ≤
        C0*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ)) :
    |windowWeightedRemainder β α a p s h k N lam z+
        windowWeightedRemainder β α a p s h (-k) N lam z-
        2*windowWeightedRemainder β α a p s h 0 N lam z| ≤
      24*M*(C2+C0)*(Real.sqrt h*h^3*k^2)+48*M*h*eta*k^2 := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hdiff (j : Fin (12*N)) :
      |massSensitivityRemainder β α a p s h N lam j z k+
        massSensitivityRemainder β α a p s h N lam j z (-k)-
        2*massSensitivityRemainder β α a p s h N lam j z 0| ≤
          2*(C2*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ))*k^2 := by
    apply abs_symmetric_second_difference_le hkap (by positivity) hk
    · intro t ht
      exact ((hr j t ht).1.differentiableAt (by norm_num)).hasDerivAt
    · intro t ht
      exact (((hr j t ht).1.derivWithin (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasDerivAt
    · intro t ht
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using (hr j t ht).2
  have H := weighted_symmetric_remainder_sum_le (mul_nonneg hM hh)
    (mul_nonneg (mul_nonneg hM hh) (sq_nonneg k)) hw hd hdiff
    (fun j => hv j k hk) (fun j => hv j (-k) (by simpa only [abs_neg] using hk))
  have he : ((12*N:ℕ):ℝ)*((M*h)*(2*(C2*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ))*k^2)+
      2*(M*h*k^2)*(C0*(Real.sqrt h*h^2)/(N:ℝ)+eta/(N:ℝ))) =
      24*M*(C2+C0)*(Real.sqrt h*h^3*k^2)+48*M*h*eta*k^2 := by
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

def AggregateMassRemainderBound (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ k : ℝ, |k| ≤ kap →
      ∀ eps : ℝ, 0 < eps → ∀ᶠ N : ℕ in atTop, ∀ z : ℝ,
        |cornerMassRemainder β α r h k N z| ≤ C*(Real.sqrt h*h^3*k^2)+eps

theorem aggregateMassRemainderBound_of_sensitivityInputs
    {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hsecond : MassSensitivityC2 β α I) (hvalue : MassSensitivityValueBound β α I)
    (hweights : WindowMassWeightBounds β α I)
    (hregular : UniformMassVariationRegularity β α I) :
    AggregateMassRemainderBound β α I := by
  obtain ⟨C2,h20,kap2,hC2,hh2,hkap2,hsecond⟩ := hsecond
  obtain ⟨C0,hv0,kapv,hC0,hhv,hkapv,hvalue⟩ := hvalue
  obtain ⟨M,hw0,kapw,hM,hhw,hkapw,hweights⟩ := hweights
  obtain ⟨hR0,kapR,hhR,hkapR,hregular⟩ := hregular
  let h0 := min h20 (min hv0 (min hw0 (min hR0 1)))
  let kap := min kap2 (min kapv (min kapw (min kapR (1/2))))
  have hkap : 0 < kap := lt_min hkap2 (lt_min hkapv (lt_min hkapw (lt_min hkapR (by norm_num))))
  refine ⟨12*M*(C2+C0),h0,kap,by positivity,
    lt_min hh2 (lt_min hhv (lt_min hhw (lt_min hhR (by norm_num)))),hkap,?_⟩
  intro r hr h hh hh0 k hk eps heps
  have hh2' : h ≤ h20 := hh0.trans (min_le_left _ _)
  have hhv' : h ≤ hv0 := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhw' : h ≤ hw0 := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hhR' : h ≤ hR0 := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hh1 : h ≤ 1 := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hk2 : kap ≤ kap2 := min_le_left _ _
  have hkv : kap ≤ kapv := (min_le_right _ _).trans (min_le_left _ _)
  have hkw : kap ≤ kapw := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hkR : kap ≤ kapR := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hkhalf : |k| ≤ 1/2 := hk.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  let eta := eps/(24*M+1)
  have heta : 0 < eta := by positivity
  filter_upwards [hsecond r hr h hh hh2' eta heta, hvalue r hr h hh hhv' eta heta,
    eventually_ge_atTop (1:ℕ)] with N hN2 hNv hN
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
      exact windowWeightedRemainder_second_difference_le β α _ _ _ _ k lam z M C2 C0 eta kap
        hNpos hh.le hkap hk hM hC2 hC0 heta.le
        (fun j => (hweights r hr h hh hhw' N hN j k (hk.trans hkw)).1)
        (fun j => (hweights r hr h hh hhw' N hN j k (hk.trans hkw)).2)
        (fun j t ht => hN2 lam hlam z j t (ht.trans hk2))
        (fun j t ht => hNv lam hlam z j t (ht.trans hkv)))
  have hkSq : k^2 ≤ 1 := by
    have hkabs : |k| ≤ 1 := hkhalf.trans (by norm_num)
    have H := (sq_le_sq₀ (abs_nonneg k) (by norm_num : (0:ℝ)≤1)).mpr hkabs
    simpa only [sq_abs, one_pow] using H
  have hsmall : 24*M*h*eta*k^2 ≤ eps := by
    calc
      _ ≤ 24*M*1*eta*1 := by gcongr
      _ ≤ (24*M+1)*eta := by nlinarith only [heta.le]
      _ = eps := by dsimp only [eta]; field_simp
  have he : (24*M*(C2+C0)*(Real.sqrt h*h^3*k^2)+48*M*h*eta*k^2)/2 =
      (12*M*(C2+C0))*(Real.sqrt h*h^3*k^2)+24*M*h*eta*k^2 := by ring
  rw [he] at H
  exact H.trans (add_le_add le_rfl hsmall)

def MassVariationLeadingBound (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ k : ℝ, |k| ≤ kap →
      ∀ eps : ℝ, 0 < eps → ∀ᶠ N : ℕ in atTop, ∀ z : ℝ,
        |cornerMassLeadingPart β α r h k N z-
          cornerQuadratic β α (r-h) z*cornerMassVariationPenalty α r h k N| ≤
          C*(Real.sqrt h*h^3*k^2+h^3*|k|^3)+eps

theorem cornerMassLeadingPart_sub_penalty_eventually
    {β : ℝ} {α : ℝ → ℝ} {K : NNReal} {r h k B D P L A : ℝ}
    {dchi : ℝ → ℝ → ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hk : |k| ≤ 1/2)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hP : 0 ≤ P) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hα : LipschitzOnWith K α (Icc (r-h) ((r-h)+4*h)))
    (hder : ∀ t ∈ Icc (r-h) ((r-h)+4*h), ∀ z,
      HasDerivAt (fun u => jet β α 2 u z) (dchi t z) t)
    (hdt : ∀ t ∈ Icc (r-h) ((r-h)+4*h), ∀ z, |dchi t z| ≤ D)
    (hchi : ∀ t ∈ Icc (r-h) ((r-h)+4*h), ∀ z, |jet β α 2 t z| ≤ B)
    (hcoeffA : ∀ z, |3*((β^2)*(jet β α 1 ((r-h)+4*h) z)^2/2+
      2*(β^2)^2*h*jet β α 1 ((r-h)+4*h) z*jet β α 3 ((r-h)+4*h) z-
      2*(r-h)*((β^2)^2*(jet β α 2 ((r-h)+4*h) z)^2/4))| ≤ L)
    (hcoeffB : ∀ z, |(β^2)^2*(jet β α 1 ((r-h)+4*h) z)^2*
      jet β α 2 ((r-h)+4*h) z| ≤ L)
    (hcoeffQ : ∀ z, |(β^2)^2*(jet β α 2 ((r-h)+4*h) z)^2/4| ≤ L)
    (hcontrast : ∀ z, (β^2)^2*(jet β α 1 ((r-h)+4*h) z)^2*
      |jet β α 2 ((r-h)+4*h) z| ≤ A)
    (hJ : Tendsto (fun N => quarticMass (massVariationWindow α (α (r-h)) (1/2) (r-h) h k N)-
      quarticMass (massVariationWindow α (α (r-h)) (1/2) (r-h) h 0 N)) atTop (𝓝 0))
    (hpen : ∀ᶠ N : ℕ in atTop, |cornerMassVariationPenalty α r h k N| ≤ P*h^3*k^2)
    {eps : ℝ} (heps : 0 < eps) : ∀ᶠ N : ℕ in atTop, ∀ z : ℝ,
      |cornerMassLeadingPart β α r h k N z-
        cornerQuadratic β α (r-h) z*cornerMassVariationPenalty α r h k N| ≤
        (A*((8/3:ℝ)*(K:ℝ))^2+2*β^4*B*D*P)*
          (Real.sqrt h*h^3*k^2+h^3*|k|^3)+eps := by
  have hmesh := integrated_windowLeadingEnergy_uniform (b := β^2) (a := α (r-h))
    (p := (1/2:ℝ)) (u := fun z => jet β α 1 ((r-h)+4*h) z)
    (chi := fun z => jet β α 2 ((r-h)+4*h) z)
    (w := fun z => jet β α 3 ((r-h)+4*h) z) hh (by norm_num)
    (OW.repairLength_mem (by norm_num) hk) hα hL hcoeffA hcoeffB hcoeffQ hJ heps
  filter_upwards [hmesh,hpen] with N hmeshN hpenN z
  have hcon := contrast_energy_abs_le (β^2) (jet β α 1 ((r-h)+4*h) z)
    (jet β α 2 ((r-h)+4*h) z) h k (zetaIntegral α (1/2) (r-h) h)
    ((8/3:ℝ)*(K:ℝ)) (by positivity) (zetaIntegral_half_abs_le hh hα)
  have hcon' : |(β^2)^2*(jet β α 1 ((r-h)+4*h) z)^2*
      jet β α 2 ((r-h)+4*h) z*(k^2*(zetaIntegral α (1/2) (r-h) h)^2)| ≤
      (A*((8/3:ℝ)*(K:ℝ))^2)*(Real.sqrt h*h^3*k^2+h^3*|k|^3) := by
    calc
      _ ≤ _ := hcon
      _ ≤ A*((8/3:ℝ)*(K:ℝ))^2*h^4*k^2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hcontrast z) (sq_nonneg _)) (pow_nonneg hh 4)) (sq_nonneg k)
      _ ≤ _ := by
        have H := mul_le_mul_of_nonneg_left (fourth_order_le_corner_error hh hh1 k)
          (by positivity : 0 ≤ A*((8/3:ℝ)*(K:ℝ))^2)
        simpa only [mul_assoc] using H
  have hshift := terminal_initial_penalty_shift hh hh1 hB hD hP hder hdt hchi hpenN z
  let E := (β^2)^2*(jet β α 1 ((r-h)+4*h) z)^2*jet β α 2 ((r-h)+4*h) z*
    (k^2*(zetaIntegral α (1/2) (r-h) h)^2)
  have hmesh' : |cornerMassLeadingPart β α r h k N z-
      cornerQuadratic β α ((r-h)+4*h) z*cornerMassVariationPenalty α r h k N-E| ≤ eps := by
    simpa only [cornerMassLeadingPart, cornerMassVariationPenalty, cornerQuadratic,
      ← pow_mul, E] using hmeshN z
  have he : cornerMassLeadingPart β α r h k N z-
      cornerQuadratic β α (r-h) z*cornerMassVariationPenalty α r h k N =
      (cornerMassLeadingPart β α r h k N z-
        cornerQuadratic β α ((r-h)+4*h) z*cornerMassVariationPenalty α r h k N-E)+E+
      (cornerQuadratic β α ((r-h)+4*h) z-cornerQuadratic β α (r-h) z)*
        cornerMassVariationPenalty α r h k N := by ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add hmesh' hcon') hshift).trans_eq (by ring))

def MassVariationScalarInputs (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ K : NNReal, ∃ B D P L A h0 kap : ℝ,
    0 ≤ B ∧ 0 ≤ D ∧ 0 ≤ P ∧ 0 ≤ L ∧ 0 ≤ A ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 →
      LipschitzOnWith K α (Icc (r-h) ((r-h)+4*h)) ∧
      (∀ t ∈ Icc (r-h) ((r-h)+4*h), ∀ z,
        HasDerivAt (fun u => jet β α 2 u z) (deriv (fun u => jet β α 2 u z) t) t ∧
        |deriv (fun u => jet β α 2 u z) t| ≤ D ∧ |jet β α 2 t z| ≤ B) ∧
      (∀ z,
        |3*((β^2)*(jet β α 1 ((r-h)+4*h) z)^2/2+
          2*(β^2)^2*h*jet β α 1 ((r-h)+4*h) z*jet β α 3 ((r-h)+4*h) z-
          2*(r-h)*((β^2)^2*(jet β α 2 ((r-h)+4*h) z)^2/4))| ≤ L ∧
        |(β^2)^2*(jet β α 1 ((r-h)+4*h) z)^2*jet β α 2 ((r-h)+4*h) z| ≤ L ∧
        |(β^2)^2*(jet β α 2 ((r-h)+4*h) z)^2/4| ≤ L ∧
        (β^2)^2*(jet β α 1 ((r-h)+4*h) z)^2*|jet β α 2 ((r-h)+4*h) z| ≤ A) ∧
      ∀ k : ℝ, |k| ≤ kap →
        Tendsto (fun N => quarticMass (massVariationWindow α (α (r-h)) (1/2) (r-h) h k N)-
          quarticMass (massVariationWindow α (α (r-h)) (1/2) (r-h) h 0 N)) atTop (𝓝 0) ∧
        ∀ᶠ N : ℕ in atTop, |cornerMassVariationPenalty α r h k N| ≤ P*h^3*k^2

theorem massVariationLeadingBound_of_scalarInputs
    {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hscalar : MassVariationScalarInputs β α I) : MassVariationLeadingBound β α I := by
  obtain ⟨K,B,D,P,L,A,hS0,kapS,hB,hD,hP,hL,hA,hhS,hkapS,hscalar⟩ := hscalar
  refine ⟨A*((8/3:ℝ)*(K:ℝ))^2+2*β^4*B*D*P,min hS0 1,min kapS (1/2),
    by positivity,lt_min hhS (by norm_num),lt_min hkapS (by norm_num),?_⟩
  intro r hr h hh hh0 k hk eps heps
  obtain ⟨hα,hjets,hcoeff,hmesh⟩ := hscalar r hr h hh (hh0.trans (min_le_left _ _))
  obtain ⟨hJ,hpen⟩ := hmesh k (hk.trans (min_le_left _ _))
  exact cornerMassLeadingPart_sub_penalty_eventually hh.le (hh0.trans (min_le_right _ _))
    (hk.trans (min_le_right _ _)) hB hD hP hL hA hα
    (fun t ht z => (hjets t ht z).1) (fun t ht z => (hjets t ht z).2.1)
    (fun t ht z => (hjets t ht z).2.2) (fun z => (hcoeff z).1)
    (fun z => (hcoeff z).2.1) (fun z => (hcoeff z).2.2.1) (fun z => (hcoeff z).2.2.2)
    hJ hpen heps

theorem massVariationBound_of_remainder_of_leading
    {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hR : AggregateMassRemainderBound β α I) (hL : MassVariationLeadingBound β α I) :
    MassVariationBound β α I := by
  obtain ⟨CR,hR0,kapR,hCR,hhR,hkapR,hR⟩ := hR
  obtain ⟨CL,hL0,kapL,hCL,hhL,hkapL,hL⟩ := hL
  refine ⟨CR+CL,min hR0 hL0,min kapR kapL,add_nonneg hCR hCL,
    lt_min hhR hhL,lt_min hkapR hkapL,?_⟩
  intro r hr h hh hh0 k hk eps heps
  filter_upwards [hR r hr h hh (hh0.trans (min_le_left _ _)) k (hk.trans (min_le_left _ _))
    (eps/2) (by positivity),
    hL r hr h hh (hh0.trans (min_le_right _ _)) k (hk.trans (min_le_right _ _))
      (eps/2) (by positivity)] with N hRN hLN z
  have he : cornerMassVariation β α r h k N z-
      cornerQuadratic β α (r-h) z*cornerMassVariationPenalty α r h k N =
      cornerMassRemainder β α r h k N z+
        (cornerMassLeadingPart β α r h k N z-
          cornerQuadratic β α (r-h) z*cornerMassVariationPenalty α r h k N) := by
    unfold cornerMassRemainder
    ring
  rw [he]
  calc
    _ ≤ |cornerMassRemainder β α r h k N z|+
        |cornerMassLeadingPart β α r h k N z-
          cornerQuadratic β α (r-h) z*cornerMassVariationPenalty α r h k N| := abs_add_le _ _
    _ ≤ (CR*(Real.sqrt h*h^3*k^2)+eps/2)+
        (CL*(Real.sqrt h*h^3*k^2+h^3*|k|^3)+eps/2) := add_le_add (hRN z) (hLN z)
    _ ≤ _ := by nlinarith only [mul_nonneg hCR (mul_nonneg (pow_nonneg hh.le 3)
        (pow_nonneg (abs_nonneg k) 3))]

theorem massVariationBound_of_sensitivityInputs
    {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hsecond : MassSensitivityC2 β α I) (hvalue : MassSensitivityValueBound β α I)
    (hweights : WindowMassWeightBounds β α I)
    (hregular : UniformMassVariationRegularity β α I)
    (hscalar : MassVariationScalarInputs β α I) : MassVariationBound β α I := by
  exact massVariationBound_of_remainder_of_leading
    (aggregateMassRemainderBound_of_sensitivityInputs hsecond hvalue hweights hregular)
    (massVariationLeadingBound_of_scalarInputs hscalar)

end SKBarriers2.Corner
