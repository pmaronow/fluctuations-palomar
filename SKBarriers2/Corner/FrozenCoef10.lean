module

public import SKBarriers2.Corner.FrozenOriginalNoise
public import SKBarriers2.Main.Leaves

@[expose] public section

noncomputable section
open scoped BigOperators Matrix ContDiff Topology NNReal
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

theorem scalarData_frozenOriginalAffine_control {β : ℝ} (D : ScalarData β) :
    ∃ M h₀ : ℝ, 0 < M ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ a s h z : ℝ, a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ →
      s + 4 * h ∈ Icc (0 : ℝ) 1 → ∀ i : Fin 3,
        VectorAffineRegularOn
          (frozenOriginalAffine β a (jet β (cdf (D.μ : Measure ℝ)) 1 (s + 4 * h) z)
            (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h z i)
          (frozenOriginalAffineFirst β a (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h i)
          (frozenOriginalAffineSecond β a (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h i)
          (Ioo (-(1 / 2) : ℝ) (1 / 2)) ∧
        VectorAffineScaleBound
          (frozenOriginalAffine β a (jet β (cdf (D.μ : Measure ℝ)) 1 (s + 4 * h) z)
            (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h z i)
          (frozenOriginalAffineFirst β a (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h i)
          (frozenOriginalAffineSecond β a (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h i)
          (Ioo (-(1 / 2) : ℝ) (1 / 2)) z M (Real.sqrt h) := by
  let B := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  obtain ⟨M, h₀, hM, hh₀, hh₁, H⟩ := frozenOriginalAffine_uniform_control β B hB
  refine ⟨M, h₀, hM, hh₀, hh₁, ?_⟩
  intro a s h z ha hh hh₀' ht i
  exact H a _ _ h z ha
    ((scalarData_jet_le D le_rfl (by norm_num : 1 ≤ 2) ht z).trans (by dsimp only [B]; linarith))
    ((scalarData_jet_le D (by norm_num : 1 ≤ 2) le_rfl ht z).trans (by dsimp only [B]; linarith))
    hh hh₀' i

def affineNoisePullback {n d : ℕ} (A : Fin (d + 1) → ℝ → ℝ)
    (P : Fin d → Fin n → ℝ) : Fin (n + 1) → ℝ → ℝ :=
  Fin.cons (A 0) (fun j k => ∑ i : Fin d, A i.succ k * P i j)

theorem VectorAffineRegularOn.noisePullback {n d : ℕ}
    {A A₁ A₂ : Fin (d + 1) → ℝ → ℝ} {U : Set ℝ}
    (H : VectorAffineRegularOn A A₁ A₂ U) (P : Fin d → Fin n → ℝ) :
    VectorAffineRegularOn (affineNoisePullback A P) (affineNoisePullback A₁ P)
      (affineNoisePullback A₂ P) U := by
  intro k hk j
  refine Fin.cases (H k hk 0) (fun j => ?_) j
  change HasDerivAt (fun k => ∑ i : Fin d, A i.succ k * P i j)
      (∑ i : Fin d, A₁ i.succ k * P i j) k ∧
    HasDerivAt (fun k => ∑ i : Fin d, A₁ i.succ k * P i j)
      (∑ i : Fin d, A₂ i.succ k * P i j) k
  exact ⟨HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => (H k hk i.succ).1.mul_const (P i j)),
    HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => (H k hk i.succ).2.mul_const (P i j))⟩

theorem VectorAffineScaleBound.noisePullback {n d : ℕ}
    {A A₁ A₂ : Fin (d + 1) → ℝ → ℝ} {U : Set ℝ} {z M ρ : ℝ}
    (H : VectorAffineScaleBound A A₁ A₂ U z M ρ)
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hd : 1 ≤ d) (P : Fin d → Fin n → ℝ)
    (hP : ∀ i j, |P i j| ≤ 1) :
    VectorAffineScaleBound (affineNoisePullback A P) (affineNoisePullback A₁ P)
      (affineNoisePullback A₂ P) U z ((d : ℝ) * M) ρ := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hen : M * ρ ≤ ((d : ℝ) * M) * ρ := by nlinarith [mul_nonneg hM hρ]
  intro k hk j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact ⟨(H k hk 0).1.trans hen, (H k hk 0).2.1.trans hen, (H k hk 0).2.2.trans hen⟩
  · have hs {B : Fin d → ℝ} (hB : ∀ i, |B i| ≤ M * ρ) :
        |∑ i : Fin d, B i * P i j| ≤ ((d : ℝ) * M) * ρ := by
      calc
        _ ≤ ∑ i : Fin d, |B i * P i j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ : Fin d, M * ρ := Finset.sum_le_sum (fun i _ => by
          rw [abs_mul]
          exact (mul_le_mul (hB i) (hP i j) (abs_nonneg _) (mul_nonneg hM hρ)).trans_eq (mul_one _))
        _ = _ := by simp; ring
    change |(∑ i : Fin d, A i.succ k * P i j) - 0| ≤ _ ∧
      |∑ i : Fin d, A₁ i.succ k * P i j| ≤ _ ∧ |∑ i : Fin d, A₂ i.succ k * P i j| ≤ _
    exact ⟨by simpa only [sub_zero] using hs (fun i => by simpa using (H k hk i.succ).1),
      hs (fun i => (H k hk i.succ).2.1), hs (fun i => (H k hk i.succ).2.2)⟩

theorem gaussianVectorAffine_noisePullback {n d : ℕ}
    (A : Fin (d + 1) → ℝ → ℝ) (P : Fin d → Fin n → ℝ) (k : ℝ) (g : Fin n → ℝ) :
    gaussianVectorAffine (affineNoisePullback A P) k g =
      gaussianVectorAffine A k (fun i => ∑ j : Fin n, P i j * g j) := by
  simp only [gaussianVectorAffine, affineNoisePullback, Fin.cons_zero, Fin.cons_succ,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl (fun j _ => by ring)

def joinLabelNoise {ι : Type} [DecidableEq ι] (l t : List ι)
    (p : Fin l.length → ℝ) (a : Fin t.length → ℝ) (j : ι) : ℝ :=
  if hj : j ∈ l then p ⟨l.idxOf j, List.idxOf_lt_length_of_mem hj⟩
  else if hj : j ∈ t then a ⟨t.idxOf j, List.idxOf_lt_length_of_mem hj⟩ else 0

private theorem joinLabelNoise_prefix {ι : Type} [DecidableEq ι]
    (l t : List ι) (hl : l.Nodup) (p : Fin l.length → ℝ) (a : Fin t.length → ℝ)
    (j : Fin l.length) : joinLabelNoise l t p a l[j.val] = p j := by
  have hj : l[j.val] ∈ l := List.getElem_mem j.isLt
  simp only [joinLabelNoise, dite_eq_left hj, hl.idxOf_getElem j]

private theorem joinLabelNoise_suffix {ι : Type} [DecidableEq ι]
    (l t : List ι) (ht : t.Nodup) (hdisj : l.Disjoint t)
    (p : Fin l.length → ℝ) (a : Fin t.length → ℝ) (j : Fin t.length) :
    joinLabelNoise l t p a t[j.val] = a j := by
  have hj : t[j.val] ∈ t := List.getElem_mem j.isLt
  have hnot : t[j.val] ∉ l := fun h => List.disjoint_left.mp hdisj h hj
  simp only [joinLabelNoise, dite_eq_right hnot, dite_eq_left hj, ht.idxOf_getElem j]

theorem labelledQuadraticPath_join_prefix {ι : Type} [DecidableEq ι]
    (m : ι → ℝ) (v : ι → Vec3) (l t : List ι) (hl : l.Nodup)
    (Q : QuadraticTerminal) (x : Vec3) (p : Fin l.length → ℝ) (a : Fin t.length → ℝ) :
    labelledQuadraticPath m v l Q x (joinLabelNoise l t p a) =
      quadraticNoisePath (l.map (fun j => (m j, v j))) Q x
        (fun j => p ⟨j.val, by simpa using j.isLt⟩) := by
  rw [labelledQuadraticPath_eq_original]
  congr 1
  funext j
  exact joinLabelNoise_prefix l t hl p a ⟨j.val, by simpa using j.isLt⟩

theorem labelledQuadraticPath_join_suffix {ι : Type} [DecidableEq ι]
    (m : ι → ℝ) (v : ι → Vec3) (l t : List ι) (ht : t.Nodup) (hdisj : l.Disjoint t)
    (Q : QuadraticTerminal) (x : Vec3) (p : Fin l.length → ℝ) (a : Fin t.length → ℝ) :
    labelledQuadraticPath m v t Q x (joinLabelNoise l t p a) =
      quadraticNoisePath (t.map (fun j => (m j, v j))) Q x
        (fun j => a ⟨j.val, by simpa using j.isLt⟩) := by
  rw [labelledQuadraticPath_eq_original]
  congr 1
  funext j
  exact joinLabelNoise_suffix l t ht hdisj p a ⟨j.val, by simpa using j.isLt⟩

abbrev LabelNoiseIndex (l t : List (Fin 12)) := Fin l.length ⊕ (Fin t.length ⊕ Fin t.length)

def labelNoiseIndexEquiv (m : Fin 12 → ℝ) (v : Fin 12 → Vec3) (l t : List (Fin 12)) :
    OriginalSharedNoiseIndex (l.map (fun j => (m j, v j))) (t.map (fun j => (m j, v j))) ≃
      LabelNoiseIndex l t :=
  Equiv.sumCongr (finCongr (List.length_map (f := fun j => (m j, v j))))
    (Equiv.sumCongr (finCongr (List.length_map (f := fun j => (m j, v j))))
      (finCongr (List.length_map (f := fun j => (m j, v j)))))

def sharedJoinedNoise (l t : List (Fin 12)) (right : Bool)
    (g : Fin (Fintype.card (LabelNoiseIndex l t)) → ℝ) : Fin 12 → ℝ :=
  let G := fun j => g (Fintype.equivFin (LabelNoiseIndex l t) j)
  joinLabelNoise l t (fun j => G (.inl j))
    (fun j => G (.inr (if right then .inr j else .inl j)))

def sharedJoinedNoiseLinearMap (l t : List (Fin 12)) (right : Bool) :
    (Fin (Fintype.card (LabelNoiseIndex l t)) → ℝ) →ₗ[ℝ] (Fin 12 → ℝ) where
  toFun := sharedJoinedNoise l t right
  map_add' g w := by
    funext j
    unfold sharedJoinedNoise joinLabelNoise
    split_ifs <;> simp_all
  map_smul' c g := by
    funext j
    unfold sharedJoinedNoise joinLabelNoise
    split_ifs <;> simp_all

def sharedNoiseMatrix (l t : List (Fin 12)) (right : Bool) :
    Fin 12 → Fin (Fintype.card (LabelNoiseIndex l t)) → ℝ :=
  fun i j => sharedJoinedNoise l t right (Pi.single j 1) i

theorem sharedNoiseMatrix_bound (l t : List (Fin 12)) (right : Bool)
    (i : Fin 12) (j : Fin (Fintype.card (LabelNoiseIndex l t))) :
    |sharedNoiseMatrix l t right i j| ≤ 1 := by
  unfold sharedNoiseMatrix sharedJoinedNoise joinLabelNoise
  split_ifs <;> simp_all [Pi.single_apply] <;> split_ifs <;> norm_num

theorem sharedJoinedNoise_eq_sum (l t : List (Fin 12)) (right : Bool)
    (g : Fin (Fintype.card (LabelNoiseIndex l t)) → ℝ) (i : Fin 12) :
    sharedJoinedNoise l t right g i =
      ∑ j, sharedNoiseMatrix l t right i j * g j := by
  have hg : g = ∑ j, g j • Pi.single j (1 : ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have H := congrArg (sharedJoinedNoiseLinearMap l t right) hg
  simp only [map_sum, map_smul] at H
  have Hi := congrFun H i
  simpa only [sharedJoinedNoiseLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sharedNoiseMatrix, mul_comm] using Hi

theorem originalSharedNoiseProduct_labelled
    (m : Fin 12 → ℝ) (v : Fin 12 → Vec3) (l t : List (Fin 12))
    (hlt : l ++ t = List.finRange 12) (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3)
    (G : LabelNoiseIndex l t → ℝ) :
    originalSharedNoiseProduct (l.map (fun j => (m j, v j)))
      (t.map (fun j => (m j, v j))) Q K x (G ∘ labelNoiseIndexEquiv m v l t) =
      K (labelledQuadraticPath m v (List.finRange 12) Q x
        (joinLabelNoise l t (fun j => G (.inl j)) (fun j => G (.inr (.inl j))))) *
      K (labelledQuadraticPath m v (List.finRange 12) Q x
        (joinLabelNoise l t (fun j => G (.inl j)) (fun j => G (.inr (.inr j))))) := by
  have hN : (l ++ t).Nodup := hlt.symm ▸ List.nodup_finRange 12
  obtain ⟨hl, ht, hdisj⟩ := List.nodup_append'.mp hN
  have HE (a : Fin t.length → ℝ) :
      labelledQuadraticPath m v (List.finRange 12) Q x
          (joinLabelNoise l t (fun j => G (.inl j)) a) =
        quadraticNoisePath (t.map (fun j => (m j, v j))) Q
          (quadraticNoisePath (l.map (fun j => (m j, v j)))
            (riccatiRecursion (t.map (fun j => (m j, v j))) Q) x
            (fun j => G (.inl ⟨j.val, by simpa using j.isLt⟩)))
          (fun j => a ⟨j.val, by simpa using j.isLt⟩) := by
    rw [← hlt, labelledQuadraticPath_append,
      labelledQuadraticPath_join_suffix m v l t ht hdisj,
      labelledQuadraticPath_join_prefix m v l t hl]
  rw [HE, HE]
  rfl

theorem originalConditionalSquare_eq_labelled_gaussian
    (m : Fin 12 → ℝ) (v : Fin 12 → Vec3) (l t : List (Fin 12))
    (hlt : l ++ t = List.finRange 12) (Q : QuadraticTerminal)
    {K : Vec3 → ℝ} (hc : Continuous K) (hg : HasExpGrowth K) (x : Vec3) :
    originalConditionalSquare (l.map (fun j => (m j, v j)))
      (t.map (fun j => (m j, v j))) Q K x =
      ∫ g, K (labelledQuadraticPath m v (List.finRange 12) Q x (sharedJoinedNoise l t false g)) *
        K (labelledQuadraticPath m v (List.finRange 12) Q x (sharedJoinedNoise l t true g))
        ∂standardGaussianVector (Fintype.card (LabelNoiseIndex l t)) := by
  rw [originalConditionalSquare_eq_pi _ _ Q hc hg x]
  let e := (labelNoiseIndexEquiv m v l t).trans (Fintype.equivFin (LabelNoiseIndex l t))
  let F := originalSharedNoiseProduct (l.map (fun j => (m j, v j)))
    (t.map (fun j => (m j, v j))) Q K x
  have H := (measurePreserving_piCongrLeft
    (fun _ : OriginalSharedNoiseIndex (l.map (fun j => (m j, v j)))
      (t.map (fun j => (m j, v j))) => gaussianReal 0 1) e.symm).integral_comp' F
  have he (g : Fin (Fintype.card (LabelNoiseIndex l t)) → ℝ) :
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e.symm) g = fun j => g (e j) := by
    funext j
    simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
      Equiv.symm_symm, eq_rec_constant]
  have H' : (∫ g, F g ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ g, F (fun j => g (e j)) ∂standardGaussianVector (Fintype.card (LabelNoiseIndex l t)) := by
    simpa only [he, standardGaussianVector] using H.symm
  rw [H']
  apply integral_congr_ae
  apply ae_of_all
  intro g
  exact originalSharedNoiseProduct_labelled m v l t hlt Q K x
    (fun j => g (Fintype.equivFin (LabelNoiseIndex l t) j))

def sharedOriginalAffine (β a u χ h z : ℝ) (l t : List (Fin 12)) (right : Bool)
    (i : Fin 3) : Fin (Fintype.card (LabelNoiseIndex l t) + 1) → ℝ → ℝ :=
  affineNoisePullback (frozenOriginalAffine β a u χ h z i) (sharedNoiseMatrix l t right)

def sharedOriginalAffineFirst (β a χ h : ℝ) (l t : List (Fin 12)) (right : Bool)
    (i : Fin 3) : Fin (Fintype.card (LabelNoiseIndex l t) + 1) → ℝ → ℝ :=
  affineNoisePullback (frozenOriginalAffineFirst β a χ h i) (sharedNoiseMatrix l t right)

def sharedOriginalAffineSecond (β a χ h : ℝ) (l t : List (Fin 12)) (right : Bool)
    (i : Fin 3) : Fin (Fintype.card (LabelNoiseIndex l t) + 1) → ℝ → ℝ :=
  affineNoisePullback (frozenOriginalAffineSecond β a χ h i) (sharedNoiseMatrix l t right)

theorem sharedOriginalAffine_represents (β a c u χ h z k : ℝ) (hh : 0 ≤ h)
    (hk : |k| ≤ 1 / 2)
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z))
    (l t : List (Fin 12)) (right : Bool)
    (g : Fin (Fintype.card (LabelNoiseIndex l t)) → ℝ) (i : Fin 3) :
    labelledQuadraticPath (fun j => a * frozenUnitMass j)
      (fun j => Real.sqrt h • frozenUnitDirection β k j) (List.finRange 12)
      (separableTaylorQuadratic c u χ z) (fun _ => z) (sharedJoinedNoise l t right g) i =
      gaussianVectorAffine (sharedOriginalAffine β a u χ h z l t right i) k g := by
  rw [frozenOriginalAffine_represents β a c u χ h z k hh hk hQ]
  unfold sharedOriginalAffine
  rw [gaussianVectorAffine_noisePullback]
  congr 1
  funext i
  exact sharedJoinedNoise_eq_sum l t right g i

theorem scalarData_sharedOriginalAffine_control {β : ℝ} (D : ScalarData β) :
    ∃ M h₀ : ℝ, 0 < M ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ a s h z : ℝ, a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ →
      s + 4 * h ∈ Icc (0 : ℝ) 1 → ∀ (l t : List (Fin 12)) (right : Bool) (i : Fin 3),
        VectorAffineRegularOn
          (sharedOriginalAffine β a (jet β (cdf (D.μ : Measure ℝ)) 1 (s + 4 * h) z)
            (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h z l t right i)
          (sharedOriginalAffineFirst β a (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h l t right i)
          (sharedOriginalAffineSecond β a (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h l t right i)
          (Ioo (-(1 / 2) : ℝ) (1 / 2)) ∧
        VectorAffineScaleBound
          (sharedOriginalAffine β a (jet β (cdf (D.μ : Measure ℝ)) 1 (s + 4 * h) z)
            (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h z l t right i)
          (sharedOriginalAffineFirst β a (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h l t right i)
          (sharedOriginalAffineSecond β a (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h l t right i)
          (Ioo (-(1 / 2) : ℝ) (1 / 2)) z M (Real.sqrt h) := by
  obtain ⟨M, η, hM, hη, hη₁, H⟩ := scalarData_frozenOriginalAffine_control D
  refine ⟨12 * M, η, by positivity, hη, hη₁, ?_⟩
  intro a s h z ha hh hhη ht l t right i
  have Hi := H a s h z ha hh hhη ht i
  exact ⟨Hi.1.noisePullback _, Hi.2.noisePullback hM.le (Real.sqrt_nonneg h)
    (by norm_num) _ (sharedNoiseMatrix_bound l t right)⟩

private theorem noise_growth_affine {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} (hf : HasExpGrowth f) (c : F) (L : E →L[ℝ] F) :
    HasExpGrowth (fun x => f (c + L x)) := by
  obtain ⟨C, M, hC, hM, hb⟩ := hf
  refine ⟨C * Real.exp (M * ‖c‖), M * ‖L‖, by positivity, by positivity, ?_⟩
  intro x
  calc
    _ ≤ C * Real.exp (M * ‖c + L x‖) := hb _
    _ ≤ C * Real.exp (M * (‖c‖ + ‖L‖ * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
          (add_le_add (le_refl ‖c‖) (L.le_opNorm x))) hM)) hC
    _ = _ := by rw [mul_add, ← mul_assoc M ‖L‖ ‖x‖, Real.exp_add]; ring

private theorem affine_scalar_regular {n : ℕ} {f : ℝ → ℝ}
    (hc : Continuous f) (hg : HasExpGrowth f) (A : Fin (n + 1) → ℝ → ℝ) (k : ℝ) :
    Continuous (fun g => f (gaussianVectorAffine A k g)) ∧
      HasExpGrowth (fun g => f (gaussianVectorAffine A k g)) := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    ∑ j : Fin n, (A j.succ k) • LinearMap.proj j
  have he (g : Fin n → ℝ) : L g = ∑ j, A j.succ k * g j := by
    simp [L, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have he' : (fun g => f (gaussianVectorAffine A k g)) =
      fun g => f (A 0 k + L.toContinuousLinearMap g) := by
    funext g
    simp only [gaussianVectorAffine, LinearMap.coe_toContinuousLinearMap', he]
  rw [he']
  exact ⟨hc.comp (continuous_const.add L.toContinuousLinearMap.continuous),
    noise_growth_affine hg _ _⟩

private theorem scalarTaylorPolynomial_regular (f : ℝ → ℝ) (n : ℕ) (z : ℝ) :
    Continuous (scalarTaylorPolynomial f n z) ∧ HasExpGrowth (scalarTaylorPolynomial f n z) := by
  have hid : HasExpGrowth (fun y : ℝ => y) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  have hg := hid.sub_real (HasExpGrowth.const z)
  constructor
  · unfold scalarTaylorPolynomial
    fun_prop
  · exact HasExpGrowth.finsetSum _ _ (fun j _ =>
      ((HasExpGrowth.const _).mul (hg.pow j)).mul (HasExpGrowth.const _))

private theorem scalarTaylorParts_regular {f : ℝ → ℝ} (hc : Continuous f)
    (hg : HasExpGrowth f) (z : ℝ) :
    (Continuous (quadraticTaylorTail f z) ∧ HasExpGrowth (quadraticTaylorTail f z)) ∧
      (Continuous (scalarCubicPart f z) ∧ HasExpGrowth (scalarCubicPart f z)) := by
  have hp := scalarTaylorPolynomial_regular f 2 z
  have hid : HasExpGrowth (fun y : ℝ => y) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  refine ⟨⟨hc.sub hp.1, hg.sub_real hp.2⟩, ?_⟩
  exact ⟨by unfold scalarCubicPart; fun_prop,
    (HasExpGrowth.const _).mul ((hid.sub_real (HasExpGrowth.const z)).pow 3)⟩

theorem gaussianTaylorSumError_eq {n : ℕ} {f : ℝ → ℝ}
    (hc : Continuous f) (hg : HasExpGrowth f) (z : ℝ)
    (A B : Fin 3 → Fin (n + 1) → ℝ → ℝ) (k : ℝ) :
    (∫ g, (∑ i : Fin 3, quadraticTaylorTail f z (gaussianVectorAffine (A i) k g)) *
        (∑ j : Fin 3, quadraticTaylorTail f z (gaussianVectorAffine (B j) k g))
        ∂standardGaussianVector n) -
      (∫ g, (∑ i : Fin 3, scalarCubicPart f z (gaussianVectorAffine (A i) k g)) *
        (∑ j : Fin 3, scalarCubicPart f z (gaussianVectorAffine (B j) k g))
        ∂standardGaussianVector n) =
      ∑ i : Fin 3, ∑ j : Fin 3, vectorTaylorTailError f z (A i) (B j) k := by
  have hp := scalarTaylorParts_regular hc hg z
  have hiR (i j : Fin 3) : Integrable (fun g =>
      quadraticTaylorTail f z (gaussianVectorAffine (A i) k g) *
      quadraticTaylorTail f z (gaussianVectorAffine (B j) k g)) (standardGaussianVector n) := by
    have hA := affine_scalar_regular hp.1.1 hp.1.2 (A i) k
    have hB := affine_scalar_regular hp.1.1 hp.1.2 (B j) k
    exact hasExpGrowth_integrable_standardGaussianVector (hA.1.mul hB.1) (hA.2.mul hB.2)
  have hiC (i j : Fin 3) : Integrable (fun g =>
      scalarCubicPart f z (gaussianVectorAffine (A i) k g) *
      scalarCubicPart f z (gaussianVectorAffine (B j) k g)) (standardGaussianVector n) := by
    have hA := affine_scalar_regular hp.2.1 hp.2.2 (A i) k
    have hB := affine_scalar_regular hp.2.1 hp.2.2 (B j) k
    exact hasExpGrowth_integrable_standardGaussianVector (hA.1.mul hB.1) (hA.2.mul hB.2)
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hiR i j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hiC i j)),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hiR i j), integral_finsetSum _ (fun j _ => hiC i j),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => (integral_sub (hiR i j) (hiC i j)).symm)

def labelledTailSquareError (β : ℝ) (α : ℝ → ℝ) (a s h z : ℝ)
    (l t : List (Fin 12)) (k : ℝ) : ℝ :=
  let m := fun j => a * frozenUnitMass j
  let v := fun j => Real.sqrt h • frozenUnitDirection β k j
  let Q := terminalTaylorQuadratic β α s h z
  originalConditionalSquare (l.map (fun j => (m j, v j))) (t.map (fun j => (m j, v j)))
      Q (terminalResidual β α s h z) (fun _ => z) -
    originalConditionalSquare (l.map (fun j => (m j, v j))) (t.map (fun j => (m j, v j)))
      Q (terminalCubicResidual β α s h z) (fun _ => z)

theorem labelledTailSquareError_eq_sum (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (l t : List (Fin 12))
    (hlt : l ++ t = List.finRange 12) (hφ : BoundedDerivs (Phi β α (s + 4 * h)))
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)) :
    labelledTailSquareError β α a s h z l t k =
      ∑ i : Fin 3, ∑ j : Fin 3,
        vectorTaylorTailError (Phi β α (s + 4 * h)) z
          (sharedOriginalAffine β a (jet β α 1 (s + 4 * h) z)
            (jet β α 2 (s + 4 * h) z) h z l t false i)
          (sharedOriginalAffine β a (jet β α 1 (s + 4 * h) z)
            (jet β α 2 (s + 4 * h) z) h z l t true j) k := by
  have hP := terminalCubicResidual_continuous_expGrowth β α s h z
  dsimp only [labelledTailSquareError]
  rw [originalConditionalSquare_eq_labelled_gaussian _ _ l t hlt _
      (terminalResidual_continuous β α s h z hφ) (terminalResidual_hasExpGrowth β α s h z hφ),
    originalConditionalSquare_eq_labelled_gaussian _ _ l t hlt _ hP.1 hP.2]
  have HR (right : Bool) (g : Fin (Fintype.card (LabelNoiseIndex l t)) → ℝ) :
      terminalResidual β α s h z
        (labelledQuadraticPath (fun j => a * frozenUnitMass j)
          (fun j => Real.sqrt h • frozenUnitDirection β k j) (List.finRange 12)
          (terminalTaylorQuadratic β α s h z) (fun _ => z) (sharedJoinedNoise l t right g)) =
      ∑ i : Fin 3, quadraticTaylorTail (Phi β α (s + 4 * h)) z
        (gaussianVectorAffine (sharedOriginalAffine β a (jet β α 1 (s + 4 * h) z)
          (jet β α 2 (s + 4 * h) z) h z l t right i) k g) := by
    rw [terminalResidual_eq_quadraticTaylorTails]
    apply Finset.sum_congr rfl
    intro i _
    unfold terminalTaylorQuadratic
    rw [sharedOriginalAffine_represents β a _ _ _ h z k hh hk hQ]
  have HC (right : Bool) (g : Fin (Fintype.card (LabelNoiseIndex l t)) → ℝ) :
      terminalCubicResidual β α s h z
        (labelledQuadraticPath (fun j => a * frozenUnitMass j)
          (fun j => Real.sqrt h • frozenUnitDirection β k j) (List.finRange 12)
          (terminalTaylorQuadratic β α s h z) (fun _ => z) (sharedJoinedNoise l t right g)) =
      ∑ i : Fin 3, scalarCubicPart (Phi β α (s + 4 * h)) z
        (gaussianVectorAffine (sharedOriginalAffine β a (jet β α 1 (s + 4 * h) z)
          (jet β α 2 (s + 4 * h) z) h z l t right i) k g) := by
    unfold terminalCubicResidual
    apply Finset.sum_congr rfl
    intro i _
    unfold terminalTaylorQuadratic
    rw [sharedOriginalAffine_represents β a _ _ _ h z k hh hk hQ]
    unfold scalarCubicPart jet
    ring
  simp only [HR, HC]
  exact gaussianTaylorSumError_eq hφ.1.continuous hφ.hasExpGrowth z _ _ k

theorem scalarData_labelledTailSquareError_control {β : ℝ} (D : ScalarData β) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ a s h z : ℝ, a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ →
      s + 4 * h ∈ Icc (0 : ℝ) 1 → ∀ l t : List (Fin 12),
      l ++ t = List.finRange 12 → ∃ f₁ f₂ : ℝ → ℝ,
        ∀ k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2),
          HasDerivAt (labelledTailSquareError β (cdf (D.μ : Measure ℝ)) a s h z l t) (f₁ k) k ∧
          HasDerivAt f₁ (f₂ k) k ∧ |f₂ k| ≤ C * Real.sqrt h * h ^ 3 := by
  obtain ⟨M, η, hM, hη, hη₁, H⟩ := scalarData_sharedOriginalAffine_control D
  choose C hC HC using fun n : Fin 25 => scalarData_vectorTaylorTailError_control D n.val M hM.le
  let S := ∑ n : Fin 25, C n
  have hS : 0 < S := Finset.sum_pos (fun n _ => hC n) (by simp)
  have hCS (n : Fin 25) : C n ≤ S :=
    Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ n)
  let B := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  obtain ⟨ξ, hξ, HQ⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  refine ⟨9 * S, min η ξ, by positivity, by positivity, (min_le_left _ _).trans hη₁, ?_⟩
  intro a s h z ha hh hh₀ ht l t hlt
  have hn : Fintype.card (LabelNoiseIndex l t) < 25 := by
    have he := congrArg List.length hlt
    simp only [List.length_append, List.length_finRange] at he
    simp only [LabelNoiseIndex, Fintype.card_sum, Fintype.card_fin]
    omega
  let n : Fin 25 := ⟨_, hn⟩
  have hcoef := H a s h z ha hh (hh₀.trans (min_le_left _ _)) ht l t
  let A := sharedOriginalAffine β a (jet β (cdf (D.μ : Measure ℝ)) 1 (s + 4 * h) z)
    (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h z l t
  let A₁ := sharedOriginalAffineFirst β a (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h l t
  let A₂ := sharedOriginalAffineSecond β a (jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z) h l t
  have hij (i j : Fin 3) := HC n s h z hh (hh₀.trans ((min_le_left _ _).trans hη₁)) ht
    _ isOpen_Ioo (A false i) (A₁ false i) (A₂ false i) (A true j) (A₁ true j) (A₂ true j)
    (hcoef false i).1 (hcoef true j).1 (hcoef false i).2 (hcoef true j).2
  choose f₁ f₂ hf using hij
  have he (k : ℝ) (hk : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
      labelledTailSquareError β (cdf (D.μ : Measure ℝ)) a s h z l t k =
        ∑ i : Fin 3, ∑ j : Fin 3,
          vectorTaylorTailError (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z
            (A false i) (A true j) k := by
    have hk' : |k| ≤ 1 / 2 := (abs_le.mpr ⟨hk.1.le, hk.2.le⟩)
    exact labelledTailSquareError_eq_sum β _ a s h z k hh hk' l t hlt
      (scalarData_phi_regular D ht)
      (HQ _ a s h k z ha hh (hh₀.trans (min_le_right _ _)) hk'
        ((scalarData_jet_le D (by norm_num) le_rfl ht z).trans (by dsimp only [B]; linarith)))
  refine ⟨fun k => ∑ i : Fin 3, ∑ j : Fin 3, f₁ i j k,
    fun k => ∑ i : Fin 3, ∑ j : Fin 3, f₂ i j k, ?_⟩
  intro k hk
  have hd := HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    HasDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => (hf i j k hk).1))
  have hd₂ := HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    HasDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => (hf i j k hk).2.1))
  have hevent : (fun k => ∑ i : Fin 3, ∑ j : Fin 3,
      vectorTaylorTailError (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z
        (A false i) (A true j) k) =ᶠ[𝓝 k]
      labelledTailSquareError β (cdf (D.μ : Measure ℝ)) a s h z l t :=
    by
      filter_upwards [isOpen_Ioo.mem_nhds hk] with k hk
      exact (he k hk).symm
  refine ⟨hd.congr_of_eventuallyEq hevent.symm, hd₂, ?_⟩
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |f₂ i j k| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, C n * Real.sqrt h * h ^ 3 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => (hf i j k hk).2.2.2.2))
    _ = (9 * C n) * Real.sqrt h * h ^ 3 := by simp; ring
    _ ≤ (9 * S) * Real.sqrt h * h ^ 3 := by gcongr; exact hCS n

def frozenSquareTail (β : ℝ) (α : ℝ → ℝ) (a s h z : ℝ) (j : ℕ) (k : ℝ) : ℝ :=
  let L := frozenSchedule β a (1 / 2) h k
  let Q := terminalTaylorQuadratic β α s h z
  originalConditionalSquare (L.take j) (L.drop j) Q (terminalResidual β α s h z) (fun _ => z) -
    originalConditionalSquare (L.take j) (L.drop j) Q (terminalCubicResidual β α s h z) (fun _ => z)

theorem frozenSquareTail_eq_labelled (β : ℝ) (α : ℝ → ℝ) (a s h z : ℝ)
    (j : ℕ) (k : ℝ) (hh : 0 ≤ h) :
    frozenSquareTail β α a s h z j k =
      labelledTailSquareError β α a s h z ((List.finRange 12).take j) ((List.finRange 12).drop j) k := by
  dsimp only [frozenSquareTail, labelledTailSquareError]
  rw [frozenSchedule_eq_labelled β a h k hh, ← List.map_take, ← List.map_drop]

theorem originalFrozenSecond_tail_eq (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ) :
    originalFrozenSecond β a h k (terminalTaylorQuadratic β α s h z)
        (terminalResidual β α s h z) (fun _ => z) -
      originalFrozenSecond β a h k (terminalTaylorQuadratic β α s h z)
        (terminalCubicResidual β α s h z) (fun _ => z) =
      a * frozenSquareTail β α a s h z 12 k -
        a / 2 * frozenSquareTail β α a s h z 2 k -
        a / 6 * frozenSquareTail β α a s h z 1 k -
        a / 3 * frozenSquareTail β α a s h z 0 k := by
  have h12 : (frozenSchedule β a (1 / 2) h k).take 12 = frozenSchedule β a (1 / 2) h k := by
    rw [← frozenSchedule_length β a (1 / 2) h k, List.take_length]
  have hd12 : (frozenSchedule β a (1 / 2) h k).drop 12 = [] := by
    rw [← frozenSchedule_length β a (1 / 2) h k, List.drop_length]
  have h2 : (frozenSchedule β a (1 / 2) h k).take 2 =
      frozenCommon β a (1 / 2) h k ++ frozenShared β a (1 / 2) h k := rfl
  have hd2 : (frozenSchedule β a (1 / 2) h k).drop 2 = frozenInner β a (1 / 2) h k := rfl
  have h1 : (frozenSchedule β a (1 / 2) h k).take 1 = frozenCommon β a (1 / 2) h k := rfl
  have hd1 : (frozenSchedule β a (1 / 2) h k).drop 1 =
      frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k := rfl
  simp only [frozenSquareTail, h12, hd12, h2, hd2, h1, hd1, List.take_zero, List.drop_zero,
    originalFrozenSecond]
  ring

theorem scalarData_frozenSecondTail_control {β : ℝ} (D : ScalarData β) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ a s h z : ℝ, a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ →
      s + 4 * h ∈ Icc (0 : ℝ) 1 → ∃ f₁ f₂ : ℝ → ℝ,
        ∀ k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2),
          HasDerivAt (fun k =>
            originalFrozenSecond β a h k (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
                (terminalResidual β (cdf (D.μ : Measure ℝ)) s h z) (fun _ => z) -
              originalFrozenSecond β a h k (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
                (terminalCubicResidual β (cdf (D.μ : Measure ℝ)) s h z) (fun _ => z)) (f₁ k) k ∧
          HasDerivAt f₁ (f₂ k) k ∧ |f₂ k| ≤ C * Real.sqrt h * h ^ 3 := by
  obtain ⟨C, η, hC, hη, hη₁, H⟩ := scalarData_labelledTailSquareError_control D
  refine ⟨4 * C, η, by positivity, hη, hη₁, ?_⟩
  intro a s h z ha hh hhη ht
  have Hj (j : ℕ) := H a s h z ha hh hhη ht
    ((List.finRange 12).take j) ((List.finRange 12).drop j) (List.take_append_drop j _)
  choose p q hp using Hj
  have hd (j : ℕ) (k : ℝ) (hk : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
      HasDerivAt (frozenSquareTail β (cdf (D.μ : Measure ℝ)) a s h z j) (p j k) k ∧
        HasDerivAt (p j) (q j k) k ∧ |q j k| ≤ C * Real.sqrt h * h ^ 3 := by
    have he : frozenSquareTail β (cdf (D.μ : Measure ℝ)) a s h z j =
        labelledTailSquareError β (cdf (D.μ : Measure ℝ)) a s h z
          ((List.finRange 12).take j) ((List.finRange 12).drop j) := by
      funext k
      exact frozenSquareTail_eq_labelled β _ a s h z j k hh
    rw [he]
    exact hp j k hk
  refine ⟨fun k => a * p 12 k - a / 2 * p 2 k - a / 6 * p 1 k - a / 3 * p 0 k,
    fun k => a * q 12 k - a / 2 * q 2 k - a / 6 * q 1 k - a / 3 * q 0 k, ?_⟩
  intro k hk
  have h₁ := ((((hd 12 k hk).1.const_mul a).sub ((hd 2 k hk).1.const_mul (a / 2))).sub
    ((hd 1 k hk).1.const_mul (a / 6))).sub ((hd 0 k hk).1.const_mul (a / 3))
  have h₂ := ((((hd 12 k hk).2.1.const_mul a).sub ((hd 2 k hk).2.1.const_mul (a / 2))).sub
    ((hd 1 k hk).2.1.const_mul (a / 6))).sub ((hd 0 k hk).2.1.const_mul (a / 3))
  have he : (fun k => originalFrozenSecond β a h k
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
        (terminalResidual β (cdf (D.μ : Measure ℝ)) s h z) (fun _ => z) -
      originalFrozenSecond β a h k (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
        (terminalCubicResidual β (cdf (D.μ : Measure ℝ)) s h z) (fun _ => z)) =
      fun k => a * frozenSquareTail β (cdf (D.μ : Measure ℝ)) a s h z 12 k -
        a / 2 * frozenSquareTail β (cdf (D.μ : Measure ℝ)) a s h z 2 k -
        a / 6 * frozenSquareTail β (cdf (D.μ : Measure ℝ)) a s h z 1 k -
        a / 3 * frozenSquareTail β (cdf (D.μ : Measure ℝ)) a s h z 0 k := by
    funext k
    exact originalFrozenSecond_tail_eq β _ a s h z k
  refine ⟨by rw [he]; exact h₁, h₂, ?_⟩
  have hb (j : ℕ) {w : ℝ} (hw : |w| ≤ 1) : |w * q j k| ≤ C * Real.sqrt h * h ^ 3 := by
    rw [abs_mul]
    exact (mul_le_mul hw (hd j k hk).2.2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
  have ha' : |a| ≤ 1 := by rw [abs_of_pos ha.1]; exact ha.2
  have h2 : |a / 2| ≤ 1 := by rw [abs_div]; norm_num; linarith
  have h6 : |a / 6| ≤ 1 := by rw [abs_div]; norm_num; linarith
  have h3 : |a / 3| ≤ 1 := by rw [abs_div]; norm_num; linarith
  calc
    _ ≤ |a * q 12 k - a / 2 * q 2 k - a / 6 * q 1 k| + |a / 3 * q 0 k| := abs_sub _ _
    _ ≤ (|a * q 12 k - a / 2 * q 2 k| + |a / 6 * q 1 k|) + |a / 3 * q 0 k| := by gcongr; exact abs_sub _ _
    _ ≤ ((|a * q 12 k| + |a / 2 * q 2 k|) + |a / 6 * q 1 k|) + |a / 3 * q 0 k| := by gcongr; exact abs_sub _ _
    _ ≤ ((C * Real.sqrt h * h ^ 3 + C * Real.sqrt h * h ^ 3) + C * Real.sqrt h * h ^ 3) +
        C * Real.sqrt h * h ^ 3 := add_le_add (add_le_add (add_le_add (hb 12 ha') (hb 2 h2)) (hb 1 h6)) (hb 0 h3)
    _ = (4 * C) * Real.sqrt h * h ^ 3 := by ring

theorem scalarData_wickTailSecondControl {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    WickTailSecondControl β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  obtain ⟨C, η, hC, hη, _, HS⟩ := scalarData_frozenSecondTail_control D
  let B := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  obtain ⟨ξ, hξ, HQ⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  obtain ⟨hw, Hw⟩ := frozen_window_cover hl hu
  refine ⟨C, min η (min ξ (min (l / 2) ((D.q - u) / 6))), hC.le, by positivity, ?_⟩
  intro r hr h hh hh₀ z
  have hhη := hh₀.trans (min_le_left _ _)
  have hhξ := hh₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhw := hh₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc := Hw r hr h hh hhw
  have hs : 0 < r - h := by linarith [hc.1.1]
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hc.2.1], by linarith [hc.2.2, D.q_mem.2]⟩
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  have ha : a ∈ Ioc (0 : ℝ) 1 := ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  obtain ⟨p, q, Hp⟩ := HS a (r - h) h z ha hh.le hhη ht
  let E : ℝ → ℝ := fun k =>
    originalFrozenSecond β a h k (terminalTaylorQuadratic β α (r - h) h z)
        (terminalResidual β α (r - h) h z) (fun _ => z) -
      originalFrozenSecond β a h k (terminalTaylorQuadratic β α (r - h) h z)
        (terminalCubicResidual β α (r - h) h z) (fun _ => z)
  have hQ (k : ℝ) (hk : |k| ≤ 1 / 2) :
      RiccatiAdmissible (frozenSchedule β a (1 / 2) h k)
        (terminalTaylorQuadratic β α (r - h) h z) :=
    HQ α a (r - h) h k z ha hh.le hhξ hk
      ((scalarData_jet_le D (by norm_num) le_rfl ht z).trans (by dsimp only [B]; linarith))
  have he (k : ℝ) (hk : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
      wickTailCoefficientError β α a (r - h) h z k = (E k - E 0) / 2 := by
    rw [wickTailCoefficientError_eq_original β α a (r - h) h z k (scalarData_phi_regular D ht)
      (hQ k (abs_le.mpr ⟨hk.1.le, hk.2.le⟩)) (hQ 0 (by norm_num))]
    rfl
  have hsub : Icc (-(1 / 4) : ℝ) (1 / 4) ⊆ Ioo (-(1 / 2) : ℝ) (1 / 2) :=
    fun k hk => ⟨by linarith [hk.1], by linarith [hk.2]⟩
  refine ⟨fun k => p k / 2, fun k => q k / 2, ?_, ?_⟩
  · intro k hk
    have hk' := hsub hk
    have hnear : wickTailCoefficientError β α a (r - h) h z =ᶠ[𝓝 k]
        (fun k => (E k - E 0) / 2) := by
      filter_upwards [isOpen_Ioo.mem_nhds hk'] with k hk
      exact he k hk
    exact ⟨(((Hp k hk').1.sub_const (E 0)).div_const 2).congr_of_eventuallyEq hnear,
      (Hp k hk').2.1.div_const 2⟩
  · intro k hk
    have hb := (Hp k (hsub hk)).2.2
    rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
    have hnonneg : 0 ≤ C * Real.sqrt h * h ^ 3 := by positivity
    linarith

theorem scalarData_terminalSplitDerivativeControl {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      TerminalSplitDerivativeControl β (cdf (D.μ : Measure ℝ)) (Icc l u) C h₀ (1 / 4) :=
  scalarData_terminalSplitDerivativeControl_of_wickTail D hl hu
    (scalarData_wickTail_HT_of_secondControl D hl hu (scalarData_wickTailSecondControl D hl hu))

end SKBarriers2.Corner
