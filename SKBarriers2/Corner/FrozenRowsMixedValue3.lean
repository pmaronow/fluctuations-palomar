module

public import SKBarriers2.Corner.FrozenRowsMixedValue2
public import SKBarriers2.Corner.FrozenRowsMixed9
public import SKBarriers2.Corner.FrozenRowsMixed12
public import SKBarriers2.Corner.FrozenRowsMovingTestSource

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic

namespace SKBarriers2.StepCalculus
local notation "X" => (Fin 3 → ℝ)

theorem centeredFirstNoiseTransport_scale_inv {K : ℝ} (hK : K ≠ 0)
    (m : ℝ) (v : X) (f : X → ℝ) (A : X →L[ℝ] X) (b : X)
    (a c s : ℝ → X → ℝ) :
    centeredFirstNoiseTransport m (K⁻¹ • v) (spatialRescale K 0 f)
        (K⁻¹ • A) (K⁻¹ • b) a c s =
      centeredFirstNoiseTransport m v f A b a c s := by
  have hlaw (x : X) : stepLaw m (K⁻¹ • v) (spatialRescale K 0 f)
      ((K⁻¹ • A) x + K⁻¹ • b) = stepLaw m v f (A x + b) := by
    unfold stepLaw gaussianStepLaw
    congr 1
    funext t
    apply congrArg (fun y : X => m * f y)
    change K • ((K⁻¹ • A) x + K⁻¹ • b + t • (K⁻¹ • v)) + 0 = A x + b + t • v
    have he : (K⁻¹ • A) x + K⁻¹ • b + t • (K⁻¹ • v) = K⁻¹ • (A x + b + t • v) := by
      simp only [smul_apply, smul_add, smul_comm t K⁻¹]
    rw [he, smul_smul, mul_inv_cancel₀ hK, one_smul, add_zero]
  funext x
  simp only [centeredFirstNoiseTransport, noiseMean, hlaw]

theorem wJets_centeredFirstNoiseTransport_boundedNoise
    {r p q : ℕ} {B C H L m K : ℝ} {f : X → ℝ} {a c s : ℝ → X → ℝ}
    (hf : QPotential (r + 1) B f) (hC : 0 ≤ C) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (ha : ContDiff ℝ r (Function.uncurry a))
    (hc : ContDiff ℝ r (Function.uncurry c))
    (hs : ContDiff ℝ r (Function.uncurry s))
    (haj : ∀ t, WJets r (H * (1 + |t|) ^ q) (p + 1) (a t))
    (hcj : ∀ t, WJets r (C * (1 + |t|) ^ q) p (c t))
    (hsj : ∀ t, WJets r (L * (1 + |t|) ^ q) 1 (s t))
    (hm : m ∈ Icc (0 : ℝ) 1) (hK : 1 ≤ K) (v : X) (hv : ‖v‖ ≤ K)
    (A : X →L[ℝ] X) (b : X) :
    let K₁ := affineNoiseAverageCoefficient r q (B * K ^ (r + 1)) (K⁻¹ • A)
    let K₂ := affineNoiseAverageCoefficient r (q + q) (B * K ^ (r + 1)) (K⁻¹ • A)
    WJets r (K₁ * H + (2 : ℝ) ^ r * (K₂ + K₁ ^ 2) * C * L) (p + 1)
      (centeredFirstNoiseTransport m v f A b a c s) := by
  have hK₀ : 0 < K := by linarith
  have hv' : ‖K⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hK₀)]
    exact (mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hK₀.le)).trans_eq
      (inv_mul_cancel₀ hK₀.ne')
  have H := wJets_centeredFirstNoiseTransport (hf.dilate hK) hC hH hL ha hc hs
    haj hcj hsj hm (K⁻¹ • v) hv' (K⁻¹ • A) (K⁻¹ • b)
  rwa [centeredFirstNoiseTransport_scale_inv hK₀.ne'] at H

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "X" => (Fin 3 → ℝ)

theorem affineCoordinateEndpoint_scaled_deriv (c : AffineGaussianCoordinate P X)
    {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) (ρ : ℝ) (x : X) (t : ℝ) :
    ρ • deriv (fun z => affineCoordinateEndpoint c (p z,(x,t))) k =
      (ρ • c.mean (deriv p k)) x + ρ • c.shift (deriv p k) +
        t • (ρ • c.noise (deriv p k)) := by
  have hpd := (hp.differentiableAt (by norm_num)).hasDerivAt
  have hA := (c.mean.hasFDerivAt.comp_hasDerivAt k hpd).clm_apply (hasDerivAt_const k x)
  have hb := c.shift.hasFDerivAt.comp_hasDerivAt k hpd
  have hv := (c.noise.hasFDerivAt.comp_hasDerivAt k hpd).const_smul t
  have H := ((hA.add hb).add hv).deriv
  change deriv (fun z => c.mean (p z) x+c.shift (p z)+t • c.noise (p z)) k =
    c.mean (deriv p k) x+c.mean (p k) 0+c.shift (deriv p k)+t • c.noise (deriv p k) at H
  change ρ • deriv (fun z => c.mean (p z) x + c.shift (p z) + t • c.noise (p z)) k = _
  rw [H]
  simp only [map_zero, add_zero, smul_add, smul_apply, smul_comm ρ t]

def movingAffineFirstCoefficient (r p : ℕ) (B K L : ℝ)
    (A U : X →L[ℝ] X) (b d v w : X) : ℝ :=
  let N₁ := StepCalculus.affineNoiseAverageCoefficient r (p + 1)
    (B * K ^ (r + 1)) (K⁻¹ • A)
  let N₂ := StepCalculus.affineNoiseAverageCoefficient r ((p + 1) + (p + 1))
    (B * K ^ (r + 1)) (K⁻¹ • A)
  let V := StepCalculus.noiseAverageCoefficient r (p + 1) (B * K ^ (r + 1)) *
    K ^ (p + 1 + r) * (1 + ‖A‖ + ‖b‖) ^ (p + 1) * max 1 ‖A‖ ^ r
  let Q := (1 + StepCalculus.noiseAverageCoefficient r (p + 1) (B * K ^ (r + 1))) *
    K ^ (p + (r + 1)) * (1 + ‖A‖ + ‖b‖) ^ p * max 1 ‖A‖ ^ r
  let H := N₁ * movingTestFirstCoefficient r p A U b d v w +
    (2 : ℝ) ^ r * (N₂ + N₁ ^ 2) * movingTestCenteredCoefficient r p A b v * L
  1 + |V| + |Q| + |H|

theorem movingAffineFirstCoefficient_ge_one (r p : ℕ) (B K L : ℝ)
    (A U : X →L[ℝ] X) (b d v w : X) :
    1 ≤ movingAffineFirstCoefficient r p B K L A U b d v w := by
  dsimp only [movingAffineFirstCoefficient]
  have H (a b c : ℝ) : 1 ≤ 1+|a|+|b|+|c| := by
    linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c]
  exact H _ _ _

theorem movingAffineFirstCoefficient_uniform (r p : ℕ) (B K L : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧
      ∀ A U : X →L[ℝ] X, ∀ b d v w : X,
        ‖A‖ ≤ K → ‖U‖ ≤ K → ‖b‖ ≤ K → ‖d‖ ≤ K → ‖v‖ ≤ K → ‖w‖ ≤ K →
          movingAffineFirstCoefficient r p B K L A U b d v w ≤ T := by
  let E := (X →L[ℝ] X) × ((X →L[ℝ] X) × (X × (X × (X × X))))
  let f : E → ℝ := fun z => movingAffineFirstCoefficient r p B K L
    z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2
  have hf : Continuous f := by
    dsimp only [f, movingAffineFirstCoefficient, StepCalculus.affineNoiseAverageCoefficient,
      movingTestFirstCoefficient, movingTestCenteredCoefficient]
    fun_prop
  have hcompact : IsCompact (Metric.closedBall (0 : E) (max K 0)) := isCompact_closedBall _ _
  obtain ⟨S,hS⟩ := hcompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨1+|S|, by linarith [abs_nonneg S], ?_⟩
  intro A U b d v w hA hU hb hd hv hw
  have hx : (A,(U,(b,(d,(v,w))))) ∈ Metric.closedBall (0 : E) (max K 0) := by
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    exact (max_le hA (max_le hU (max_le hb (max_le hd (max_le hv hw))))).trans
      (le_max_left _ _)
  have H := hS (A,(U,(b,(d,(v,w))))) hx
  change |movingAffineFirstCoefficient r p B K L A U b d v w| ≤ S at H
  exact (le_abs_self _).trans (H.trans (by linarith [le_abs_self S]))

def movingAffineFirstAverage (m : ℝ) (v : X) (f : X → ℝ)
    (A U : X →L[ℝ] X) (b d w : X) (s : ℝ → X → ℝ)
    (J : X → MomentKJet) (x : X) : MomentKJet :=
  ⟨StepCalculus.tiltedAverage m v f (fun y => (J y).value) (A x+b),
    StepCalculus.centeredFirstNoiseTransport m v f A b
      (fun t x => (J (A x+b+t • v)).first+
        fderiv ℝ (fun y => (J y).value) (A x+b+t • v) (U x+d+t • w))
      (fun t x => (J (A x+b+t • v)).value-(J (A x+b)).value) s x, 0⟩

theorem firstDegreeBound_movingAffineFirstAverage
    {r p : ℕ} {B C L K m : ℝ} {f : X → ℝ} {s : ℝ → X → ℝ}
    (hQ : QPotential (r + 1) B f)
    {J : X → MomentKJet} (hJ : MomentKJet.FirstDegreeBound (r + 1) C p J)
    (hL : 0 ≤ L) (hK : 1 ≤ K) (hm : m ∈ Icc (0 : ℝ) 1)
    (v : X) (hv : ‖v‖ ≤ K) (A U : X →L[ℝ] X) (b d w : X)
    (hs : ContDiff ℝ r (Function.uncurry s))
    (hsj : ∀ t, WJets r (L * (1 + |t|) ^ (p + 1)) 1 (s t)) :
    MomentKJet.FirstDegreeBound r
      (movingAffineFirstCoefficient r p B K L A U b d v w * C) p
      (movingAffineFirstAverage m v f A U b d w s J) := by
  have hC := hJ.value.value.nonneg
  have hfirst := hJ.value.moving_firstSource hJ.first A U b d v w
  have hcenter := hJ.value.positive.affine_noise_centered_contDiff A b v
  have hcenterj := hJ.value.positive.affine_noise_centered_jets A b v
  have HD := StepCalculus.wJets_centeredFirstNoiseTransport_boundedNoise
    (a := fun t x => (J (A x+b+t • v)).first+
      fderiv ℝ (fun y => (J y).value) (A x+b+t • v) (U x+d+t • w))
    (c := fun t x => (J (A x+b+t • v)).value-(J (A x+b)).value) (s := s)
    hQ (mul_nonneg hC (movingTestCenteredCoefficient_nonneg r p A b v))
    (mul_nonneg hC (movingTestFirstCoefficient_nonneg r p A U b d v w)) hL
    (by convert! hfirst.1 using 1) (by convert! hcenter using 1) hs hfirst.2 hcenterj hsj hm hK v hv A b
  have HV := StepCalculus.wJets_affineAverage_boundedNoise hQ
    (hJ.value.value.of_le (Nat.le_succ r)) hm hK v hv A b
  have HQ := StepCalculus.wQ_affineAverage_boundedNoise hQ hJ.value.positive hm hK v hv A b
  let N₁ := StepCalculus.affineNoiseAverageCoefficient r (p + 1)
    (B * K ^ (r + 1)) (K⁻¹ • A)
  let N₂ := StepCalculus.affineNoiseAverageCoefficient r ((p + 1) + (p + 1))
    (B * K ^ (r + 1)) (K⁻¹ • A)
  let V := StepCalculus.noiseAverageCoefficient r (p + 1) (B * K ^ (r + 1)) *
    K ^ (p + 1 + r) * (1 + ‖A‖ + ‖b‖) ^ (p + 1) * max 1 ‖A‖ ^ r
  let Q := (1 + StepCalculus.noiseAverageCoefficient r (p + 1) (B * K ^ (r + 1))) *
    K ^ (p + (r + 1)) * (1 + ‖A‖ + ‖b‖) ^ p * max 1 ‖A‖ ^ r
  let H := N₁ * movingTestFirstCoefficient r p A U b d v w +
    (2 : ℝ) ^ r * (N₂ + N₁ ^ 2) * movingTestCenteredCoefficient r p A b v * L
  have hV : C * V ≤ (1 + |V| + |Q| + |H|) * C := by
    rw [mul_comm _ C]
    exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self V, abs_nonneg Q, abs_nonneg H]) hC
  have hQ' : C * Q ≤ (1 + |V| + |Q| + |H|) * C := by
    rw [mul_comm _ C]
    exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self Q, abs_nonneg V, abs_nonneg H]) hC
  have hH : C * H ≤ (1 + |V| + |Q| + |H|) * C := by
    rw [mul_comm _ C]
    exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self H, abs_nonneg V, abs_nonneg Q]) hC
  refine ⟨⟨HV.mono ?_ le_rfl, HQ.mono ?_ le_rfl⟩, HD.mono ?_ le_rfl⟩
  · convert hV using 1
    all_goals dsimp only [movingAffineFirstCoefficient, V, Q, H, N₁, N₂]
    all_goals ring
  · convert hQ' using 1
    all_goals dsimp only [movingAffineFirstCoefficient, V, Q, H, N₁, N₂]
    all_goals ring
  · convert hH using 1
    all_goals dsimp only [movingAffineFirstCoefficient, V, Q, H, N₁, N₂]
    all_goals ring

theorem movingAffineFirstAverage_actual_slots
    (c : AffineGaussianCoordinate P X) {F G : P × X → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) (ρ : ℝ)
    {J : X → MomentKJet}
    (hvalue : ∀ y, (J y).value = G (p k,y))
    (hfirst : ∀ y, (J y).first = ρ * deriv (fun z => G (p z,y)) k) (x : X) :
    let H := movingAffineFirstAverage (Real.exp (c.logMass (p k))) (c.noise (p k))
      (fun y => F (p k,y)) (c.mean (p k)) (ρ • c.mean (deriv p k))
      (c.shift (p k)) (ρ • c.shift (deriv p k)) (ρ • c.noise (deriv p k))
      (fun t x => ρ * deriv (fun z => affineCoordinateDensityPotential c F (p z,(x,t))) k) J x
    H.value = affineCoordinateAverage c F G (p k,x) ∧
      H.first = ρ * deriv (fun z => affineCoordinateAverage c F G (p z,x)) k := by
  dsimp only
  have hfun : (fun y => (J y).value) = fun y => G (p k,y) := funext hvalue
  constructor
  · simp only [movingAffineFirstAverage, hfun]
    rfl
  · rw [affineCoordinateAverage_scaled_first_eq_transport c hF hG hp
      (fun x => G (p k,c.mean (p k) x+c.shift (p k))) ρ x]
    simp only [movingAffineFirstAverage, hvalue, hfirst]
    congr 1
    funext t y
    rw [affineCoordinateObservable_scaled_first c hG hp,
      affineCoordinateEndpoint_scaled_deriv c hp]
    rfl

theorem firstDegreeBound_affineCoordinateAverage
    {r pdegree : ℕ} {B C L K ρ : ℝ}
    (c : AffineGaussianCoordinate P X) {F G : P × X → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k)
    (hQ : QPotential (r + 1) B (fun y => F (p k,y)))
    (hJ : MomentKJet.FirstDegreeBound (r + 1) C pdegree
      (fun y => ⟨G (p k,y), ρ * deriv (fun z => G (p z,y)) k, 0⟩))
    (hL : 0 ≤ L) (hK : 1 ≤ K)
    (hm : Real.exp (c.logMass (p k)) ∈ Icc (0 : ℝ) 1)
    (hv : ‖c.noise (p k)‖ ≤ K)
    (hs : ContDiff ℝ r (fun z : ℝ × X =>
      ρ * deriv (fun u => affineCoordinateDensityPotential c F (p u,(z.2,z.1))) k))
    (hsj : ∀ t, WJets r (L * (1 + |t|) ^ (pdegree + 1)) 1
      (fun x => ρ * deriv (fun u => affineCoordinateDensityPotential c F (p u,(x,t))) k)) :
    MomentKJet.FirstDegreeBound r
      (movingAffineFirstCoefficient r pdegree B K L (c.mean (p k)) (ρ • c.mean (deriv p k))
        (c.shift (p k)) (ρ • c.shift (deriv p k)) (c.noise (p k)) (ρ • c.noise (deriv p k)) * C)
      pdegree (fun x => ⟨affineCoordinateAverage c F G (p k,x),
        ρ * deriv (fun u => affineCoordinateAverage c F G (p u,x)) k, 0⟩) := by
  let A := c.mean (p k)
  let b := c.shift (p k)
  let v := c.noise (p k)
  let U := ρ • c.mean (deriv p k)
  let d := ρ • c.shift (deriv p k)
  let w := ρ • c.noise (deriv p k)
  let J : X → MomentKJet := fun y => ⟨G (p k,y), ρ * deriv (fun z => G (p z,y)) k, 0⟩
  let s := fun t x => ρ * deriv (fun u => affineCoordinateDensityPotential c F (p u,(x,t))) k
  have H := firstDegreeBound_movingAffineFirstAverage (s := s) hQ hJ hL hK hm v hv A U b d w hs hsj
  refine H.congr ?_ ?_
  · intro x
    exact (movingAffineFirstAverage_actual_slots c hF hG hp ρ (J := J)
      (fun _ => rfl) (fun _ => rfl) x).1.symm
  · intro x
    exact (movingAffineFirstAverage_actual_slots c hF hG hp ρ (J := J)
      (fun _ => rfl) (fun _ => rfl) x).2.symm

end SKBarriers2.Corner
