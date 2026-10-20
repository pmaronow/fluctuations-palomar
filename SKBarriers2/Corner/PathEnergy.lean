module

public import SKBarriers2.Corner.MassVariationAnalytic
public import SKBarriers2.Analysis.ChainJets

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def pathCoordinateSum (v : Vec3) : ℝ := ∑ a, v a

def pathDot (v w : Vec3) : ℝ := ∑ a, v a * w a

def firstOrderPathPolynomial {n : ℕ} (b u chi w : ℝ)
    (m : Fin n → ℝ) (v : Fin n → Vec3) (j : Fin n) : ℝ :=
  b*u^2*(pathCoordinateSum (v j))^2 +
    b^2*u*w*pathCoordinateSum (v j) *
      (∑ i, if i = j then 0 else ∑ a, (v i a)^2*v j a) +
    2*b^2*u^2*chi*pathCoordinateSum (v j) *
      (∑ i, if i = j then 0 else m i*pathCoordinateSum (v i)*pathDot (v i) (v j)) +
    b^2*chi^2*(∑ i, if i < j then (pathDot (v i) (v j))^2 else 0)

def entryEnergyPolynomial (b u chi w h : ℝ) (v mu : Vec3)
    (Q : Fin 3 → Fin 3 → ℝ) : ℝ :=
  u^2*(pathCoordinateSum v)^2 +
    2*b*u^2*chi*pathCoordinateSum v*pathDot v mu +
    4*b*h*u*w*(pathCoordinateSum v)^2 + b*chi^2*matrixQuadratic Q v

def pathEnergySelfInteraction (b u chi w m : ℝ) (v : Vec3) : ℝ :=
  b^2*(u*w*pathCoordinateSum v*(∑ a, (v a)^3) +
    2*m*u^2*chi*(pathCoordinateSum v)^2*(∑ a, (v a)^2))

private theorem sum_omit_index {n : ℕ} (f : Fin n → ℝ) (j : Fin n) :
    (∑ i, if i = j then 0 else f i) = (∑ i, f i)-f j := by
  have hs : (∑ i, f i) = (∑ i, if i = j then 0 else f i)+f j := by
    calc
      _ = ∑ i, ((if i = j then 0 else f i)+(if i = j then f i else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
      _ = _ := by rw [Finset.sum_add_distrib]; simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  linarith only [hs]

private theorem pathDot_translation {n : ℕ} (m : Fin n → ℝ)
    (v : Fin n → Vec3) (x : Vec3) :
    pathDot x (∑ i, m i • (pathCoordinateSum (v i) • v i)) =
      ∑ i, m i*pathCoordinateSum (v i)*pathDot (v i) x := by
  simp only [pathDot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem matrixQuadratic_strictPrefix {n : ℕ} (v : Fin n → Vec3)
    (j : Fin n) :
    matrixQuadratic (strictPrefix (fun i => rankOneMatrix (v i)) j) (v j) =
      ∑ i, if i < j then (pathDot (v i) (v j))^2 else 0 := by
  simp only [matrixQuadratic, strictPrefix, Finset.sum_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i < j
  · simp only [ite_eq_left hi, rankOneMatrix]
    simp only [pathDot, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    ring
  · simp only [ite_eq_right hi, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]

theorem firstOrderPathPolynomial_eq_energy {n : ℕ} (b u chi w h : ℝ)
    (m : Fin n → ℝ) (v : Fin n → Vec3) (j : Fin n)
    (hdiag : ∀ a, (∑ i, (v i a)^2) = 4*h) :
    firstOrderPathPolynomial b u chi w m v j =
      b*entryEnergyPolynomial b u chi w h (v j)
        (∑ i, m i • (pathCoordinateSum (v i) • v i))
        (strictPrefix (fun i => rankOneMatrix (v i)) j) -
      pathEnergySelfInteraction b u chi w (m j) (v j) := by
  have hd : (∑ i, ∑ a, (v i a)^2*v j a) = 4*h*pathCoordinateSum (v j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hdiag, pathCoordinateSum, ← Finset.mul_sum]
  simp only [firstOrderPathPolynomial, entryEnergyPolynomial,
    pathEnergySelfInteraction, sum_omit_index, pathDot_translation,
    matrixQuadratic_strictPrefix, hd]
  have hc : (∑ a, (v j a)^2*v j a) = ∑ a, (v j a)^3 := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hq : pathDot (v j) (v j) = ∑ a, (v j a)^2 := by
    simp only [pathDot, pow_two]
  rw [hc, hq]
  ring

theorem entryEnergyPolynomial_eq_windowMassEnergyEntry (β : ℝ) (α : ℝ → ℝ)
    (a p s h k : ℝ) (N : ℕ) (lam : ℝ)
    (j : Fin (windowMassPath β α a p s h k N).length) (z : ℝ) :
    entryEnergyPolynomial (β^2) (jet β α 1 (s+4*h) z)
      (jet β α 2 (s+4*h) z) (jet β α 3 (s+4*h) z) h
      (windowRawDirection β α a p s h k N j)
      (translation (OW.window (interpolatedProfile α a lam) p s h k N))
      (strictPrefix (fun i => rankOneMatrix (windowRawDirection β α a p s h k N i)) j) =
      windowMassEnergyEntry β α a p s h k N lam j z := by
  rfl

def orderedPathEnergyRemainder (β : ℝ) (α : ℝ → ℝ) (a p s h : ℝ)
    (N : ℕ) (lam : ℝ) (j : Fin (12*N)) (z k : ℝ) : ℝ :=
  let jj : Fin (windowMassPath β α a p s h k N).length :=
    ⟨j.val, by rw [windowMassPath_length]; exact j.isLt⟩
  (1/2:ℝ)*windowGradientEnergy β α a p s h k N lam jj z -
    (β^2/2)*windowMassEnergyEntry β α a p s h k N lam jj z

def OrderedPathRemainderStationarity (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ h0 : ℝ, 0 < h0 ∧ ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 →
    ∀ eps : ℝ, 0 < eps → ∀ᶠ N : ℕ in atTop,
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ z : ℝ, ∀ j : Fin (12*N),
        |deriv (orderedPathEnergyRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z) 0| ≤
          eps/(N:ℝ)

def UniformOrderedPathRemainderC2 (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ᶠ N : ℕ in atTop,
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ z : ℝ, ∀ j : Fin (12*N),
        let R := orderedPathEnergyRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z
        ∀ k : ℝ, |k| ≤ kap →
          HasDerivAt R (deriv R k) k ∧
          HasDerivAt (deriv R) (deriv (deriv R) k) k ∧
          |deriv (deriv R) k| ≤ C*(Real.sqrt h*h^2)/(N:ℝ)

private theorem increment_le_slope_add_quadratic {f : ℝ → ℝ} {kap M k : ℝ}
    (hkap : 0 < kap) (hM : 0 ≤ M) (hk : |k| ≤ kap)
    (hd : ∀ t : ℝ, |t| ≤ kap → HasDerivAt f (deriv f t) t)
    (hdd : ∀ t : ℝ, |t| ≤ kap →
      HasDerivAt (deriv f) (deriv (deriv f) t) t)
    (hb : ∀ t : ℝ, |t| ≤ kap → |deriv (deriv f) t| ≤ M) :
    |f k-f 0| ≤ |deriv f 0| * |k|+M*k^2 := by
  have hzero : (0:ℝ) ∈ Icc (-kap) kap := ⟨by linarith, hkap.le⟩
  have hfirst (t : ℝ) (ht : |t| ≤ kap) :
      |deriv f t-deriv f 0| ≤ M*|t| := by
    have H := (convex_Icc (-kap) kap).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hdd t (abs_le.mpr ht)).hasDerivWithinAt)
      (fun t ht => by simpa only [Real.norm_eq_abs] using hb t (abs_le.mpr ht))
      hzero (abs_le.mp ht)
    simpa only [Real.norm_eq_abs, sub_zero] using H
  have hsegment (t : ℝ) (ht : t ∈ uIcc (0:ℝ) k) : |t| ≤ |k| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht
  have H := (convex_uIcc (0:ℝ) k).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t ((hsegment t ht).trans hk)).hasDerivWithinAt)
    (C := |deriv f 0|+M*|k|) (by
      intro t ht
      rw [Real.norm_eq_abs]
      calc
        |deriv f t| ≤ |deriv f t-deriv f 0|+|deriv f 0| := by
          simpa only [sub_add_cancel] using abs_add_le (deriv f t-deriv f 0) (deriv f 0)
        _ ≤ M*|t|+|deriv f 0| :=
          add_le_add (hfirst t ((hsegment t ht).trans hk)) le_rfl
        _ ≤ |deriv f 0|+M*|k| := by
          linarith [mul_le_mul_of_nonneg_left (hsegment t ht) hM])
    left_mem_uIcc right_mem_uIcc
  have he : (|deriv f 0|+M*|k|) * |k| = |deriv f 0| * |k|+M*k^2 := by
    rw [add_mul, mul_assoc, ← pow_two, sq_abs]
  simpa only [Real.norm_eq_abs, sub_zero, he] using H

theorem pathEnergyExpansion_of_remainderC2_of_stationarity
    {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hC2 : UniformOrderedPathRemainderC2 β α I)
    (hstationary : OrderedPathRemainderStationarity β α I) :
    PathEnergyExpansion β α I := by
  obtain ⟨C,hC0,kap,hC,hhC,hkap,hC2⟩ := hC2
  obtain ⟨hS0,hhS,hstationary⟩ := hstationary
  refine ⟨C,min hC0 hS0,min kap 1,hC,lt_min hhC hhS,lt_min hkap (by norm_num),?_⟩
  intro r hr h hh hh0 k hk eps heps
  have hhC' : h ≤ hC0 := hh0.trans (min_le_left _ _)
  have hhS' : h ≤ hS0 := hh0.trans (min_le_right _ _)
  have hkC : |k| ≤ kap := hk.trans (min_le_left _ _)
  have hk1 : |k| ≤ 1 := hk.trans (min_le_right _ _)
  filter_upwards [hC2 r hr h hh hhC', hstationary r hr h hh hhS' eps heps,
    eventually_ge_atTop (1:ℕ)] with N hN2 hNS hN
  intro lam hlam z j hjk hj0
  let jj : Fin (12*N) := ⟨j, by simpa only [windowMassPath_length] using hjk⟩
  let R := orderedPathEnergyRemainder β α (α (r-h)) (1/2) (r-h) h N lam jj z
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have H := increment_le_slope_add_quadratic hkap
    (by positivity : 0 ≤ C*(Real.sqrt h*h^2)/(N:ℝ)) hkC
    (fun t ht => (hN2 lam hlam z jj t ht).1)
    (fun t ht => (hN2 lam hlam z jj t ht).2.1)
    (fun t ht => (hN2 lam hlam z jj t ht).2.2)
  have hs : |deriv R 0| * |k| ≤ eps/(N:ℝ) := by
    calc
      _ ≤ (eps/(N:ℝ))*1 := mul_le_mul (hNS lam hlam z jj) hk1 (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hbound : |R k-R 0| ≤
      C*(Real.sqrt h*h^2*k^2+h^2*|k|^3)/(N:ℝ)+eps/(N:ℝ) := by
    calc
      _ ≤ eps/(N:ℝ)+(C*(Real.sqrt h*h^2)/(N:ℝ))*k^2 :=
        H.trans (add_le_add hs le_rfl)
      _ ≤ _ := by
        have he : C*(Real.sqrt h*h^2*k^2+h^2*|k|^3)/(N:ℝ)+eps/(N:ℝ) =
            (eps/(N:ℝ)+(C*(Real.sqrt h*h^2)/(N:ℝ))*k^2)+C*h^2*|k|^3/(N:ℝ) := by ring
        rw [he]
        exact le_add_of_nonneg_right (by positivity)
  dsimp only [R, orderedPathEnergyRemainder, jj] at hbound
  convert hbound using 1
  congr 1
  ring

theorem massSensitivityExpansion_of_orderedRemainderInputs
    {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hentropy : UniformWindowEntropyInputs β α I)
    (hC2 : UniformOrderedPathRemainderC2 β α I)
    (hstationary : OrderedPathRemainderStationarity β α I) :
    MassSensitivityExpansion β α I := by
  exact massSensitivityExpansion_of_pathEnergyExpansion hentropy
    (pathEnergyExpansion_of_remainderC2_of_stationarity hC2 hstationary)

theorem abs_linearized_increment_le {f f1 f2 : ℝ → ℝ} {kap M k : ℝ}
    (hkap : 0 < kap) (hM : 0 ≤ M) (hk : |k| ≤ kap)
    (hd : ∀ t, |t| ≤ kap → HasDerivAt f (f1 t) t)
    (hdd : ∀ t, |t| ≤ kap → HasDerivAt f1 (f2 t) t)
    (hb : ∀ t, |t| ≤ kap → |f2 t| ≤ M) :
    |f k-f 0-f1 0*k| ≤ M*k^2 := by
  have hzero : (0:ℝ) ∈ Icc (-kap) kap := ⟨by linarith, hkap.le⟩
  have hfirst (t : ℝ) (ht : |t| ≤ kap) : |f1 t-f1 0| ≤ M*|t| := by
    have H := (convex_Icc (-kap) kap).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hdd t (abs_le.mpr ht)).hasDerivWithinAt)
      (fun t ht => by simpa only [Real.norm_eq_abs] using hb t (abs_le.mpr ht))
      hzero (abs_le.mp ht)
    simpa only [Real.norm_eq_abs, sub_zero] using H
  have hsegment (t : ℝ) (ht : t ∈ uIcc (0:ℝ) k) : |t| ≤ |k| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht
  have H := (convex_uIcc (0:ℝ) k).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => ((hd t ((hsegment t ht).trans hk)).sub
      ((hasDerivAt_id t).const_mul (f1 0))).hasDerivWithinAt)
    (C := M*|k|) (by
      intro t ht
      simpa only [Real.norm_eq_abs, mul_one] using
        (hfirst t ((hsegment t ht).trans hk)).trans
          (mul_le_mul_of_nonneg_left (hsegment t ht) hM))
    left_mem_uIcc right_mem_uIcc
  have he : (f k-f1 0*k)-(f 0-f1 0*0) = f k-f 0-f1 0*k := by ring
  simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs, sub_zero, he, mul_one,
    mul_assoc, ← pow_two, sq_abs] using H

theorem abs_symmetric_second_difference_le {f f1 f2 : ℝ → ℝ} {kap M k : ℝ}
    (hkap : 0 < kap) (hM : 0 ≤ M) (hk : |k| ≤ kap)
    (hd : ∀ t, |t| ≤ kap → HasDerivAt f (f1 t) t)
    (hdd : ∀ t, |t| ≤ kap → HasDerivAt f1 (f2 t) t)
    (hb : ∀ t, |t| ≤ kap → |f2 t| ≤ M) :
    |f k+f (-k)-2*f 0| ≤ 2*M*k^2 := by
  have hp := abs_linearized_increment_le hkap hM hk hd hdd hb
  have hn := abs_linearized_increment_le (k := -k) hkap hM
    (by simpa only [abs_neg] using hk) hd hdd hb
  have he : f k+f (-k)-2*f 0 =
      (f k-f 0-f1 0*k)+(f (-k)-f 0-f1 0*(-k)) := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hp hn).trans_eq (by ring))

theorem weighted_symmetric_remainder_sum_le {n : ℕ}
    {wk w0 rp rm r0 : Fin n → ℝ} {W D A B : ℝ}
    (hW : 0 ≤ W) (hD : 0 ≤ D)
    (hw : ∀ j, |w0 j| ≤ W) (hd : ∀ j, |wk j-w0 j| ≤ D)
    (hr : ∀ j, |rp j+rm j-2*r0 j| ≤ A)
    (hp : ∀ j, |rp j| ≤ B) (hm : ∀ j, |rm j| ≤ B) :
    |∑ j, (wk j*rp j+wk j*rm j-2*w0 j*r0 j)| ≤ (n:ℝ)*(W*A+2*D*B) := by
  calc
    _ ≤ ∑ j, |wk j*rp j+wk j*rm j-2*w0 j*r0 j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, (W*A+2*D*B) := by
      apply Finset.sum_le_sum
      intro j _
      have he : wk j*rp j+wk j*rm j-2*w0 j*r0 j =
          w0 j*(rp j+rm j-2*r0 j)+(wk j-w0 j)*(rp j+rm j) := by ring
      rw [he]
      calc
        _ ≤ |w0 j| * |rp j+rm j-2*r0 j|+|wk j-w0 j| * |rp j+rm j| := by
          simpa only [abs_mul] using abs_add_le
            (w0 j*(rp j+rm j-2*r0 j)) ((wk j-w0 j)*(rp j+rm j))
        _ ≤ W*A+D*(B+B) := add_le_add
          (mul_le_mul (hw j) (hr j) (abs_nonneg _) hW)
          (mul_le_mul (hd j) ((abs_add_le _ _).trans (add_le_add (hp j) (hm j)))
            (abs_nonneg _) hD)
        _ = _ := by ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

namespace FormalPathCoefficient

def rowSum (A : Mat3) (i : Fin 3) : ℝ := ∑ a, A i a

def twiceGenerator (A B : Mat3) (m n u chi w d1 d2 d3 d4 : ℝ) : ℝ :=
  (1/4:ℝ)*A 1 1*B 1 1*d4 +
    (n/2)*w*d1*(∑ a, A a a*B 1 a) +
    n*chi*d2*(∑ a, A a 1*B 1 a) +
    (n/2)*u*rowSum B 1*A 1 1*d3 +
    (m/2)*u*rowSum A 1*B 1 1*d3 +
    m*n*u*chi*d1*(∑ a, rowSum A a*B 1 a) +
    m*n*u^2*rowSum A 1*rowSum B 1*d2

def continuationSource (A B : Mat3) (m n u chi w d1 : ℝ) : ℝ :=
  m*d1*(∑ a, A a 1*((w/2)*B a a+n*u*chi*rowSum B a))

def covarianceJet (k : ℝ) : Fin 3 → Mat3 :=
  ![!![1, 1+2*k/3, 1-2*k/3;
        1+2*k/3, 1+4*k/3, 1;
        1-2*k/3, 1, 1-4*k/3],
    !![0, 0, 0; 0, 1/2-2*k/3, 1/2; 0, 1/2, 1/2+2*k/3],
    !![3, k/3, -k/3; k/3, 5/2-2*k/3, 0; -k/3, 0, 5/2+2*k/3]]

def frozenCovariance (k : ℝ) : Fin 3 → Mat3 :=
  let A0 := outer (commonVector (1/2) k)
  let A1 := (1/2:ℝ) • outer (sharedVector (1/2) k)
  ![A0, A1,
    (!![4, 1+k, 1-k; 1+k, 4, 3/2; 1-k, 3/2, 4] : Mat3)-A0-A1]

theorem frozenCovariance_eq_jet_add_quadratic (k : ℝ) (i a b : Fin 3) :
    frozenCovariance k i a b = covarianceJet k i a b +
      k^2*(frozenCovariance 1 i a b-covarianceJet 1 i a b) := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [frozenCovariance, covarianceJet, outer, commonVector,
      sharedVector, tentWeight, Pi.smul_apply, smul_eq_mul] <;> ring

def stageMass : Fin 3 → ℝ := ![1/3, 1/2, 1]

def secondCoefficientFor (S : Fin 3 → Mat3) (u chi w d1 d2 d3 d4 : ℝ) : ℝ :=
  (∑ i : Fin 3,
    (twiceGenerator (S i) (S i)
        (stageMass i) (stageMass i) u chi w d1 d2 d3 d4 +
      continuationSource (S i) (S i)
        (stageMass i) (stageMass i) u chi w d1)/2) +
    ∑ i : Fin 3, ∑ j : Fin 3, if i < j then
      twiceGenerator (S i) (S j)
        (stageMass i) (stageMass j) u chi w d1 d2 d3 d4 +
      continuationSource (S i) (S j)
        (stageMass i) (stageMass j) u chi w d1 else 0

def secondCoefficient (k u chi w d1 d2 d3 d4 : ℝ) : ℝ :=
  secondCoefficientFor (covarianceJet k) u chi w d1 d2 d3 d4

def frozenSecondCoefficient (k u chi w d1 d2 d3 d4 : ℝ) : ℝ :=
  secondCoefficientFor (frozenCovariance k) u chi w d1 d2 d3 d4

theorem secondCoefficient_odd_part (k u chi w d1 d2 d3 d4 : ℝ) :
    (secondCoefficient k u chi w d1 d2 d3 d4 -
      secondCoefficient (-k) u chi w d1 d2 d3 d4)/2 = -(chi*d2/6)*k := by
  norm_num [secondCoefficient, secondCoefficientFor, twiceGenerator, continuationSource,
    covarianceJet, stageMass, rowSum, Fin.sum_univ_succ]
  ring

theorem frozenSecondCoefficient_odd_part (k u chi w d1 d2 d3 d4 : ℝ) :
    (frozenSecondCoefficient k u chi w d1 d2 d3 d4 -
      frozenSecondCoefficient (-k) u chi w d1 d2 d3 d4)/2 =
      -(chi*d2/162)*k*(52*k^2+27) := by
  norm_num [frozenSecondCoefficient, secondCoefficientFor, twiceGenerator,
    continuationSource, frozenCovariance, outer, commonVector, sharedVector,
    tentWeight, stageMass, rowSum, Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul]
  ring

theorem logCosh_squareGradient_odd_part (k : ℝ) :
    (secondCoefficient k (1/2) (3/4) (-3/4) (3/4) (3/8) (-15/4) (39/8) -
      secondCoefficient (-k) (1/2) (3/4) (-3/4) (3/4) (3/8) (-15/4) (39/8))/2 =
      -(3/64:ℝ)*k := by
  rw [secondCoefficient_odd_part]
  ring

theorem frozen_logCosh_squareGradient_odd_part (k : ℝ) :
    (frozenSecondCoefficient k (1/2) (3/4) (-3/4) (3/4) (3/8) (-15/4) (39/8) -
      frozenSecondCoefficient (-k) (1/2) (3/4) (-3/4) (3/4) (3/8) (-15/4) (39/8))/2 =
      -(3/64:ℝ)*k-(13/144:ℝ)*k^3 := by
  rw [frozenSecondCoefficient_odd_part]
  ring

theorem frozen_logCosh_odd_part_not_quadratically_bounded :
    ¬ ∃ C kap : ℝ, 0 ≤ C ∧ 0 < kap ∧ ∀ k : ℝ, |k| ≤ kap →
      |(frozenSecondCoefficient k (1/2) (3/4) (-3/4) (3/4) (3/8) (-15/4) (39/8) -
        frozenSecondCoefficient (-k) (1/2) (3/4) (-3/4) (3/4) (3/8) (-15/4) (39/8))/2| ≤
        C*k^2 := by
  rintro ⟨C,kap,hC,hkap,hbound⟩
  let k := min (kap/2) ((3/128:ℝ)/(C+1))
  have hk : 0 < k := lt_min (by positivity) (by positivity)
  have hkap' : |k| ≤ kap := by
    rw [abs_of_pos hk]
    exact (min_le_left _ _).trans (by linarith)
  have hsmall : k*(C+1) ≤ (3/128:ℝ) :=
    (le_div_iff₀ (by positivity : 0 < C+1)).mp (min_le_right _ _)
  have H := hbound k hkap'
  rw [frozen_logCosh_squareGradient_odd_part,
    abs_of_nonpos (by nlinarith only [hk.le, pow_nonneg hk.le 3] :
      -(3/64:ℝ)*k-(13/144:ℝ)*k^3 ≤ 0)] at H
  have hc : C*k < (3/64:ℝ) := by linarith
  have hprod := mul_lt_mul_of_pos_right hc hk
  have hp : 0 ≤ (13/144:ℝ)*k^3 := by positivity
  nlinarith only [H, hprod, hp]

theorem logCosh_squareGradient_not_even :
    ¬ Function.Even (fun k =>
      secondCoefficient k (1/2) (3/4) (-3/4) (3/4) (3/8) (-15/4) (39/8)) := by
  intro he
  have hz := logCosh_squareGradient_odd_part (1/4)
  have hh : secondCoefficient (-(1/4)) (1/2) (3/4) (-3/4) (3/4) (3/8) (-15/4) (39/8) =
      secondCoefficient (1/4) (1/2) (3/4) (-3/4) (3/4) (3/8) (-15/4) (39/8) := he (1/4)
  rw [hh] at hz
  norm_num at hz

end FormalPathCoefficient
end SKBarriers2.Corner
