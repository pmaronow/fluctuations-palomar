module

public import UpperPowerLedger
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

set_option autoImplicit false

namespace OAI.SKFluctuations.PositiveLaplaceAssembly

open Filter Set
open scoped Topology

noncomputable def wallStep (T ε : ℝ) : ℝ :=
  ε + min ε (T-ε) / 4

noncomputable def wallOrbit (T ε : ℝ) : ℕ → ℝ
  | 0 => ε
  | k+1 => wallStep T (wallOrbit T ε k)

theorem wallStep_ge {T ε : ℝ} (hε : ε ∈ Icc 0 T) : ε ≤ wallStep T ε := by
  unfold wallStep
  have hmin : 0 ≤ min ε (T-ε) := le_min hε.1 (sub_nonneg.mpr hε.2)
  linarith

theorem wallStep_mem {T ε : ℝ} (hε : ε ∈ Ioo 0 T) : wallStep T ε ∈ Ioo 0 T := by
  have hge := wallStep_ge ⟨hε.1.le, hε.2.le⟩
  have hmin := min_le_right ε (T-ε)
  constructor
  · exact hε.1.trans_le hge
  · unfold wallStep
    have hlt := hε.2
    linarith

theorem wallOrbit_mem {T ε : ℝ} (hε : ε ∈ Ioo 0 T) (k : ℕ) :
    wallOrbit T ε k ∈ Ioo 0 T := by
  induction k with
  | zero => exact hε
  | succ k ih => exact wallStep_mem ih

theorem wallOrbit_monotone {T ε : ℝ} (hε : ε ∈ Ioo 0 T) :
    Monotone (wallOrbit T ε) := by
  apply monotone_nat_of_le_succ
  intro k
  exact wallStep_ge ⟨(wallOrbit_mem hε k).1.le, (wallOrbit_mem hε k).2.le⟩

theorem wallOrbit_add (T ε : ℝ) (a b : ℕ) :
    wallOrbit T ε (a+b) = wallOrbit T (wallOrbit T ε a) b := by
  induction b with
  | zero => simp [wallOrbit]
  | succ b ih =>
    change wallStep T (wallOrbit T ε (a+b)) =
      wallStep T (wallOrbit T (wallOrbit T ε a) b)
    rw [ih]

theorem wallOrbit_before_half {T ε : ℝ} (hε : ε ∈ Ioo 0 T) (k : ℕ)
    (hk : wallOrbit T ε k ≤ T/2) :
    wallOrbit T ε k = (5/4 : ℝ)^k * ε := by
  induction k with
  | zero => simp [wallOrbit]
  | succ k ih =>
    have hprev : wallOrbit T ε k ≤ T/2 :=
      (wallOrbit_monotone hε (Nat.le_succ k)).trans hk
    have hformula := ih hprev
    have hmin : min (wallOrbit T ε k) (T-wallOrbit T ε k) = wallOrbit T ε k :=
      min_eq_left (by linarith)
    rw [wallOrbit, wallStep, hmin, hformula, pow_succ]
    ring

theorem wallOrbit_after_half {T ε : ℝ} (hε : ε ∈ Ioo 0 T)
    (hhalf : T/2 ≤ ε) (k : ℕ) :
    T-wallOrbit T ε k = (3/4 : ℝ)^k * (T-ε) := by
  induction k with
  | zero => simp [wallOrbit]
  | succ k ih =>
    have hprev : T/2 ≤ wallOrbit T ε k :=
      hhalf.trans (wallOrbit_monotone hε (Nat.zero_le k))
    have hmin : min (wallOrbit T ε k) (T-wallOrbit T ε k) = T-wallOrbit T ε k :=
      min_eq_right (by linarith)
    rw [wallOrbit, wallStep, hmin, pow_succ]
    nlinarith [ih]

noncomputable def logarithmicCount (q X : ℝ) : ℕ :=
  Nat.ceil (Real.log X / Real.log q)

theorem pow_logarithmicCount_ge {q X : ℝ} (hq : 1 < q) (hX : 0 < X) :
    X ≤ q ^ logarithmicCount q X := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hlogpos : 0 < Real.log q := Real.log_pos hq
  have hceil := Nat.le_ceil (Real.log X / Real.log q)
  have hmul := (div_le_iff₀ hlogpos).mp hceil
  apply (Real.log_le_log_iff hX (pow_pos hqpos _)).mp
  rw [Real.log_pow]
  exact hmul

noncomputable def wallIterationCount (T ε r : ℝ) : ℕ :=
  logarithmicCount (5/4) (T/ε) + logarithmicCount (4/3) (T/r)

theorem wallOrbit_reaches_half {T ε : ℝ} (hε : ε ∈ Ioo 0 T) :
    T/2 ≤ wallOrbit T ε (logarithmicCount (5/4) (T/ε)) := by
  have hT : 0 < T := hε.1.trans hε.2
  have hp := pow_logarithmicCount_ge (by norm_num : (1 : ℝ) < 5/4)
    (div_pos hT hε.1)
  have hprod := (div_le_iff₀ hε.1).mp hp
  by_contra hnot
  have hsmall : wallOrbit T ε (logarithmicCount (5/4) (T/ε)) ≤ T/2 :=
    (lt_of_not_ge hnot).le
  have hformula := wallOrbit_before_half hε _ hsmall
  nlinarith

theorem wallOrbit_residual_le {T ε r : ℝ} (hε : ε ∈ Ioo 0 T) (hr : 0 < r) :
    T-wallOrbit T ε (wallIterationCount T ε r) ≤ r := by
  let a := logarithmicCount (5/4) (T/ε)
  let b := logarithmicCount (4/3) (T/r)
  have hT : 0 < T := hε.1.trans hε.2
  have hhalf : T/2 ≤ wallOrbit T ε a := wallOrbit_reaches_half hε
  have hformula := wallOrbit_after_half (wallOrbit_mem hε a) hhalf b
  have hp := pow_logarithmicCount_ge (by norm_num : (1 : ℝ) < 4/3)
    (div_pos hT hr)
  have hprod : T ≤ (4/3 : ℝ)^b * r := (div_le_iff₀ hr).mp hp
  have hpositive : 0 ≤ (3/4 : ℝ)^b := pow_nonneg (by norm_num) _
  have hinverse : (3/4 : ℝ)^b * (4/3 : ℝ)^b = 1 := by
    rw [← mul_pow]
    norm_num
  have hshrink := mul_le_mul_of_nonneg_left hprod hpositive
  have htail : (3/4 : ℝ)^b * T ≤ r := by
    simpa only [← mul_assoc, hinverse, one_mul] using hshrink
  unfold wallIterationCount
  rw [wallOrbit_add, hformula]
  have hstart := (wallOrbit_mem hε a).1.le
  calc
    _ ≤ (3/4 : ℝ)^b * T := mul_le_mul_of_nonneg_left (by linarith) hpositive
    _ ≤ r := htail

theorem wallOrbit_telescope (p : ℝ → ℝ) {T ε E : ℝ}
    (hε : ε ∈ Ioo 0 T)
    (hstep : ∀ x : ℝ, ε ≤ x → x < T → p (wallStep T x)-p x ≤ E) (k : ℕ) :
    p (wallOrbit T ε k)-p ε ≤ (k : ℝ)*E := by
  induction k with
  | zero => simp [wallOrbit]
  | succ k ih =>
    have hnext := hstep (wallOrbit T ε k)
      (wallOrbit_monotone hε (Nat.zero_le k)) (wallOrbit_mem hε k).2
    rw [wallOrbit]
    push_cast
    linarith

theorem wall_upper_telescope (p : ℝ → ℝ) {T ε r E s : ℝ}
    (hε : ε ∈ Ioo 0 T) (hr : 0 < r) (hs : 0 ≤ s)
    (hstep : ∀ x : ℝ, ε ≤ x → x < T → p (wallStep T x)-p x ≤ E)
    (hslope : ∀ x : ℝ, ε ≤ x → x ≤ T → p T-p x ≤ s/4*(T-x)) :
    p T-p 0 ≤ p ε-p 0 + (wallIterationCount T ε r : ℝ)*E + s*r/4 := by
  let k := wallIterationCount T ε r
  have htelescope := wallOrbit_telescope p hε hstep k
  have hremaining := hslope (wallOrbit T ε k)
    (wallOrbit_monotone hε (Nat.zero_le k)) (wallOrbit_mem hε k).2.le
  have hresidual := wallOrbit_residual_le hε hr
  have htail := mul_le_mul_of_nonneg_left hresidual (show 0 ≤ s/4 by positivity)
  dsimp only [k] at *
  linarith

noncomputable def upperInitialEpsilon (m : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)^(-(1 : ℝ)/3+40*m)

noncomputable def upperFinalResidual (n : ℕ) : ℝ := (n : ℝ)^(-(5 : ℝ))

noncomputable def wallLogConstant (T : ℝ) : ℝ :=
  (Real.log T+1)/Real.log (5/4) + (Real.log T+5)/Real.log (4/3) + 2

theorem wallLogConstant_pos {T : ℝ} (hT : 1 < T) : 0 < wallLogConstant T := by
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hlogA : 0 < Real.log (5/4 : ℝ) := Real.log_pos (by norm_num)
  have hlogB : 0 < Real.log (4/3 : ℝ) := Real.log_pos (by norm_num)
  unfold wallLogConstant
  positivity

theorem upperInitialEpsilon_mem {T m : ℝ} (hT : 1 < T)
    (hm : m < 1/300) {n : ℕ} (hn : 1 ≤ n) :
    upperInitialEpsilon m n ∈ Ioo 0 T := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hp := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hnR)
    (-(1 : ℝ)/3+40*m)
  have hle := Real.rpow_le_one_of_one_le_of_nonpos hnR
    (show -(1 : ℝ)/3+40*m ≤ 0 by linarith)
  exact ⟨hp, hle.trans_lt hT⟩

theorem logarithmicCount_le {q X : ℝ} (hq : 1 < q) (hX : 1 ≤ X) :
    (logarithmicCount q X : ℝ) ≤ Real.log X / Real.log q + 1 := by
  unfold logarithmicCount
  exact (Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hX)
    (Real.log_pos hq).le)).le

theorem wallIterationCount_le_log {T m : ℝ} (hT : 1 < T) (hm : 0 < m)
    (hmmax : m < 1/300) {n : ℕ} (hn : 1 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ)) :
    (wallIterationCount T (upperInitialEpsilon m n) (upperFinalResidual n) : ℝ) ≤
      wallLogConstant T * Real.log (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hlogT : 0 ≤ Real.log T := (Real.log_pos hT).le
  have hlogA : 0 < Real.log (5/4 : ℝ) := Real.log_pos (by norm_num)
  have hlogB : 0 < Real.log (4/3 : ℝ) := Real.log_pos (by norm_num)
  have hε := upperInitialEpsilon_mem hT hmmax hn
  have hrpos : 0 < upperFinalResidual n := Real.rpow_pos_of_pos hnpos _
  have hrone : upperFinalResidual n ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnR (by norm_num)
  have hTone : (1 : ℝ) ≤ T := hT.le
  have hratioA : 1 ≤ T/upperInitialEpsilon m n :=
    (le_div_iff₀ hε.1).mpr (by simpa using hε.2.le)
  have hratioB : 1 ≤ T/upperFinalResidual n :=
    (le_div_iff₀ hrpos).mpr (by simpa using hrone.trans hTone)
  have hTscale : Real.log T ≤ Real.log T * Real.log (n : ℝ) := by
    nlinarith
  have hlogratioA : Real.log (T/upperInitialEpsilon m n) ≤
      (Real.log T+1)*Real.log (n : ℝ) := by
    unfold upperInitialEpsilon
    rw [Real.log_div (by linarith : T ≠ 0) (Real.rpow_pos_of_pos hnpos _).ne',
      Real.log_rpow hnpos]
    have hterm := mul_le_mul_of_nonneg_right
      (show -(-(1 : ℝ)/3+40*m) ≤ 1 by linarith) (by linarith : 0 ≤ Real.log (n : ℝ))
    nlinarith
  have hlogratioB : Real.log (T/upperFinalResidual n) ≤
      (Real.log T+5)*Real.log (n : ℝ) := by
    unfold upperFinalResidual
    rw [Real.log_div (by linarith : T ≠ 0) (Real.rpow_pos_of_pos hnpos _).ne',
      Real.log_rpow hnpos]
    nlinarith
  have hcountA := logarithmicCount_le (by norm_num : (1 : ℝ) < 5/4) hratioA
  have hcountB := logarithmicCount_le (by norm_num : (1 : ℝ) < 4/3) hratioB
  have hdivA := div_le_div_of_nonneg_right hlogratioA hlogA.le
  have hdivB := div_le_div_of_nonneg_right hlogratioB hlogB.le
  have hA : (logarithmicCount (5/4) (T/upperInitialEpsilon m n) : ℝ) ≤
      ((Real.log T+1)/Real.log (5/4)+1)*Real.log (n : ℝ) := by
    calc
      _ ≤ Real.log (T/upperInitialEpsilon m n)/Real.log (5/4)+1 := hcountA
      _ ≤ ((Real.log T+1)*Real.log (n : ℝ))/Real.log (5/4)+Real.log (n : ℝ) :=
        add_le_add hdivA hlog
      _ = _ := by ring
  have hB : (logarithmicCount (4/3) (T/upperFinalResidual n) : ℝ) ≤
      ((Real.log T+5)/Real.log (4/3)+1)*Real.log (n : ℝ) := by
    calc
      _ ≤ Real.log (T/upperFinalResidual n)/Real.log (4/3)+1 := hcountB
      _ ≤ ((Real.log T+5)*Real.log (n : ℝ))/Real.log (4/3)+Real.log (n : ℝ) :=
        add_le_add hdivB hlog
      _ = _ := by ring
  unfold wallIterationCount wallLogConstant
  rw [Nat.cast_add]
  linarith

noncomputable def upperWallStepLedger (m : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)^(-(5 : ℝ)/6+27*m+20*(m/10000)) +
  (n : ℝ)^(-(5 : ℝ)/6+65*m+m/10000)*(Real.log (n : ℝ))^3 +
  (n : ℝ)^(-(10 : ℝ))

theorem wall_cost_ledger_bound {A B D R X L Ci Cw H : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hL : 1 ≤ L) (hCi : 0 ≤ Ci) (hCw : 0 ≤ Cw) (hH : 0 ≤ H)
    (htail : X*L ≤ R) :
    Ci*(A+B)+H*L*(Cw*(B+D*L^3+X))+R/4 ≤
      (Ci+H*Cw+1)*(A+D*L^4+B*L+R) := by
  let W := H*Cw
  have hW : 0 ≤ W := mul_nonneg hH hCw
  have hBL : 0 ≤ B*L := mul_nonneg hB (by linarith)
  have hDL : 0 ≤ D*L^4 := mul_nonneg hD (pow_nonneg (by linarith) _)
  have hBsmall : B ≤ B*L := by nlinarith
  have hAi : Ci*A ≤ (Ci+W+1)*A :=
    mul_le_mul_of_nonneg_right (by linarith) hA
  have hBi : Ci*B+W*(B*L) ≤ (Ci+W+1)*(B*L) := by
    have hi := mul_le_mul_of_nonneg_left hBsmall hCi
    nlinarith
  have hDi : W*(D*L^4) ≤ (Ci+W+1)*(D*L^4) :=
    mul_le_mul_of_nonneg_right (by linarith) hDL
  have hRi : W*(X*L)+R/4 ≤ (Ci+W+1)*R := by
    have ht := mul_le_mul_of_nonneg_left htail hW
    have hciR : 0 ≤ Ci*R := mul_nonneg hCi hR
    nlinarith
  calc
    _ = (Ci*A+(Ci*B+W*(B*L)))+(W*(D*L^4)+(W*(X*L)+R/4)) := by
      dsimp [W]
      ring
    _ ≤ ((Ci+W+1)*A+(Ci+W+1)*(B*L))+
        ((Ci+W+1)*(D*L^4)+(Ci+W+1)*R) :=
      add_le_add (add_le_add hAi hBi) (add_le_add hDi hRi)
    _ = _ := by dsimp [W]; ring

theorem eventually_upperPressureLedger_of_wall_cost (p : ℕ → ℝ → ℝ)
    {T m Ci Cw : ℝ} (hT : 1 < T) (hm : 0 < m) (hmmax : m < 1/300)
    (hCi : 0 ≤ Ci) (hCw : 0 ≤ Cw)
    (hinitial : ∀ᶠ n : ℕ in atTop,
      p n (upperInitialEpsilon m n)-p n 0 ≤ Ci *
        ((n : ℝ)^(-(5 : ℝ)/6+95*m)+
          (n : ℝ)^(-(5 : ℝ)/6+27*m+20*(m/10000))))
    (hwall : ∀ᶠ n : ℕ in atTop, ∀ x : ℝ,
      upperInitialEpsilon m n ≤ x → x < T →
        p n (wallStep T x)-p n x ≤ Cw * upperWallStepLedger m n)
    (hslope : ∀ᶠ n : ℕ in atTop, ∀ x : ℝ,
      upperInitialEpsilon m n ≤ x → x ≤ T →
        p n T-p n x ≤ (n : ℝ)^(-(1 : ℝ)/6+5*m)/4*(T-x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      p n T-p n 0 ≤ C * upperPressureLedger m n := by
  let H := wallLogConstant T
  have hH : 0 ≤ H := (wallLogConstant_pos hT).le
  refine ⟨Ci+H*Cw+1, by positivity, ?_⟩
  have hlogs : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have htail := eventually_nat_rpow_mul_log_pow_le 1
    (show -(10 : ℝ) < -(5 : ℝ)+(-(1 : ℝ)/6+5*m) by linarith)
  filter_upwards [hinitial, hwall, hslope, hlogs, htail, eventually_ge_atTop (1 : ℕ)]
    with n hninitial hnwall hnslope hnlog hntail hn1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hε := upperInitialEpsilon_mem hT hmmax hn1
  have hr : 0 < upperFinalResidual n := Real.rpow_pos_of_pos hnpos _
  have hs : 0 ≤ (n : ℝ)^(-(1 : ℝ)/6+5*m) := Real.rpow_nonneg hnpos.le _
  have hstepnonneg : 0 ≤ Cw*upperWallStepLedger m n := by
    unfold upperWallStepLedger
    positivity
  have htelescope := wall_upper_telescope (p n) hε hr hs hnwall hnslope
  have hcount := wallIterationCount_le_log hT hm hmmax hn1 hnlog
  have herror := mul_le_mul_of_nonneg_right hcount hstepnonneg
  have hmain : p n T-p n 0 ≤
      Ci*((n : ℝ)^(-(5 : ℝ)/6+95*m)+
        (n : ℝ)^(-(5 : ℝ)/6+27*m+20*(m/10000)))+
      H*Real.log (n : ℝ)*(Cw*upperWallStepLedger m n)+
      ((n : ℝ)^(-(5 : ℝ))*(n : ℝ)^(-(1 : ℝ)/6+5*m))/4 := by
    dsimp only [H, upperFinalResidual] at *
    linarith
  have hsmalltail : (n : ℝ)^(-(10 : ℝ))*Real.log (n : ℝ) ≤
      (n : ℝ)^(-(5 : ℝ))*(n : ℝ)^(-(1 : ℝ)/6+5*m) := by
    rw [← Real.rpow_add hnpos]
    simpa only [pow_one] using hntail
  have hledger := wall_cost_ledger_bound
    (A := (n : ℝ)^(-(5 : ℝ)/6+95*m))
    (B := (n : ℝ)^(-(5 : ℝ)/6+27*m+20*(m/10000)))
    (D := (n : ℝ)^(-(5 : ℝ)/6+65*m+m/10000))
    (R := (n : ℝ)^(-(5 : ℝ))*(n : ℝ)^(-(1 : ℝ)/6+5*m))
    (X := (n : ℝ)^(-(10 : ℝ))) (L := Real.log (n : ℝ))
    (Ci := Ci) (Cw := Cw) (H := H)
    (by positivity) (by positivity) (by positivity) (by positivity)
    hnlog hCi hCw hH hsmalltail
  apply hmain.trans
  simpa only [upperWallStepLedger, upperPressureLedger, add_assoc] using hledger

end OAI.SKFluctuations.PositiveLaplaceAssembly
