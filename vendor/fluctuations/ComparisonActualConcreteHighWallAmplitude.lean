module

public import ComparisonActualHighWallOverlapAmplitude
public import ConcreteWallPowerBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal
set_option maxHeartbeats 9000000

structure ActualConcreteHighWallNumeric (m : ℝ) (n : ℕ) : Prop where
  hn : 0 < n
  hd1 : wallHighD m n ≤ 1
  hs : wallHighMass m n∈Ioc (0:ℝ) (1/4)
  hq : 2 ≤ (n:ℝ)^(m/10000)
  hsmall : comparisonSmallMass (n:ℝ) (wallHighError m n) ≤ wallHighD m n
  hmargin : (wallHighD m n)^2 ≤ upperInitialEpsilon m n
  hscale : comparisonLowerScale (n:ℝ) (wallHighError m n) (wallHighD m n) ≤ wallHighD m n
  hsD : wallHighMass m n ≤ wallHighD m n
  hupper : Real.sqrt (n:ℝ)*wallHighError m n ≤ (wallHighD m n)^2
  hlower : (n:ℝ)^(-(2:ℝ)/3+m)*wallHighD m n ≤ wallHighError m n
  htest : (n:ℝ)*(wallHighError m n)^2 ≤ (wallHighD m n)^4

theorem actualConcreteHighWallNumeric_eventually {m : ℝ}
    (hm : 0 < m) (hmmax : m < 1/300) :
    ∀ᶠ n : ℕ in atTop,ActualConcreteHighWallNumeric m n := by
  have hSlim : Tendsto (wallHighMass m) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by linarith : 0 < (1:ℝ)/6-5*m)).comp
      tendsto_natCast_atTop_atTop using 1
    funext n
    dsimp only [wallHighMass,Function.comp_apply]
    congr 1
    ring
  filter_upwards [wallHighParameters_eventually hm hmmax,
    hSlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4)),
    eventually_ge_atTop (1:ℕ)] with n hp hs hn
  have hn0 : 0 < n := by omega
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr hn0
  have hN1 : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have hpow (a b : ℝ) (hab : a≤b) : (n:ℝ)^a ≤ (n:ℝ)^b :=
    Real.rpow_le_rpow_of_exponent_le hN1 hab
  have hscale : comparisonLowerScale (n:ℝ) (wallHighError m n) (wallHighD m n) ≤
      wallHighD m n := by
    rw [wallHighLowerScale_eq m hn0]
    unfold wallHighD
    exact hpow _ _ (by linarith)
  have hsD : wallHighMass m n ≤ wallHighD m n := by
    unfold wallHighMass wallHighD
    exact hpow _ _ (by linarith)
  have hupper : Real.sqrt (n:ℝ)*wallHighError m n ≤ (wallHighD m n)^2 := by
    have hscale' := hscale
    unfold comparisonLowerScale at hscale'
    exact (div_le_iff₀ (wallHighD_pos m hn0)).mp hscale' |>.trans_eq (by ring)
  have hlower : (n:ℝ)^(-(2:ℝ)/3+m)*wallHighD m n ≤ wallHighError m n := by
    unfold wallHighError
    exact mul_le_mul_of_nonneg_right (hpow _ _ (by linarith)) (wallHighD_pos m hn0).le
  have htest : (n:ℝ)*(wallHighError m n)^2 ≤ (wallHighD m n)^4 := by
    rw [wallHighError_eq m hn0]
    unfold wallHighD
    rw [←Real.rpow_natCast,←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    have hleft : (n:ℝ)*(n:ℝ)^((-(5:ℝ)/6+25*m)*(2:ℝ))=
        (n:ℝ)^(-(2:ℝ)/3+50*m) := by
      calc
        _ = (n:ℝ)^(1:ℝ)*(n:ℝ)^((-(5:ℝ)/6+25*m)*(2:ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hN];congr 1;ring
    simp only [neg_div] at hleft
    rw [hleft]
    exact hpow _ _ (by linarith)
  exact ⟨hn0,hp.2.1,⟨hp.2.2.1.1,hs.le⟩,hp.2.2.2.1,hp.2.2.2.2.1,
    hp.2.2.2.2.2,hscale,hsD,hupper,hlower,htest⟩

def actualConcreteHighWallData (T m : ℝ) (n : ℕ)
    (hp : ActualConcreteHighWallNumeric m n) (epsilon theta : ℝ)
    (hepsilon : epsilon∈Ioo (0:ℝ) T) (heps0 : upperInitialEpsilon m n≤epsilon)
    (htheta : theta∈Icc (0:ℝ) 1) : ActualHighWallData n (m/10000) where
  E := wallHighError m n
  d := wallHighD m n
  s := wallHighMass m n
  T := T
  epsilon := epsilon
  theta := theta
  tau := (n:ℝ)^(-(10:ℝ))
  hn := hp.hn
  hE := wallHighError_pos m hp.hn
  hd := wallHighD_pos m hp.hn
  hd1 := hp.hd1
  hs := hp.hs
  hq := hp.hq
  hsmall := hp.hsmall
  hepsilon := hepsilon
  htheta := htheta
  htau := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.hn) _
  hdepsilon := hp.hmargin.trans heps0

def actualConcreteHighWallOverlapMinimum
    {T m cl cu : ℝ} {n : ℕ} (hp : ActualConcreteHighWallNumeric m n)
    {epsilon theta : ℝ} (hepsilon : epsilon∈Ioo (0:ℝ) T)
    (heps0 : upperInitialEpsilon m n≤epsilon) (htheta : theta∈Icc (0:ℝ) 1)
    (alpha : (actualConcreteHighWallData T m n hp epsilon theta hepsilon heps0 htheta).Profile)
    (hmin : ∀beta,
      (actualConcreteHighWallData T m n hp epsilon theta hepsilon heps0 htheta).objective alpha ≤
      (actualConcreteHighWallData T m n hp epsilon theta hepsilon heps0 htheta).objective beta)
    (hregular : ∀r∈Icc (wallHighD m n) 1,cl*r≤alpha.val.val r ∧ alpha.val.val r≤cu*r) :
    ActualHighWallOverlapMinimum n m (m/10000) cl cu 1 1 1 1 T := by
  let a:=actualConcreteHighWallData T m n hp epsilon theta hepsilon heps0 htheta
  have hg : a.g a.d=a.d^2 := by
    dsimp only [ActualHighWallData.g]
    rw [laplaceFinalStrength_eq a.hd.ne']
    simp only [div_self a.hd.ne',laplaceComparisonShape,le_refl,ite_true,mul_one]
  refine ⟨a,alpha,hmin,a.d,a.d,a.hd,hp.hscale,hp.hsD,?_,?_,hp.hd1,
    hp.hupper,?_,?_,hregular,le_rfl⟩
  · exact ⟨a.hrbounds.2.1.trans (by linarith [a.hd]),a.hd1⟩
  · simp
  · change (n:ℝ)^(-(2:ℝ)/3+m)*wallHighD m n ≤ 1*wallHighError m n
    simpa only [one_mul] using hp.hlower
  · rw [one_mul,hg]
    change (n:ℝ)*(wallHighError m n)^2 ≤ (wallHighD m n)^2*(wallHighD m n)^2
    convert hp.htest using 1 <;> ring

theorem actual_concrete_high_wall_omitted_clock_amplitude
    {T m cl cu : ℝ} (hm : 0 < m) (hcl : 0 < cl) (hcu : 0 < cu) :
    ∃C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀hp : ActualConcreteHighWallNumeric m n,
      ∀(epsilon : ℝ) (hepsilon : epsilon∈Ioo (0:ℝ) T) (heps0 : upperInitialEpsilon m n≤epsilon),
      ∀(theta : ℝ) (htheta : theta∈Icc (0:ℝ) 1),
      ∀alpha : (actualConcreteHighWallData T m n hp epsilon theta hepsilon heps0 htheta).Profile,
      (∀beta,(actualConcreteHighWallData T m n hp epsilon theta hepsilon heps0 htheta).objective alpha ≤
        (actualConcreteHighWallData T m n hp epsilon theta hepsilon heps0 htheta).objective beta) →
      (∀r∈Icc (wallHighD m n) 1,cl*r≤alpha.val.val r ∧ alpha.val.val r≤cu*r) →
      ∀u∈Ioo (0:ℝ) (wallHighMass m n),
        let a:=actualConcreteHighWallData T m n hp epsilon theta hepsilon heps0 htheta
        orderedPathS n (a.bf alpha) (a.hf alpha) u ≤ C*wallHighD m n ∧
        Real.sqrt (orderedPathB n (a.bf alpha) (a.hf alpha) u-
          (orderedPathS n (a.bf alpha) (a.hf alpha) u)^2) ≤ C*wallHighD m n ∧
        actualMixedClock n (a.bf alpha) (a.hf alpha) u ≤ (1/16+T*C)*wallHighD m n := by
  obtain ⟨C,hC,hamp⟩ := eventually_actual_high_wall_omitted_clock_amplitude
    (D:=1) (C0:=1) (Ct:=1) (Az:=1) (m:=m) (delta:=m/10000)
    T hm (by positivity) (by linarith) hcl hcu (by norm_num) zero_lt_one (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [hamp] with n hn
  intro hp epsilon hepsilon heps0 theta htheta alpha hmin hregular u hu
  let a:=actualConcreteHighWallOverlapMinimum hp hepsilon heps0 htheta alpha hmin hregular
  exact hn a le_rfl u hu

end OAI.SKFluctuations.LaplaceWindowFormalization
