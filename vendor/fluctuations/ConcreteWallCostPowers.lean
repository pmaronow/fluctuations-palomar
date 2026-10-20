module

public import WallActualCostBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal

def concreteHighWallPhysicalCost (T C m : ℝ) (n : ℕ) (epsilon : ℝ) : ℝ :=
  let s := wallHighMass m n
  let d := wallHighD m n
  let rmin := concreteWallRadius (n:ℝ) (m/10000) (wallHighError m n) d s
  let A := wallMeanScale C d epsilon
  wallLowStrength T epsilon/4*(wallPhysicalCostU s A n+2*s*(wallLowRadius d rmin epsilon)^2)+
    (wallLowStrength T epsilon*wallPhysicalCostV T epsilon d rmin s A n/4)*
      (-Real.log ((n:ℝ)^(-(10:ℝ))))+
    wallLipschitzConstant T epsilon d rmin*(n:ℝ)^(-(10:ℝ))

theorem wallHighMeanCost_power (m : ℝ) {n : ℕ} (hn : 0 < n) :
    wallHighMass m n*(wallHighD m n)^6/upperInitialEpsilon m n=
      (n:ℝ)^(-(5:ℝ)/6+55*m) := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  unfold wallHighMass wallHighD upperInitialEpsilon
  rw [← Real.rpow_natCast,← Real.rpow_mul hN.le,← Real.rpow_add hN,← Real.rpow_sub hN]
  congr 1
  norm_num
  ring

def highWallCostConstant (T C : ℝ) : ℝ :=
  (3/2:ℝ)*C^2+429000*(10/Real.log 2+2)*C*12+T*(10/Real.log 2+3)+1

theorem concreteHighWallPhysicalCost_eventually {T C m : ℝ}
    (hT : 1 < T) (hC : 1 ≤ C) (hm : 0 < m) (hmmax : m < 1/300) :
    0 < highWallCostConstant T C ∧
      ∀ᶠ n : ℕ in atTop, ∀ epsilon ∈ Ioo (0:ℝ) T,
        upperInitialEpsilon m n ≤ epsilon →
        concreteHighWallPhysicalCost T C m n epsilon ≤
          highWallCostConstant T C*upperWallStepLedger m n := by
  have hC0 : 0 ≤ C := by linarith
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hK : 0 < highWallCostConstant T C := by unfold highWallCostConstant; positivity
  refine ⟨hK,?_⟩
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) :=
    ((Real.tendsto_log_atTop).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  have htail := eventually_nat_rpow_mul_log_pow_le 1
    (show -(10:ℝ) < -(5:ℝ)/6+27*m+20*(m/10000) by linarith)
  filter_upwards [wallHighParameters_eventually hm hmmax,hlog,htail,eventually_ge_atTop (1:ℕ)]
    with n hparams hlogn htailn hn
  intro epsilon hepsilon heps0
  have hn0 : 0 < n := by omega
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr hn0
  have hN1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  let s := wallHighMass m n
  let d := wallHighD m n
  let rmin := concreteWallRadius (n:ℝ) (m/10000) (wallHighError m n) d s
  have hr := concreteWallRadius_bounds hN (wallHighError_pos m hn0) hparams.1 hparams.2.1
    hparams.2.2.1.1.le hparams.2.2.2.1 hparams.2.2.2.2.1
  have hrC : rmin ≤ 2*C*d := by
    have hp := mul_le_mul_of_nonneg_right hC (wallHighD_pos m hn0).le
    dsimp only [rmin,d]
    linarith [hr.2.1]
  have hdepsilon : d^2 ≤ epsilon := hparams.2.2.2.2.2.trans heps0
  have hc := wall_actual_step_cost_budget hn0 hlogn (wallHighMass_pos m hn0) hC0
    (wallHighD_pos m hn0) hr.1 (hr.2.2.trans (by norm_num)) hrC hepsilon
    (upperInitialEpsilon_mem hT hmmax hn).1 heps0 hdepsilon
  change concreteHighWallPhysicalCost T C m n epsilon ≤
    highWallCostConstant T C*upperWallStepLedger m n
  rw [show (10/Real.log (2:ℝ)+2)+1=10/Real.log 2+3 by ring] at hc
  change concreteHighWallPhysicalCost T C m n epsilon ≤
    (3/2:ℝ)*C^2*s*d^6/upperInitialEpsilon m n+
      429000*(10/Real.log 2+2)*C*d/((n:ℝ)*s*rmin)*(Real.log (n:ℝ))^3+
      T*(10/Real.log 2+3)*Real.log (n:ℝ)*(n:ℝ)^(-(10:ℝ)) at hc
  let B := (n:ℝ)^(-(5:ℝ)/6+27*m+20*(m/10000))
  let D := (n:ℝ)^(-(5:ℝ)/6+65*m+m/10000)*(Real.log (n:ℝ))^3
  let a := (3/2:ℝ)*C^2
  let b := 429000*(10/Real.log 2+2)*C*12
  let c := T*(10/Real.log 2+3)
  have hleading : s*d^6/upperInitialEpsilon m n ≤ D := by
    rw [wallHighMeanCost_power m hn0]
    have hrpow := Real.rpow_le_rpow_of_exponent_le hN1
      (show -(5:ℝ)/6+55*m ≤ -(5:ℝ)/6+65*m+m/10000 by linarith)
    have hlog3 : (1:ℝ) ≤ (Real.log (n:ℝ))^3 := one_le_pow₀ hlogn
    exact hrpow.trans (le_mul_of_one_le_right (Real.rpow_nonneg hN.le _) hlog3)
  have hfirst : (3/2:ℝ)*C^2*s*d^6/upperInitialEpsilon m n ≤ a*D := by
    have hp := mul_le_mul_of_nonneg_left hleading (by positivity : 0 ≤ a)
    convert hp using 1 <;> dsimp [a] <;> ring
  have hsecond : 429000*(10/Real.log 2+2)*C*d/((n:ℝ)*s*rmin)*(Real.log (n:ℝ))^3 ≤ b*D := by
    have hp := mul_le_mul_of_nonneg_left (wallHighRadius_noise_budget hm.le hn)
      (by positivity : 0 ≤ 429000*(10/Real.log 2+2)*C*(Real.log (n:ℝ))^3)
    convert hp using 1 <;> dsimp [s,d,rmin,b,D] <;> ring
  have hthird : T*(10/Real.log 2+3)*Real.log (n:ℝ)*(n:ℝ)^(-(10:ℝ)) ≤ c*B := by
    simp only [pow_one] at htailn
    have hp := mul_le_mul_of_nonneg_left htailn (by positivity : 0 ≤ c)
    convert hp using 1 <;> dsimp [c,B] <;> ring
  have hKD : (a+b)*D ≤ highWallCostConstant T C*D := by
    apply mul_le_mul_of_nonneg_right _ (by dsimp [D]; positivity)
    dsimp [a,b,highWallCostConstant]
    linarith [show 0 ≤ T*(10/Real.log (2:ℝ)+3) by positivity]
  have hKB : c*B ≤ highWallCostConstant T C*B := by
    apply mul_le_mul_of_nonneg_right _ (by dsimp [B]; positivity)
    dsimp [c,highWallCostConstant]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 429000*(10/Real.log 2+2)*C) (by norm_num : (0:ℝ) ≤ 12)]
  have hsmall : 0 ≤ highWallCostConstant T C*(n:ℝ)^(-(10:ℝ)) := by positivity
  change concreteHighWallPhysicalCost T C m n epsilon ≤
    highWallCostConstant T C*(B+D+(n:ℝ)^(-(10:ℝ)))
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
