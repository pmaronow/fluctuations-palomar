module

public import ComparisonConditionalOptimizedSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Filter
open scoped Topology

namespace RegularEq7

theorem eventually_four_quarter_scalar_budget_draft
    {m delta Kprefix Rcoeff Kinner Kouter Wouter Kfloor : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta)
    (hKprefix : 0 ≤ Kprefix) (hRcoeff : 0 ≤ Rcoeff)
    (hKinner : 0 ≤ Kinner) (hKouter : 0 ≤ Kouter)
    (hWouter : 0 ≤ Wouter)
    (hKfloor : 0 ≤ Kfloor) :
    ∀ᶠ n : ℕ in atTop, ∀ E : ℝ, 0 ≤ E →
      let N := (n+1:ℝ)
      let L := Real.log N
      (Kprefix+Rcoeff)*N^(2*delta)*E+
        3*Kinner*L^6*N^(3*delta)*E+
        Kouter*L^9*N^(-delta/2)*E+
        Wouter*L^4*N^(-3*m-2*delta)*E+
        Kfloor*N^delta*E ≤ N^(10*delta)*E := by
  have h8 : 0 < 8*delta := by positivity
  have h7 : 0 < 7*delta := by positivity
  have h21 : 0 < (21/2:ℝ)*delta := by positivity
  have hmismatch : 0 < 3*m+12*delta := by positivity
  have h9 : 0 < 9*delta := by positivity
  have Hcast : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have HN : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      Hcast.comp (tendsto_add_atTop_nat 1)
  have Hpref := HN.eventually
    (comparison_log_loss_eventually
      (C:=4*(Kprefix+Rcoeff)) (p:=0) (eps:=8*delta)
      (by positivity) h8)
  have Hinner := HN.eventually
    (comparison_log_loss_eventually
      (C:=12*Kinner) (p:=((6:ℕ):ℝ)) (eps:=7*delta)
      (by positivity) h7)
  have Houter := HN.eventually
    (comparison_log_loss_eventually
      (C:=8*Kouter) (p:=((9:ℕ):ℝ)) (eps:=(21/2:ℝ)*delta)
      (by positivity) h21)
  have Hmismatch := HN.eventually
    (comparison_log_loss_eventually
      (C:=8*Wouter) (p:=((4:ℕ):ℝ)) (eps:=3*m+12*delta)
      (by positivity) hmismatch)
  have Hfloor := HN.eventually
    (comparison_log_loss_eventually
      (C:=4*Kfloor) (p:=0) (eps:=9*delta)
      (by positivity) h9)
  filter_upwards [Hpref,Hinner,Houter,Hmismatch,Hfloor]
    with n hp hi ho hw hf E hE
  let N : ℝ := n+1
  let L : ℝ := Real.log N
  have hN : 0 < N := by dsimp [N]; positivity
  have hpow (a b : ℝ) :
      N^a*(N^b*E)=N^(a+b)*E := by
    rw [←mul_assoc,←Real.rpow_add hN]
  have hp' : 4*(Kprefix+Rcoeff) ≤ N^(8*delta) := by
    simpa only [Real.rpow_zero,mul_one,N] using hp
  have hf' : 4*Kfloor ≤ N^(9*delta) := by
    simpa only [Real.rpow_zero,mul_one,N] using hf
  have hpM := mul_le_mul_of_nonneg_right hp'
    (mul_nonneg (Real.rpow_pos_of_pos hN (2*delta)).le hE)
  rw [hpow (8*delta) (2*delta)] at hpM
  have hpExp : 8*delta+2*delta=10*delta := by ring
  rw [hpExp] at hpM
  have HprefQuarter : (Kprefix+Rcoeff)*N^(2*delta)*E ≤
      (1/4:ℝ)*N^(10*delta)*E := by nlinarith only [hpM]
  have hi' : 12*Kinner*L^6 ≤ N^(7*delta) := by
    simpa only [N,L,Real.rpow_natCast] using hi
  have hiM := mul_le_mul_of_nonneg_right hi'
    (mul_nonneg (Real.rpow_pos_of_pos hN (3*delta)).le hE)
  rw [hpow (7*delta) (3*delta)] at hiM
  have hiExp : 7*delta+3*delta=10*delta := by ring
  rw [hiExp] at hiM
  have HinnerQuarter : 3*Kinner*L^6*N^(3*delta)*E ≤
      (1/4:ℝ)*N^(10*delta)*E := by nlinarith only [hiM]
  have ho' : 8*Kouter*L^9 ≤ N^((21/2:ℝ)*delta) := by
    simpa only [N,L,Real.rpow_natCast] using ho
  have hoM := mul_le_mul_of_nonneg_right ho'
    (mul_nonneg (Real.rpow_pos_of_pos hN (-delta/2)).le hE)
  rw [hpow ((21/2:ℝ)*delta) (-delta/2)] at hoM
  have hoExp : (21/2:ℝ)*delta+-delta/2=10*delta := by ring
  rw [hoExp] at hoM
  have HouterQuarter : Kouter*L^9*N^(-delta/2)*E ≤
      (1/8:ℝ)*N^(10*delta)*E := by nlinarith only [hoM]
  have hw' : 8*Wouter*L^4 ≤ N^(3*m+12*delta) := by
    simpa only [N,L,Real.rpow_natCast] using hw
  have hwM := mul_le_mul_of_nonneg_right hw'
    (mul_nonneg (Real.rpow_pos_of_pos hN (-3*m-2*delta)).le hE)
  rw [hpow (3*m+12*delta) (-3*m-2*delta)] at hwM
  have hwExp : (3*m+12*delta)+(-3*m-2*delta)=10*delta := by ring
  rw [hwExp] at hwM
  have HmismatchEighth : Wouter*L^4*N^(-3*m-2*delta)*E ≤
      (1/8:ℝ)*N^(10*delta)*E := by nlinarith only [hwM]
  have hfM := mul_le_mul_of_nonneg_right hf'
    (mul_nonneg (Real.rpow_pos_of_pos hN delta).le hE)
  rw [hpow (9*delta) delta] at hfM
  have hfExp : 9*delta+delta=10*delta := by ring
  rw [hfExp] at hfM
  have HfloorQuarter : Kfloor*N^delta*E ≤
      (1/4:ℝ)*N^(10*delta)*E := by nlinarith only [hfM]
  dsimp only [N,L]
  nlinarith only [HprefQuarter,HinnerQuarter,HouterQuarter,
    HmismatchEighth,HfloorQuarter]

end RegularEq7
end OAI.SKFluctuations.LaplaceWindowFormalization
