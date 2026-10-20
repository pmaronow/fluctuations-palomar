module

public import SKConstants.Completion.N13bc.WeightedFinite
public import SKConstants.Completion.N13bc.GramRate

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace SKConstants.Completion.N13bc
open Blueprint Blueprint4

def sevenTailBudget (n r : ℕ) (B R η : ℝ) : ℝ :=
  2*(10*(2 : ℝ)^r-3)*(5 : ℝ)^(2^r)*Real.exp (-(n : ℝ)*
    min (η^2/(4096*B^2*(r+1 : ℝ)^2*Real.log (2+R)))
      (η/(256*B*(r+1 : ℝ)*Real.sqrt R*Real.log (2+R))))

theorem sevenTailBudget_le_exponential (n r : ℕ) (B R η : ℝ) :
    sevenTailBudget n r B R η ≤ 2*Real.exp
      ((10+Real.log 5)*(2 : ℝ)^r - (n : ℝ)*
        min (η^2/(4096*B^2*(r+1 : ℝ)^2*Real.log (2+R)))
          (η/(256*B*(r+1 : ℝ)*Real.sqrt R*Real.log (2+R)))) := by
  let Q := (n : ℝ)*min (η^2/(4096*B^2*(r+1 : ℝ)^2*Real.log (2+R)))
    (η/(256*B*(r+1 : ℝ)*Real.sqrt R*Real.log (2+R)))
  have hm : 10*(2 : ℝ)^r-3 ≤ Real.exp (10*(2 : ℝ)^r) := by
    linarith [Real.add_one_le_exp (10*(2 : ℝ)^r)]
  have h5 : (5 : ℝ)^(2^r) = Real.exp ((2 : ℝ)^r*Real.log 5) := by
    rw [show (2 : ℝ)^r = ((2^r : ℕ) : ℝ) by norm_cast,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
  change _ ≤ 2*Real.exp ((10+Real.log 5)*(2 : ℝ)^r-Q)
  unfold sevenTailBudget
  calc
    _ ≤ 2*Real.exp (10*(2 : ℝ)^r)*(5 : ℝ)^(2^r)*Real.exp (-Q) := by
      have H := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2)
      have H' := mul_le_mul_of_nonneg_right H (by positivity : 0 ≤ (5 : ℝ)^(2^r))
      convert mul_le_mul_of_nonneg_right H' (Real.exp_pos (-Q)).le using 1 <;> dsimp [Q] <;> ring
    _ = _ := by
      rw [h5]
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [Q]
      ring

theorem sevenTailBudget_eventually_le
    (r : ℕ → ℕ) (R : ℕ → ℝ) (B a u v γ s C D M : ℝ)
    (hB : 0 < B) (has : a < 1-s) (hus : 2*γ+u < s) (hvs : γ+v < s)
    (hs : s < 1) (hC : 0 < C) (hD : 0 ≤ D) (hM : 0 < M)
    (hR : ∀ᶠ n : ℕ in atTop, 1 ≤ R n)
    (hd : ∀ᶠ n : ℕ in atTop, (2 : ℝ)^(r n) ≤ D*(n : ℝ)^a)
    (hv : ∀ᶠ n : ℕ in atTop,
      4096*B^2*(r n+1 : ℝ)^2*Real.log (2+R n) ≤ C*(n : ℝ)^u)
    (hl : ∀ᶠ n : ℕ in atTop,
      256*B*(r n+1 : ℝ)*Real.sqrt (R n)*Real.log (2+R n) ≤ C*(n : ℝ)^v) :
    ∀ᶠ n : ℕ in atTop,
      sevenTailBudget n (r n) B (R n) ((n : ℝ)^(-γ)) ≤
        Real.exp (-(M*(n : ℝ)^(1-s))) := by
  filter_upwards [hR,hd,hv,hl,
    constant_rpow_le_small_rpow a (1-s) (D*(10+Real.log 5)) 1 has
      (by positivity [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)]) (by norm_num),
    constant_rpow_le_small_rpow (1-s) (1-2*γ-u) (M+2) (1/C)
      (by linarith) (by linarith) (by positivity),
    constant_rpow_le_small_rpow (1-s) (1-γ-v) (M+2) (1/C)
      (by linarith) (by linarith) (by positivity),
    constant_rpow_le_small_rpow 0 (1-s) (Real.log 2) 1 (by linarith)
      (Real.log_nonneg (by norm_num)) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hR hd hv hl hdim hquad hlin htwo hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hR0 : 0 < R n := by linarith
  have hlog : 0 < Real.log (2+R n) := Real.log_pos (by linarith)
  have hDq : 0 < 4096*B^2*(r n+1 : ℝ)^2*Real.log (2+R n) := by positivity
  have hDl : 0 < 256*B*(r n+1 : ℝ)*Real.sqrt (R n)*Real.log (2+R n) := by positivity
  have hquad' : (1/C)*(n : ℝ)^(1-2*γ-u) ≤
      (n : ℝ)*((n : ℝ)^(-γ))^2 /
        (4096*B^2*(r n+1 : ℝ)^2*Real.log (2+R n)) := by
    have he : (n : ℝ)*((n : ℝ)^(-γ))^2 = (n : ℝ)^(1-2*γ) := by
      calc
        _ = (n : ℝ)^(1 : ℝ) * (n : ℝ)^((-γ)*2) := by
          rw [Real.rpow_one]
          exact congrArg (fun x : ℝ => (n : ℝ)*x)
            (by simpa only [Nat.cast_ofNat] using (Real.rpow_mul_natCast hn0.le (-γ) 2).symm)
        _ = _ := by rw [← Real.rpow_add hn0]; congr 1 <;> ring
    rw [he]
    calc
      _ = (n : ℝ)^(1-2*γ) / (C*(n : ℝ)^u) := by rw [Real.rpow_sub hn0]; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hDq hv
  have hlin' : (1/C)*(n : ℝ)^(1-γ-v) ≤
      (n : ℝ)*(n : ℝ)^(-γ) /
        (256*B*(r n+1 : ℝ)*Real.sqrt (R n)*Real.log (2+R n)) := by
    have he : (n : ℝ)*(n : ℝ)^(-γ) = (n : ℝ)^(1-γ) := by
      calc
        _ = (n : ℝ)^(1 : ℝ) * (n : ℝ)^(-γ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hn0]; congr 1 <;> ring
    rw [he]
    calc
      _ = (n : ℝ)^(1-γ) / (C*(n : ℝ)^v) := by rw [Real.rpow_sub hn0]; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hDl hl
  have hmin : (M+2)*(n : ℝ)^(1-s) ≤ (n : ℝ)*
      min (((n : ℝ)^(-γ))^2/(4096*B^2*(r n+1 : ℝ)^2*Real.log (2+R n)))
        ((n : ℝ)^(-γ)/(256*B*(r n+1 : ℝ)*Real.sqrt (R n)*Real.log (2+R n))) := by
    rw [mul_min_of_nonneg _ _ hn0.le]
    apply le_min
    · simpa only [mul_div_assoc] using hquad.trans hquad'
    · simpa only [mul_div_assoc] using hlin.trans hlin'
  have hcost := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 10+Real.log 5 by positivity [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)])
  simp only [Real.rpow_zero, mul_one, one_mul] at htwo
  calc
    _ ≤ 2*Real.exp _ := sevenTailBudget_le_exponential _ _ _ _ _
    _ = Real.exp (Real.log 2 + ((10+Real.log 5)*(2 : ℝ)^(r n) - (n : ℝ)*
        min (((n : ℝ)^(-γ))^2/(4096*B^2*(r n+1 : ℝ)^2*Real.log (2+R n)))
          ((n : ℝ)^(-γ)/(256*B*(r n+1 : ℝ)*Real.sqrt (R n)*Real.log (2+R n))))) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem sharpWeighted_strict_margin (p : Parameters) (hp : CoarseExponents4 p) :
    ∃ ε : ℝ, 0 < ε ∧ 2*p.gamma+ε < p.sb ∧ p.gamma+(p.b/4+ε) < p.sb := by
  rcases hp with ⟨_,_,_,_,_,_,_,_,hγ,hγb,_⟩
  let ε := min (p.sb-2*p.gamma) (p.sb-p.gamma-p.b/4) / 2
  have hmin : 0 < min (p.sb-2*p.gamma) (p.sb-p.gamma-p.b/4) :=
    lt_min (by linarith) (by linarith)
  refine ⟨ε, by dsimp [ε]; positivity, ?_, ?_⟩
  · have := min_le_left (p.sb-2*p.gamma) (p.sb-p.gamma-p.b/4)
    dsimp [ε]
    linarith
  · have := min_le_right (p.sb-2*p.gamma) (p.sb-p.gamma-p.b/4)
    dsimp [ε]
    linarith

end SKConstants.Completion.N13bc
