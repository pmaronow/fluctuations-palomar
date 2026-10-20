module

public import SKBarriers2.Corner.FrozenRowsMovingTestProfiles

@[expose] public section

noncomputable section
open scoped BigOperators Topology
namespace SKBarriers2
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def movingTestProfileUniformCoefficient (r p : ℕ) (K : ℝ) : ℝ :=
  16*(1+6*(2:ℝ)^r*K+4*((2:ℝ)^r)^2*K^2)*
    (1+3*K)^p*(1+K)^(p+1)*K^r

theorem movingTestProfileCoefficient_uniform {r p : ℕ} {K W : ℝ}
    (hp : 2 ≤ p) (hK : 1 ≤ K) (hW : 1 ≤ W)
    (A : E →L[ℝ] E) (d v : E) (hA : ‖A‖ ≤ K) (hd : ‖d‖ ≤ K*W) (hv : ‖v‖ ≤ K)
    (t : ℝ) :
    movingTestProfileCoefficient r p A d v (K*(1+|t|)) t ≤
      movingTestProfileUniformCoefficient r p K*W^p*(1+|t|)^(p+2) := by
  let T := 1+|t|
  let G := 1+3*K
  let H := 1+K
  let M := K^r
  let a := (2:ℝ)^r
  let F := 1+6*a*K+4*a^2*K^2
  let Z := G^p*H^(p+1)*M*W^p*T^p
  let U := F*G^p*H^(p+1)*M
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hW0 : 0 ≤ W := le_trans (by norm_num) hW
  have hT : 1 ≤ T := by dsimp only [T]; linarith [abs_nonneg t]
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hG : 1 ≤ G := by dsimp only [G]; linarith
  have hH : 1 ≤ H := by dsimp only [H]; linarith
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hF : 1 ≤ F := by
    dsimp only [F]
    nlinarith only [mul_nonneg ha hK0,sq_nonneg (a*K)]
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hKW : K ≤ K*W := by nlinarith only [mul_nonneg hK0 (sub_nonneg.mpr hW)]
  have hbase : 1+‖A‖+‖d‖ ≤ G*W := by
    have HM : 1+‖A‖+‖d‖ ≤ 1+K+K*W := by linarith only [hA,hd]
    apply HM.trans
    dsimp only [G]
    nlinarith only [hKW,hW,hK0]
  have hVG : ‖v‖ ≤ G*W := by
    apply hv.trans (hKW.trans _)
    exact mul_le_mul_of_nonneg_right (by dsimp only [G]; linarith) hW0
  have hnoise : 1+‖A‖+‖d+t • v‖ ≤ G*W*T := by
    have HN := norm_add_le d (t • v)
    rw [norm_smul,Real.norm_eq_abs] at HN
    calc
      _ ≤ (1+‖A‖+‖d‖)+|t| * ‖v‖ := by linarith only [HN]
      _ ≤ G*W+|t| * (G*W) := add_le_add hbase
        (mul_le_mul_of_nonneg_left hVG (abs_nonneg t))
      _ = _ := by dsimp only [T]; ring
  have hbase' : 1+‖A‖+‖d‖ ≤ G*W*T := hbase.trans
    (le_mul_of_one_le_right (by positivity) hT)
  have hM' : max 1 ‖A‖^r ≤ M :=
    pow_le_pow_left₀ (by positivity) (max_le hK hA) r
  have hweight {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ G*W*T) {s : ℕ} (hs : s ≤ p) :
      w^s*max 1 ‖A‖^r ≤ Z := by
    have HH := one_le_pow₀ hH (n := p+1)
    calc
      _ ≤ (G*W*T)^s*M := mul_le_mul (pow_le_pow_left₀ hw0 hw s) hM' (by positivity) (by positivity)
      _ = G^s*M*W^s*T^s := by simp only [mul_pow]; ring
      _ ≤ G^p*M*W^p*T^p := by gcongr
      _ ≤ (G^p*M*W^p*T^p)*H^(p+1) := le_mul_of_one_le_right (by positivity) HH
      _ = _ := by dsimp only [Z]; ring
  have hwt {s : ℕ} (hs : s ≤ p) := hweight (by positivity : 0 ≤ 1+‖A‖+‖d+t • v‖) hnoise hs
  have hwz {s : ℕ} (hs : s ≤ p) := hweight (by positivity : 0 ≤ 1+‖A‖+‖d‖) hbase' hs
  have hT2 : 1 ≤ T^2 := one_le_pow₀ hT
  have hTT2 : T ≤ T^2 := by nlinarith only [mul_nonneg hT0 (sub_nonneg.mpr hT)]
  have hsecond : 1+6*a*(K*T)+4*a^2*(K*T)^2 ≤ F*T^2 := by
    have HL := mul_le_mul_of_nonneg_left hTT2 (show 0 ≤ 6*a*K by positivity)
    dsimp only [F]
    nlinarith only [hT2,HL]
  have hfirst : 1+2*a*(K*T) ≤ F*T^2 := by
    apply le_trans _ hsecond
    nlinarith only [mul_nonneg (show 0 ≤ 4*a*K by positivity) hT0,
      mul_nonneg (show 0 ≤ 4*a^2 by positivity) (sq_nonneg (K*T))]
  have hFT : 1 ≤ F*T^2 := hF.trans (le_mul_of_one_le_right (by linarith) hT2)
  have hbound {w Q : ℝ} (hw : 0 ≤ w) (hwZ : w ≤ Z) (hQ : Q ≤ F*T^2) :
      w*Q ≤ U*W^p*T^(p+2) := by
    calc
      _ ≤ w*(F*T^2) := mul_le_mul_of_nonneg_left hQ hw
      _ ≤ Z*(F*T^2) := mul_le_mul_of_nonneg_right hwZ (by positivity)
      _ = _ := by dsimp only [U,Z]; rw [pow_add]; ring
  have hvalue {w : ℝ} (hw : 0 ≤ w) (hwZ : w ≤ Z) : w ≤ U*W^p*T^(p+2) := by
    simpa only [mul_one] using hbound hw hwZ hFT
  have hfirstt {s : ℕ} (hs : s ≤ p) :
      movingTestFirstProfileCoefficient r s A (d+t • v) (K*T) ≤ U*W^p*T^(p+2) := by
    unfold movingTestFirstProfileCoefficient
    exact hbound (by positivity) (hwt hs) hfirst
  have hfirstz {s : ℕ} (hs : s ≤ p) :
      movingTestFirstProfileCoefficient r s A d (K*T) ≤ U*W^p*T^(p+2) := by
    unfold movingTestFirstProfileCoefficient
    exact hbound (by positivity) (hwz hs) hfirst
  have hsecondt : movingTestSecondCoefficient r p A (d+t • v) (K*T) ≤ U*W^p*T^(p+2) := by
    unfold movingTestSecondCoefficient
    exact hbound (by positivity) (hwt le_rfl) hsecond
  have hcenter : movingTestCenteredSplitCoefficient r (p-2) A d v*T^(p-2+1) ≤
      U*W^p*T^(p+2) := by
    have hdir : ‖v‖*(1+‖v‖)^(p-2) ≤ H^(p+1) := by
      calc
        _ ≤ H*H^(p-2) := by gcongr <;> dsimp only [H] <;> linarith
        _ = H^(p-2+1) := by rw [pow_succ]; ring
        _ ≤ _ := pow_le_pow_right₀ hH (by omega)
    have hm : (1+‖A‖+‖d‖)^(p-2) ≤ G^p*W^p := by
      calc
        _ ≤ (G*W)^(p-2) := pow_le_pow_left₀ (by positivity) hbase _
        _ = G^(p-2)*W^(p-2) := mul_pow _ _ _
        _ ≤ _ := by gcongr <;> omega
    have ht : T^(p-2+1) ≤ T^p := pow_le_pow_right₀ hT (by omega)
    apply hvalue (by unfold movingTestCenteredSplitCoefficient; positivity)
    unfold movingTestCenteredSplitCoefficient
    calc
      _ ≤ H^(p+1)*(G^p*W^p)*M*T^p := by gcongr
      _ = _ := by dsimp only [Z]; ring
  have hslot (i : Fin 8) : movingTestProfileBudgets r p A d v (K*T) t i ≤ U*W^p*T^(p+2) := by
    fin_cases i <;> norm_num [movingTestProfileBudgets]
    · exact hvalue (by positivity) (hwt le_rfl)
    · exact hvalue (by positivity) (hwz le_rfl)
    · exact hfirstt le_rfl
    · exact hfirstz le_rfl
    · exact hsecondt
    · exact hcenter
    · exact hfirstt (by omega)
    · exact hfirstz (by omega)
  calc
    _ ≤ 2*∑ _i : Fin 8, U*W^p*T^(p+2) := by
      unfold movingTestProfileCoefficient
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hslot i)) (by norm_num)
    _ = 16*U*W^p*T^(p+2) := by simp; ring
    _ = _ := by dsimp only [movingTestProfileUniformCoefficient,U,F,a,G,H,M,T]; ring

end SKBarriers2
