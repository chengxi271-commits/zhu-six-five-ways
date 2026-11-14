import Std

namespace QuinqueViae

def properParts (n : Nat) : List Nat :=
  (List.range n).filter (fun d => d != 0 && n % d == 0)

def procession (n : Nat) : Nat := (properParts n).sum
def Perfect (n : Nat) : Prop := 0 < n ∧ procession n = n

/- First way: first positive unmoved term under procession from proper parts. -/
def ViaMotion (n : Nat) : Prop :=
  0 < n ∧ procession n = n ∧
  ∀ m : Nat, 0 < m → m < n → procession m ≠ m

/- Second way: proper (non-self) causes exhaust the effect. -/
def ViaCause (n : Nat) : Prop :=
  properParts n = [1, 2, 3] ∧ procession n = n

/- Third way: least positive common support of duality and trinity. -/
def ViaNecessity (n : Nat) : Prop :=
  0 < n ∧ n % 2 = 0 ∧ n % 3 = 0 ∧
  ∀ m : Nat, 0 < m → m % 2 = 0 → m % 3 = 0 → n ≤ m

/- Fourth way: priority among positive perfect numbers. -/
def ViaDegree (n : Nat) : Prop :=
  Perfect n ∧ ∀ m : Nat, Perfect m → n ≤ m

/- Fifth way: integral half and third, with one unit completing the whole. -/
def ViaPurpose (n : Nat) : Prop :=
  0 < n ∧ n % 2 = 0 ∧ n % 3 = 0 ∧ n / 2 + n / 3 + 1 = n

theorem six_parts : properParts 6 = [1, 2, 3] := by decide
theorem six_perfect : Perfect 6 := by unfold Perfect; decide
theorem twenty_eight_perfect : Perfect 28 := by unfold Perfect; decide
theorem zero_not_perfect : ¬ Perfect 0 := by unfold Perfect; decide

theorem perfect_lower_bound (n : Nat) (h : Perfect n) : 6 ≤ n := by
  obtain ⟨hp, hf⟩ := h
  match n with
  | 0 => omega
  | 1 =>
    have hc : procession 1 = 0 := rfl
    omega
  | 2 =>
    have hc : procession 2 = 1 := rfl
    omega
  | 3 =>
    have hc : procession 3 = 1 := rfl
    omega
  | 4 =>
    have hc : procession 4 = 3 := rfl
    omega
  | 5 =>
    have hc : procession 5 = 1 := rfl
    omega
  | _ + 6 => omega

theorem first_way («主» : Nat) (h : ViaMotion «主») : «主» = 6 := by
  obtain ⟨hp, hf, hfirst⟩ := h
  have hlo := perfect_lower_bound «主» ⟨hp, hf⟩
  have hnot : ¬ 6 < «主» := by
    intro hlt
    exact hfirst 6 (by decide) hlt six_perfect.2
  omega

theorem second_way («主» : Nat) (h : ViaCause «主») : «主» = 6 := by
  obtain ⟨hp, hf⟩ := h
  calc
    «主» = procession «主» := hf.symm
    _ = 6 := by simp [procession, hp]

theorem third_way («主» : Nat) (h : ViaNecessity «主») : «主» = 6 := by
  obtain ⟨hp, htwo, hthree, hleast⟩ := h
  have hupper := hleast 6 (by decide) (by decide) (by decide)
  omega

theorem fourth_way («主» : Nat) (h : ViaDegree «主») : «主» = 6 := by
  obtain ⟨hp, hleast⟩ := h
  have hlo := perfect_lower_bound «主» hp
  have hhi := hleast 6 six_perfect
  omega

theorem fifth_way («主» : Nat) (h : ViaPurpose «主») : «主» = 6 := by
  obtain ⟨hp, htwo, hthree, hwhole⟩ := h
  omega

theorem six_motion : ViaMotion 6 := by
  refine ⟨six_perfect.1, six_perfect.2, ?_⟩
  intro m hp hlt heq
  have hlo := perfect_lower_bound m ⟨hp, heq⟩
  omega

theorem six_cause : ViaCause 6 := by unfold ViaCause; decide
theorem six_necessity : ViaNecessity 6 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro m hp htwo hthree
  omega
theorem six_degree : ViaDegree 6 :=
  ⟨six_perfect, fun m h => perfect_lower_bound m h⟩
theorem six_purpose : ViaPurpose 6 := by unfold ViaPurpose; decide

theorem five_ways_concord (n : Nat) :
    (ViaMotion n ↔ n = 6) ∧ (ViaCause n ↔ n = 6) ∧
    (ViaNecessity n ↔ n = 6) ∧ (ViaDegree n ↔ n = 6) ∧
    (ViaPurpose n ↔ n = 6) := by
  exact ⟨⟨first_way n, fun h => h ▸ six_motion⟩,
         ⟨second_way n, fun h => h ▸ six_cause⟩,
         ⟨third_way n, fun h => h ▸ six_necessity⟩,
         ⟨fourth_way n, fun h => h ▸ six_degree⟩,
         ⟨fifth_way n, fun h => h ▸ six_purpose⟩⟩

theorem existence : ∃ n, ViaMotion n ∧ ViaCause n ∧ ViaNecessity n ∧ ViaDegree n ∧ ViaPurpose n :=
  ⟨6, six_motion, six_cause, six_necessity, six_degree, six_purpose⟩

theorem firstness_is_needed : Perfect 28 ∧ ¬ ViaDegree 28 := by
  refine ⟨twenty_eight_perfect, ?_⟩
  intro h
  have hx := fourth_way 28 h
  contradiction

theorem integrality_is_needed : 4 / 2 + 4 / 3 + 1 = (4 : Nat) ∧ ¬ ViaPurpose 4 := by unfold ViaPurpose; decide
theorem three_routes_distinct_from_conjunction (n : Nat)
    (h : ViaCause n ∨ ViaNecessity n ∨ ViaPurpose n) : n = 6 := by
  rcases h with h | h | h
  · exact second_way n h
  · exact third_way n h
  · exact fifth_way n h

/- Evidence table, not a premise of any theorem. -/
#eval (List.range 13).map (fun n => (n, properParts n, procession n))
#eval (properParts 28, procession 28)
#print axioms first_way
#print axioms second_way
#print axioms third_way
#print axioms fourth_way
#print axioms fifth_way
#print axioms five_ways_concord
#print axioms existence

end QuinqueViae
