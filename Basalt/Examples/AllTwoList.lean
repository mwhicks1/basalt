import Basalt

open RandomChoice

def AllTwos (l : List Nat) : Prop := ∀ x ∈ l, x = 2

def AllTwos.cost (l : List Nat) : Nat := l.length + 1

def genAllTwos [Gen G] : G (List Nat) :=
  pick
    (fun () => pure [])
    (fun () => do
      let xs ← genAllTwos
      return 2 :: xs)
partial_fixpoint

theorem genAllTwos_support : a ∈ SPMF.support genAllTwos ↔ AllTwos a := by
  induction a with
  | nil =>
    rw [genAllTwos]; simp [AllTwos]
  | cons x xs ih =>
    rw [genAllTwos]
    simp only [bind_pure_comp, SPMF.support_pick, SPMF.support_pure,
      SPMF.support_map, Set.mem_setOf_eq, Set.singleton_union, Set.mem_insert_iff, reduceCtorEq,
      List.cons.injEq, exists_eq_right_right', false_or]
    constructor
    · rintro ⟨hxs, rfl⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · rfl
      · exact ih.mp hxs y hy
    · intro h
      exact ⟨ih.mpr (fun y hy => h y (List.mem_cons.mpr (Or.inr hy))),
             h x (List.mem_cons.mpr (Or.inl rfl))⟩

theorem genAllTwos_terminates : SPMF.IsPMF genAllTwos := by
  refine (SPMF.IsPMF_of_mass_fixpoint
    (g := fun () => (genAllTwos : SPMF (List Nat)))
    (F := fun c => 1 / 2 + 1 / 2 * c)
    ?bounds ?mass) ()
  case bounds =>
    intro c hle hge
    apply ENNReal.eq_one_of_fixed_ineq' hle hge
    intro hmono
    rw [ENNReal.toReal_add (by norm_num) (by aesop), ENNReal.toReal_mul] at hmono
    norm_num at hmono; linarith
  case mass =>
    intro () h
    conv_lhs => rw [genAllTwos]
    simp

theorem genAllTwos_cost : IsBounded genAllTwos AllTwos.cost := by
  open Lean.Order in
  delta genAllTwos
  apply fix_induct (motive := fun (g : SPMF.Cost (List Nat)) =>
    IsBounded g AllTwos.cost) _ ?admissible ?step
  case admissible =>
    apply admissible_IsBounded
  case step =>
    intro genAllTwos_rec ih
    simp [IsBounded_iff, AllTwos.cost] at *
    intro xs c hxs
    grind [
      pick,
      SPMF.Cost.mem_support_bind_iff,
      SPMF.Cost.mem_support_choose_iff,
      SPMF.Cost.mem_support_pure_iff
    ]

instance : LawfulGenerator genAllTwos AllTwos AllTwos.cost where
  support_iff := genAllTwos_support
  is_pmf      := genAllTwos_terminates
  is_bounded  := genAllTwos_cost
