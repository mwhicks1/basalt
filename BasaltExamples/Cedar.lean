/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt
import BasaltFuzz.Cedar

/-!
# Well-typed CedarLite expressions are sound and complete

`CedarLite.genExpr Γ τ` (defined Mathlib-free in `BasaltFuzz/Cedar.lean`, so it can also be fuzzed)
generates exactly the expressions of type `τ` in context `Γ`. This file supplies the inductive typing
judgment `Typed` and proves `IsSoundAndComplete (genExpr Γ τ) (Typed Γ · τ)`, following
`BasaltExamples/STLC/GenTerm.lean`.

The generator is the single source of truth: it is defined once, in the fuzz library, and proved
about here — there is no second copy (contrast `BasaltFuzz/BuggyBST.lean`, forced to duplicate
`BasaltExamples/BST`'s generator because the example imports the `Basalt` umbrella).
-/

open RandomChoice
open CedarLite

namespace CedarLite

/-! ## Typing judgment -/

/-- `lookup Γ n τ`: the `n`-th variable of context `Γ` has type `τ`. -/
inductive lookup : List CType → Nat → CType → Prop where
  | Now : ∀ τ Γ, lookup (τ :: Γ) 0 τ
  | Later : ∀ τ τ' n Γ, lookup Γ n τ → lookup (τ' :: Γ) (n + 1) τ

/-- `Typed Γ e τ`: expression `e` has type `τ` in context `Γ`. One rule per generator branch.
Explicit binders (as `BasaltExamples/STLC`) so `induction` on a derivation names them. -/
inductive Typed : List CType → Expr → CType → Prop where
  | lit_bool : ∀ Γ b, Typed Γ (.lit (.bool b)) .bool
  | lit_int  : ∀ Γ i, Typed Γ (.lit (.int i)) .int
  | var      : ∀ Γ i τ, lookup Γ i τ → Typed Γ (.var i) τ
  | ite      : ∀ Γ c t e τ, Typed Γ c .bool → Typed Γ t τ → Typed Γ e τ → Typed Γ (.ite c t e) τ
  | and      : ∀ Γ a b, Typed Γ a .bool → Typed Γ b .bool → Typed Γ (.and a b) .bool
  | or       : ∀ Γ a b, Typed Γ a .bool → Typed Γ b .bool → Typed Γ (.or a b) .bool
  | not      : ∀ Γ a, Typed Γ a .bool → Typed Γ (.unaryApp .not a) .bool
  | neg      : ∀ Γ a, Typed Γ a .int → Typed Γ (.unaryApp .neg a) .int
  | less     : ∀ Γ a b, Typed Γ a .int → Typed Γ b .int → Typed Γ (.binaryApp .less a b) .bool
  | lessEq   : ∀ Γ a b, Typed Γ a .int → Typed Γ b .int → Typed Γ (.binaryApp .lessEq a b) .bool
  | eq       : ∀ Γ a b τ', Typed Γ a τ' → Typed Γ b τ' → Typed Γ (.binaryApp .eq a b) .bool
  | add      : ∀ Γ a b, Typed Γ a .int → Typed Γ b .int → Typed Γ (.binaryApp .add a b) .int
  | sub      : ∀ Γ a b, Typed Γ a .int → Typed Γ b .int → Typed Γ (.binaryApp .sub a b) .int
  | mul      : ∀ Γ a b, Typed Γ a .int → Typed Γ b .int → Typed Γ (.binaryApp .mul a b) .int

/-! ## Variable-lookup lemmas (as `BasaltExamples/STLC`) -/

theorem getElem?_lookup : Γ[i]? = some τ → lookup Γ i τ := by
  intro h
  induction Γ generalizing i τ with
  | nil => simp at h
  | cons τ' Γ' IH =>
    cases i with
    | zero => simp at h; subst h; constructor
    | succ i' => apply lookup.Later; apply IH; simpa using h

theorem lookup_getElem? : lookup Γ i τ → Γ[i]? = some τ := by
  intro h
  induction h with
  | Now τ Γ => simp
  | Later τ τ' n Γ hl IH => simpa using IH

theorem varsWithType_sound : e ∈ varsWithType Γ τ → Typed Γ e τ := by
  intro h
  simp only [varsWithType, List.mem_filterMap] at h
  obtain ⟨⟨τ', i⟩, hmem, hfilt⟩ := h
  simp only at hfilt
  split at hfilt
  · rename_i heq
    simp only [Option.some.injEq] at hfilt
    subst hfilt
    apply Typed.var
    apply getElem?_lookup
    rw [List.mk_mem_zipIdx_iff_getElem?] at hmem
    have : τ' = τ := by simpa using heq
    subst this; exact hmem
  · simp at hfilt

theorem varsWithType_complete : lookup Γ i τ → Expr.var i ∈ varsWithType Γ τ := by
  intro h
  simp only [varsWithType, List.mem_filterMap]
  refine ⟨(τ, i), ?_, by simp⟩
  rw [List.mk_mem_zipIdx_iff_getElem?]
  exact lookup_getElem? h

/-! ## Leaf generators -/

theorem genBool.sound_complete : IsSoundAndComplete genBool ⊤ := by
  refine .intro ?sound ?complete
  case sound => rw [IsSoundFor.iff_obs]; walk <;> trivial
  case complete => intro b _; cases b <;> (rw [genBool, SPMF.mem_support_iff_may]; walk)

theorem genNat.sound_complete : IsSoundAndComplete genNat ⊤ := by
  refine .intro (fun _ _ => trivial) ?complete
  intro n
  induction n with
  | zero => intro _; rw [genNat, SPMF.mem_support_iff_may]; walk
  | succ n ih =>
    intro _; rw [genNat, SPMF.mem_support_iff_may]; walk
    exact ⟨n, ih trivial, rfl⟩

theorem genInt.sound_complete : IsSoundAndComplete genInt ⊤ := by
  refine .intro (fun _ _ => trivial) ?complete
  intro i _
  rw [genInt, SPMF.mem_support_iff_may]; walk [genNat.sound_complete.complete.obs]
  by_cases h : 0 ≤ i
  · exact Or.inl ⟨i.toNat, by simp [Int.toNat_of_nonneg h]⟩
  · refine Or.inr ⟨(-i - 1).toNat, ?_⟩
    have : ((-i - 1).toNat : Int) = -i - 1 := Int.toNat_of_nonneg (by omega)
    omega

theorem genCType.sound_complete : IsSoundAndComplete genCType ⊤ := by
  refine .intro ?sound ?complete
  case sound => rw [IsSoundFor.iff_obs]; walk <;> trivial
  case complete => intro τ _; cases τ <;> (rw [genCType, SPMF.mem_support_iff_may]; walk)

theorem genZero.sound : IsSoundFor (genZero τ) (Typed Γ · τ) := by
  cases τ with
  | bool =>
    rw [IsSoundFor.iff_obs, genZero]; walk [genBool.sound_complete.sound.obs]
    apply Typed.lit_bool
  | int =>
    rw [IsSoundFor.iff_obs, genZero]; walk [genInt.sound_complete.sound.obs]
    apply Typed.lit_int

/-! ## Soundness and completeness of `genExpr` -/

theorem genExpr.sound_complete : IsSoundAndComplete (genExpr Γ τ) (Typed Γ · τ) := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genZero.sound.obs, genBool.sound_complete.sound.obs,
      genInt.sound_complete.sound.obs, genNat.sound_complete.sound.obs,
      genCType.sound_complete.sound.obs]
    all_goals first
      | (constructor <;> assumption)
      | exact varsWithType_sound ‹_›
  case complete =>
    intro e h
    induction h with
    | lit_bool b =>
      rw [genExpr.eq_def, SPMF.mem_support_iff_may]
      walk [genBool.sound_complete.complete.obs]; (split <;> simp)
    | lit_int i =>
      rw [genExpr.eq_def, SPMF.mem_support_iff_may]
      by_cases h : 0 ≤ i
      · have hb : ∃ x : ℕ, (x : ℤ) = i := ⟨i.toNat, by simp [Int.toNat_of_nonneg h]⟩
        walk [genNat.sound_complete.complete.obs]; (split <;> simp [hb])
      · have hc : ∃ a : ℕ, -1 + -(a : ℤ) = i := ⟨(-i - 1).toNat, by
          have : ((-i - 1).toNat : Int) = -i - 1 := Int.toNat_of_nonneg (by omega); omega⟩
        walk [genNat.sound_complete.complete.obs]; (split <;> simp [hc])
    | var i τ hlk =>
      have hmem := varsWithType_complete hlk
      cases τ <;>
        (rw [genExpr.eq_def, SPMF.mem_support_iff_may]
         walk; simp [List.ne_nil_of_mem hmem, hmem])
    | ite c t e τ _ _ _ ihc iht ihe =>
      cases τ <;>
        (rw [genExpr.eq_def, SPMF.mem_support_iff_may]
         walk; (split <;> simp [ihc, iht, ihe]))
    | and a b _ _ iha ihb =>
      rw [genExpr.eq_def, SPMF.mem_support_iff_may]
      walk; (split <;> simp [iha, ihb])
    | or a b _ _ iha ihb =>
      rw [genExpr.eq_def, SPMF.mem_support_iff_may]
      walk; (split <;> simp [iha, ihb])
    | not a _ ih =>
      rw [genExpr.eq_def, SPMF.mem_support_iff_may]
      walk; (split <;> simp [ih])
    | neg a _ ih =>
      rw [genExpr.eq_def, SPMF.mem_support_iff_may]
      walk; (split <;> simp [ih])
    | less a b _ _ iha ihb =>
      rw [genExpr.eq_def, SPMF.mem_support_iff_may]
      walk; (split <;> simp [iha, ihb])
    | lessEq a b _ _ iha ihb =>
      rw [genExpr.eq_def, SPMF.mem_support_iff_may]
      walk; (split <;> simp [iha, ihb])
    | eq a b τ' _ _ iha ihb =>
      rw [genExpr.eq_def, SPMF.mem_support_iff_may]
      cases τ' <;> (walk; (split <;> simp_all))
    | add a b _ _ iha ihb =>
      rw [genExpr.eq_def, SPMF.mem_support_iff_may]
      walk; (split <;> simp [iha, ihb])
    | sub a b _ _ iha ihb =>
      rw [genExpr.eq_def, SPMF.mem_support_iff_may]
      walk; (split <;> simp [iha, ihb])
    | mul a b _ _ iha ihb =>
      rw [genExpr.eq_def, SPMF.mem_support_iff_may]
      walk; (split <;> simp [iha, ihb])

end CedarLite
