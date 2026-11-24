import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1316

open PEqualNP.CircuitLowerBounds

lemma getD_snoc_eq {α : Type*} (w : List α) (b : α) (d : α) :
    (w ++ [b]).getD w.length d = b := by
  simp [List.getD]

lemma gate_degree_le_two (B : ℕ) (d : List ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hd : ∀ i, d.getD i 0 ≤ B) : g.lineDegree d ≤ 2 * B := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and =>
    simp only [Gate.lineDegree, if_pos rfl]
    cases ins with
    | nil => simp
    | cons a t =>
      cases t with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ite_true, ite_false]
        have ha := hd a
        omega
      | cons b u =>
        cases u with
        | nil =>
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ite_true, ite_false]
          have ha := hd a
          have hb := hd b
          omega
        | cons c _ => simp at hg
  | or =>
    simp only [Gate.lineDegree, if_neg (show GateOp.or ≠ GateOp.and from by intro h; cases h)]
    cases ins with
    | nil => simp
    | cons a t =>
      cases t with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, ite_true, ite_false]
        have ha := hd a
        omega
      | cons b u =>
        cases u with
        | nil =>
          simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, ite_true, ite_false]
          have ha := hd a
          have hb := hd b
          omega
        | cons c _ => simp at hg
  | not => simp at hg
  | mod m => simp at hg
  | maj => simp at hg

lemma fold_degree_bound (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ (B : ℕ) (d : List ℕ), (∀ i, d.getD i 0 ≤ B) →
      ∀ i, (gs.foldl (fun d g => d ++ [g.lineDegree d]) d).getD i 0 ≤ B * 2 ^ gs.length := by
  induction gs with
  | nil => intro B d hd i; simpa using hd i
  | cons g gs ih =>
    intro B d hd i
    have hgate : g.lineDegree d ≤ 2 * B := gate_degree_le_two B d g (hg g (by simp)) hd
    have hnew : ∀ j, (d ++ [g.lineDegree d]).getD j 0 ≤ 2 * B := by
      intro j
      by_cases hj : j < d.length
      · rw [List.getD_append _ _ _ _ hj]
        exact le_trans (hd j) (by omega)
      · by_cases heq : j = d.length
        · subst heq
          rw [getD_snoc_eq]
          exact hgate
        · rw [List.getD_eq_default _ _ (by simp; omega)]
          omega
    have hrec := ih (fun h hh => hg h (by simp [hh])) (2 * B) (d ++ [g.lineDegree d]) hnew i
    simpa [List.foldl_cons, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hrec

end PEqualNP.Outside.L_meta_1316

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1316 : ∀ (n : ℕ) (marked : Finset ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → C.lineDeg n marked ≤ 2 ^ C.size := by
  intro n marked C hmono
  let d := (List.range n).map fun i => if i ∈ marked then 1 else 0
  have hd : ∀ i, d.getD i 0 ≤ 1 := by
    intro i
    by_cases hi : i < n
    · by_cases hm : i ∈ marked
      · simp [d, List.getD_eq_getElem?_getD, List.getElem?_map, hi, hm]
      · simp [d, List.getD_eq_getElem?_getD, List.getElem?_map, hi, hm]
    · simp [d, List.getD_eq_getElem?_getD, hi]
  have h := PEqualNP.Outside.L_meta_1316.fold_degree_bound C.gates hmono 1 d hd C.output
  simpa [Circuit.lineDeg, Circuit.lineDegrees, Circuit.size, d] using h
