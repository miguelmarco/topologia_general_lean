import .metricos
import tactic

noncomputable theory

open metricos
open metricos.espacio_metrico



lemma ejercicio_1_2_1_sol (A B : set ℝ ) (h : abierto A) : abierto { (x + y) | (x ∈ A) (y ∈ B) } := 
begin
  intros z hz,
  simp at hz,
  cases hz with x hx,
  cases hx with hx hy,
  cases hy with y hy,
  cases hy with hy hz,
  specialize h x hx,
  cases h with r hr,
  cases hr with hrpos hbolr,
  use r,
  split, exact hrpos,
  intros t ht, 
  simp [d,← hz] at ht,
  simp,
  use t - y,
  split,
  {
    apply hbolr,
    simp [d],
    ring_nf at ⊢ ht,
    exact ht,
  },
  use y,
  split,
  {
    exact hy,
  },
  {
    ring_nf,
  }
end

lemma ejercicio_1_2_2_sol (a b : ℝ ) (h : a < b) : abierto {x | a < x ∧ x < b } :=
begin
  intro x,
  intro hx,
  cases hx with hxa hxb,
  let r := min (b - x) (x - a),
  use r,
  split,
  {
    simp,
    tauto,
  },
  {
    intros y hy,
    simp [d] at hy,
    cases hy with hy1 hy2,
    have hxy := le_abs_self (x - y),
    have hyx := le_abs_self (y - x),
    have hs := abs_sub_comm x y,
    split,
    { 
      linarith,
    },
    {
      linarith,
    },
  }
end

lemma ejercicio_1_2_3_sol (X : Type) (S : set X) [espacio_metrico X] : 
 abierto {x : X | entorno x S } :=
begin
  intros x hx,
  cases hx with r hr,
  cases hr with hrpos hrbol,
  use r,
  split, exact hrpos,
  intros y hy,
  simp at hy,
  use (r - d x y),
  split,
  {
    linarith,
  },
  {
    intros z hz,
    apply hrbol,
    simp at *,
    have htri := d4 x y z,
    linarith,
  }
end