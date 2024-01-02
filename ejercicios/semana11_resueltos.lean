import ..sucesiones
import tactic

open topologicos topologicos.espacio_topologico

/-
## Ejercicio 4.4.7
Sea (X, T ) un e.t. Hausdorff y sea S ⊂ X una sucesión convergente. 
Demuestra que Agl S = Lim S y por tanto, toda subsucesión convergente
de S tiene el mismo límite que S.
-/
lemma ejer_4_4_7_sol (X : Type) [espacio_topologico X] (hX : hausdorff X) 
(s : ℕ → X) (x : X) (hx : x ∈ Lim s) : Agl s = Lim s :=
begin
  apply doble_contenido,
  {
    intros y hy,
    by_contradiction hn,
    have haux : x ≠ y,
    {
      intro hxy,
      apply hn,
      rw hxy at hx,
      exact hx,
    },
    specialize hX x y haux,
    rcases hX with ⟨U,⟨V,⟨hU,⟨hV,⟨hxU,⟨hyV,hUV⟩⟩⟩⟩⟩⟩,
    simp [Agl,caracterizacion_aglomeracion_abiertos] at hy,
    specialize hy V hV hyV,
    simp [Lim,caracterizacion_limite_abiertos] at hx,
    specialize hx U hU hxU,
    cases hx with n₀ hn₀,
    specialize hy n₀,
    cases hy with n hn,
    cases hn with hn1 hn2,
    specialize hn₀ n hn1,
    have hsn : s n ∈ U ∩ V := ⟨hn₀,hn2⟩,
    rw hUV at hsn,
    apply hsn,
  },
  {
    apply limite_en_aglomeracion,
  }
end


/-
## Ejercicio 4.4.10
Sea X un conjunto infinito no numerable. Consideremos en
él las topologías (X, Tcn) (topología conumerable) y (X, Td) 
(topología discreta).
Demuestra que sólo las sucesiones casiconstantes en X tienen límite
-/
lemma ejer_4_4_10_sol (X : Type) (x : X) (s : ℕ → X) (hs : x ∈ @Lim X (discreta X) s) : 
  @casiconstante X (discreta X) s x:=
begin
  specialize hs {x} _,
  {
    use {x},
    simp,
  },
  cases hs with n0 hn0,
  let s' := λ n , s (n + n0 +1 ),
  use s',
  split,
  {
    intro n,
    simp [s'],
    simp at hn0,
    apply hn0,
    linarith,
  },
  use n0 + 1,
  intro n,
  simp [s'],
  ring_nf,
end

lemma ejer_4_4_10_2_sol (X : Type) (hX : ¬ countable X) (x : X) (s : ℕ → X) (hs : x ∈ @Lim X (conumerable X) s) : 
  @casiconstante X (conumerable X) s x:=
begin
  unfold casiconstante,
  by_contradiction hneg,
  simp [constante,truncada] at hneg,
  specialize hneg (λ n, x) _,
  {
    simp only [forall_const],
  },
  choose t ht using hneg,
  let s' : (ℕ → X) := λ n, s (t n + n),
  let U := (set.range s')ᶜ ,
  simp only [Lim, caracterizacion_limite_abiertos, abierto_def, abiertos_conumerable_def, set.union_singleton, set.mem_insert_iff,
  set.mem_set_of_eq, gt_iff_lt, forall_eq_or_imp, set.mem_empty_eq, is_empty.forall_iff, true_and] at hs,
  specialize hs U _ _,
  {
    simp only [compl_compl, U],
    exact set.countable_range s',
  },
  {
    simp only [not_exists, set.mem_range, U, set.mem_compl_eq],
    simp [s',ht],
    intros l hl,
    apply ht,
    rw hl, 
  },
  cases hs with n₀ hn₀,
  simp [U,s'] at hn₀,
  specialize hn₀ (t (n₀ + 1) + n₀ + 1) _,
  {
    linarith,
  },
  specialize hn₀ (n₀ + 1),
  apply hn₀,
  ring_nf,
end