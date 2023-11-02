import .topologicos
import .cerrados
import .subconjuntos
import tactic


open set
open topologicos
open topologicos.espacio_topologico

variables {X : Type} [espacio_topologico X] {A : set X} 


instance topologia_inducida {X : Type} [espacio_topologico X] (A : set X)  : espacio_topologico A := 
{ abiertos := {( (U ↓∩ A) )  | U ∈ (abiertos : set (set X))},
  abierto_total := 
  begin
    use univ,
    simp only [and_true, eq_self_iff_true, restringe_total],
    exact abierto_total,
  end,
  abierto_vacio := 
  begin
    use ∅,
    simp only [and_true, eq_self_iff_true, restringe_vacio],
    exact abierto_vacio,
  end,
  abierto_union := 
  begin
    intros F hF,
    use ⋃₀ {U : set X | abierto U ∧ (U ↓∩  A) ∈ F},
    split,
    {
      apply abierto_union,
      intros U hU,
      exact hU.1,
    },
    {
      ext x,
      simp only [restringe_union_familia],
      split,
      {
        intro hx,
        cases hx with U hU,
        cases hU with hUF hxU,
        cases hUF with V hV,
        cases hV with hV hVU,
        cases hV with hVab hVF,
        use (V ↓∩ A),
        split, exact hVF,
        rw hVU,
        exact hxU,
      },
      {
        intro hx,
        cases hx with U hU,
        cases hU with hUF hxU,
        specialize hF hUF,
        cases hF with V hV,
        cases hV with hVab hVU,
        use (V ↓∩ A),
        split,
        {
          use V,
          simp [hVab, hVU, hUF],
        },
        {
          rw hVU,
          exact hxU,
        },
      },
    },
  end,
  abierto_interseccion := 
  begin
    intros U V hU hV,
    simp only [exists_prop, mem_set_of_eq] at *,
    cases hU with UX hUX,
    cases hUX with hUXab hUXU,
    cases hV with VX hVX,
    cases hVX with hVXab hVXV,
    use UX ∩ VX,
    split,
    {
      apply abierto_interseccion,
      assumption,
      assumption,
    },
    {
      simp only [restringe_interseccion, hUXU, hVXV],
    },
  end,
  }


def  TA (A : set X)  := topologia_inducida A


@[simp]
lemma abierto_inducido_sii (C : set A) : abierto C ↔ ∃ U  ∈ (abiertos : set (set X)),   (U ↓∩ A) = C:=
begin 
  refl,
end




lemma cerrado_inducido_sii (C : set A) : cerrado C ↔ ∃ U  ∈ (cerrados : set (set X)),   (U ↓∩ A) = C :=
begin
  simp only [cerrado, abierto_inducido_sii],
  split,
  {
    intro h,
    cases h with U hU,
    cases hU with hUab hUC,
    use Uᶜ,
    simp only [hUab,hUC, cerrados_def, compl_compl, abierto_def, restringe_complementario, eq_self_iff_true, and_true],
  },
  {
    simp only [cerrados_def, abierto_def, exists_prop, forall_exists_index, and_imp],
    intros U hUab hUC,
    use Uᶜ,
    simp only [hUab, hUC, restringe_complementario, eq_self_iff_true, and_self],
  }
end

def ι : A → X := λ x, x.val



lemma inclusion_continua : continua (ι : A → X ) :=
begin
  intros U hU, 
  use U,
  simp only [hU, true_and],
  refl,
end

def extiende (X : Type)  (A : set X) : set A →  set X := coe

example (X : Type) [TX : espacio_topologico X] (A : set X) (B : set A) : extiende X A  '' ((extiende ↥A B) '' (@abiertos ↥B (topologia_inducida B))) = (extiende X B) ''  @abiertos (B : set X) (topologia_inducida (B : set X)) :=
begin
  ext U,
  simp only [extiende, mem_image, abiertos_imagen_inversa_def, restringe_coe, exists_prop, mem_set_of_eq, exists_exists_and_eq_and,
  restringe_eleva, eleva_interseccion, interseccion_elevacion],
end


def aplicacion_restriccion_imagen {X Y : Type} (f : X → Y ) (A : set Y) (hFA : range f ⊆ A ) : X → A :=
begin
  intro x,
  fconstructor,
  {
    exact f x,
  },
  {
    apply hFA,
    use x,
  }
end


notation f `|_` hFA  := aplicacion_restriccion_imagen f _ hFA 



lemma continua_restriccion_imagen (X Y : Type) [espacio_topologico X] [espacio_topologico Y]
      (A : set Y) (f : X → Y ) (hFA : range f ⊆ A )
      (hcont : continua (f |_  hFA) ) :
      continua f 
      :=
begin
  intros U hU,
  have haux : f ⁻¹' U = (f |_ hFA) ⁻¹' (U ↓∩ A),
  {
    refl,
  },
  {
    rw haux,
    apply hcont,
    use U,
    simp,
    exact hU,
  },
end

lemma continua_a_trozos (X Y : Type) [espacio_topologico X] [espacio_topologico Y] (A B : set X) (f : X → Y)
(hAB : A ∪ B = univ ) (hA : abierto A) (hB : abierto B) (hfA : continua (f ∘ ι : A → Y)) (hfB : continua (f ∘ ι : B → Y)) :
continua f :=
begin
  intros U hU,
  specialize hfA U hU,
  specialize hfB U hU,
  have hUA : (f ∘ ι ⁻¹' U) = ((f ⁻¹' U) ↓∩ A) := rfl,
  have hUB : (f ∘ ι ⁻¹' U) = ((f ⁻¹' U) ↓∩ B) := rfl,
  simp only [hUA, abiertos_imagen_inversa_def, restringe_coe, exists_prop, mem_set_of_eq, restringe_igual] at hfA,
  simp only [hUB, abiertos_imagen_inversa_def, restringe_coe, exists_prop, mem_set_of_eq, restringe_igual] at hfB,
  clear hUA,
  clear hUB,
  cases hfA with UA hUA,
  cases hUA with hUAab hfUA,
  cases hfB with UB hUB,
  cases hUB with hUBab hfUB,
  rw ←inter_univ (f ⁻¹' U),
  rw ← hAB,
  rw inter_distrib_left,
  rw ← hfUA,
  rw ← hfUB,
  apply abierto_union_2,
  repeat {
    apply abierto_interseccion,
    assumption,
    assumption
  },
end

lemma  lema1 (n m : ℕ ) (h : n < m) (hn : 0 < n) (hm : 0 < m) : 1 / ((n: ℝ) * (n + 1)) ≤  1 / (n : ℝ ) - 1 / (m : ℝ ) :=
begin
  have haux : 1 / ((n : ℝ )* (n + 1)) =  1 / n - 1 / (n + 1),
  {
    rw div_sub_div,
    norm_num,
    repeat {norm_cast, linarith},
  },
  rw haux,
  rw sub_le_sub_iff_left,
  apply div_le_div,
  repeat {norm_num,},
  repeat {norm_cast, linarith},
end

lemma  lema2 (n m : ℕ ) (h : m < n) (hn : 0 < n) (hm : 0 < m) : 1 / ((n: ℝ) * (n + 1)) ≤  1 / (m : ℝ ) - 1 / (n : ℝ ) :=
begin
  have haux :  (1 / ((n : ℝ )*(n+1))) = 1 / n - 1 / (n + 1),
  {
    rw div_sub_div,
    rw div_eq_div_iff,
    ring_nf,
      repeat {
        norm_cast,
        simp only [nat.mul_eq_zero, nat.succ_ne_zero, or_false],
        linarith,
      },
      repeat {
        norm_cast,
        linarith,
      },
  },
  rw haux,
  rw [div_sub_div],
  rw [div_sub_div],
  apply div_le_div,
  any_goals {norm_cast, linarith,},
  {
    rw le_sub_iff_add_le,
    norm_cast,
    linarith,
  },
  {
    rw sub_le_sub_iff,
    norm_cast,
    linarith,
  },
  {
    norm_cast,
    apply mul_pos,
    exact hm,
    exact hn,
  },
  {
    apply mul_le_mul,
    repeat {norm_cast, linarith,},
  },
end

def Y := { (1 / ((↑n : ℝ) + 1)) | (n : ℕ ) }

example : topologia_inducida Y = discreta Y :=
begin
  rw ejer_2_1_3,
  intro x,
  cases x with x hx,
  cases hx with n hn,
  use metricos.bola x ( 1 / ((n + 1) * (n + 2))),
  split,
  {
    apply metricos.bola_abierta,
    rw gt_iff_lt,
    rw lt_div_iff,
    norm_num,
    apply mul_pos,
    repeat {
      norm_cast,
      linarith,
    },
  },
  {
    ext y,
    split,
    {
      intro h,
      cases y with y hy,
      cases hy with m hm,
      simp only [metricos.espacio_metrico.d, abs_lt, ←hn, ←hm, pert_restringe_def, subtype.coe_mk,
  metricos.bola_carac, neg_lt_sub_iff_lt_add, sub_lt_iff_lt_add] at h,
      cases h with h1 h2,
      by_cases hcas : n ≤ m,
      {
        rw le_iff_lt_or_eq at hcas,
        cases hcas,
        {
          have haux := lema1 (n + 1) (m + 1) _  _  _,          
          {
            norm_num at haux,
            ring_nf at *,
            linarith, 
          },
          repeat {linarith},
        },
        {
          simp only [set.mem_singleton_iff, subtype.mk_eq_mk],
          cases hcas,
          rw hm at hn,
          exact hn,
        }
      },
      {
        rw  not_le at hcas,
        have haux2 := lema2 (n + 1) (m + 1) _  _ _ ,
        norm_cast at *,
        ring_nf at *,
        repeat {linarith,},
      },
    },
    {
      intro hy,
      cases hy,
      simp only [metricos.bola_carac, mul_inv_rev,  metricos.distancia_cero, pert_restringe_def, subtype.coe_mk],
      apply div_pos,
        norm_num,
      norm_cast,
      apply mul_pos,
      repeat {linarith,},
    },
  },
 end