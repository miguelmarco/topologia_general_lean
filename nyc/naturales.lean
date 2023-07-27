import tactic

open nat finset
open_locale big_operators

/-
# Números naturales

Vamos a hacer algunos ejercicios sobre propiedades de los naturales.
La principal herramienta que vamos a usar es la inducción. Para ello aplicaremos la 
táctica `induction`.

Usaremos la notación de sumatorios. Por ejemplo, la expresión `∑ i in range (n), i^2`
representa la suma de los cuadrados de los números `0,1,..,(n-1)`. De hecho, puede aplicarse
a cualquier `finset` (de momento, quedémonos con que es otra noción de conjunto finito).
La función `range` devuelve el finset correspondiente al número que se le pase

Lo que vamos a usar fundamentalmente es un lema llamado `sum_range_succ` que permite separar
el último término de una suma. Otros resultados que pueden ser útiles son `sum_range_one` y 
`sum_range_zero`. Formalmente, estos lemas dicen:

`sum_range_succ : ∀ (f : ℕ → ?M_1) (n : ℕ), ∑ (x : ℕ) in range (n + 1), f x = ∑ (x : ℕ) in range n, f x + f n`
`sum_range_one : ∀ (f : ℕ → ?M_1), ∑ (k : ℕ) in range 1, f k = f 0`
`sum_range_zero : ∀ (f : ℕ → ?M_1), ∑ (k : ℕ) in range 0, f k = 0`

Tamién es útil, cuando queremos demostrar igualdades que se obtienen símplemente
manipulando sumas y productos en un anillo, usar la táctica `ring`.
-/

@[simp]
lemma succ_eq_mas1 (n : ℕ ): n.succ = n + 1 := rfl

-- Demostremos la fórmula para la suma de los cubos de los primeros números
lemma ejer1 ( n : ℕ ) : (∑ i in range (n + 1), i ^3) * 4  = ((n * (n + 1)  ))^2 :=
begin
  induction n with n hind,  -- aplicamos inducción sobre n
  {                         -- caso n = 0
    refl,                   -- se cumple por definición
  },
  {                         -- caso n + 1, suponiendo cierto el caso n
    rw sum_range_succ,      -- separamos el último sumando del sumatorio
    simp only [succ_eq_mas1],-- reescribimos usando operaciones en lugar de siguientes
    rw add_mul,             -- aplicamos la distributiva, para tener exactamente
                            -- la misma expresión que en la hipótesis de inducción 
    rw hind,                -- aplicamos la hipótesis de inducción
    ring,                   -- y operamos en la expresión
  }
end


-- Ahora podemos usar el anterior ejercicio para despejar el `4`
lemma ejer1' ( n : ℕ ) : (∑ i in range (n.succ), i ^3)  = (n *(n + 1)) ^ 2 / 4 :=
begin
  have h1 := ejer1 n,
  have h4m : 4 > 0, linarith,
  rw ← h1,
  simp [mul_div_cancel],
end

-- Dar esta vuelta puede parecer distinto a lo que haríamos normalmente con papel
-- y lápiz. Esto es porque nos estamos restringiendo a operaciones entre números
-- naturales, y en este contexto la divión `/` es la división con resto.

-- Si quisiéramos hacerlo en el espíritu usual de las matemáticas, debemos llevarnos
-- el problema al contexto de los racionales

lemma ejer1_racional (n : ℕ ) : (∑ i in range (n.succ), (i:ℚ)^3)  = (n *(n + 1)) ^ 2 / 4 :=
begin
  induction n with n hind,
  {
    simp,
  },
  {
    rw sum_range_succ,      -- separar el último término de la suma
    rw hind,                -- aplicar la hipótesis de inducción
    simp,                   -- convertimos los sucesores en sumas 
    ring,                   -- para poder aplicar la simplificación de expresiones en un anillo
  }
end


example ( n : ℕ ) : 13 ∣ 4 ^(2 * n  + 1) + 3 ^( n + 2) :=
begin
  induction n with n hind,
  {
    ring_nf,                -- `ring_nf` intenta poner las expresiones en anillos en una forma normal
  },
  {
    cases hind with a ha,   -- la hipótesis de divisibilidad nos da la existencia de un factor
    use 3*a + 4 * 4 ^(2*n), -- y para demostrar la divisibilidad, hay que dar el factor correspondiente
    ring_exp at *,          -- como `ring_nf` no simplifica exponentes, tenemos que usar `ring_exp`
    linarith,               -- `linarith` intenta demostrar (in)ecuaciones lineales.
  }
end

lemma ejer3div (n : ℕ ) : 3 ∣  2 ^(2*n) + 5 :=
begin
  induction n with a ha,
  {
    norm_num,
  },
  {
    cases ha with k hk,
    ring_exp at *,
    use k + 2^(a*2),
    ring_nf at *,
    linarith,
  }
end

example (n : ℕ ) : 9 ∣  (-1 : ℤ ) + 2 ^(2*n) + 15*n  :=
begin
  induction n with n hind,
  {
    norm_num,
  },
  {
    change n.succ with n+1,
    ring_exp at *,
    cases hind with a ha,
    have haux := ejer3div n,
    cases haux with k hk,
    use a + k,
    simp,
    ring_nf at *,
    linarith,
  }
end

-- # Ejercicios

-- demuestra que el producto de dos números consecutivos es par
-- puedes usar el hecho de que todo natural es par o impar (`nat.even_or_odd`)
-- también se puede hacer por inducción

lemma prod_consec_par (n : ℕ )  :  2 ∣ (n * (n + 1)) :=
begin
  sorry,
end

/-
Demostrar la fórmula para la suma de los primeros números naturales.
Primero como igualdad en los racionales:

-/

lemma suma_primeros_en_Q ( n : ℕ ) : (∑ i in range n, i  : ℚ ) = n * (n - 1) / 2 :=
begin
  sorry,
end

/-
Ahora como igualdad en los naturales, igual es más fácil hacerlo primero quitando
denominadores.
-/

lemma suma_primeros_en_N_2 ( n : ℕ ) : 2 * (∑ i in range n, i) = n * (n - 1) :=
begin
  sorry,
end

/-
y luego usar lo anterior para obtener la fórmula con fracciones
-/

lemma suma_primeros_en_N (n : ℕ ) : (∑ i in range n, i) = n * (n - 1) / 2 :=
begin
  sorry,
end


/-
# Ejemplos con Fibonaci

Demostremos ahora algunas propiedades de la sucesión de Fibonaci. Empezamos definiendola
recursivamente:
-/
def fib :  ℕ → ℕ
| 0 := 0
| 1 := 1
| (n + 2) := fib n + fib (n +1)


/-
Veamos que dos términos consecutivos son coprimos
-/
lemma cons_fib_coprimos (n : ℕ ) : gcd (fib n) (fib (n + 1)) = 1 :=
begin
  induction n with n h,
  {
    simp [fib],
  },
  {
    cases n,
    {
      simp [fib],
    },
    {
      simp  [fib] at *,
      rw nat.gcd_comm,
      assumption,
    }
  },
end

/-
Marcamos los siguientes resultados como `@[simp]` para que la táctica `simp` los use.
-/

@[simp]
lemma fib0 : fib 0 = 0 :=  eq.refl (fib 0)

@[simp]
lemma fib1 : fib 1 = 1 := eq.refl (fib 1)

@[simp]
lemma fib2 : fib 2 = 1 := eq.refl (fib 2)

@[simp]
lemma fib_suma (m n : ℕ) :
  fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) :=
begin
  induction n with n ih generalizing m,
   {
     simp,
   },
  {
    specialize ih (m+1),
    change n.succ with n +1,
    ring_nf at *,
    rw ih,
    simp only [fib],
    ring,
  },
end


/-
Aquí podemos ver un ejemplo de usar la táctica `calc`
Veamos que la función de fibonacci respeta divisibilidad
(notar que el símbolo de dividir `∣` es distinto del que
se usa para definir conjuntos: `\|` frente a `|` )
-/
lemma fib_div (n r : ℕ ) : fib n ∣ fib (n * r)  :=
begin
  by_cases h1 : n < 1,
  {
    simp only [gt_iff_lt, nat.lt_one_iff] at h1,
    simp only [fib0, zero_mul, h1, dvd_zero],
  },
  rw not_lt at h1,
  induction r with r ih,
  {
    simp,
  },
  {
    have hn : n * r.succ = n * r + n,
    {
       ring,
    },
    cases ih with a1 ha1,
    use a1 * fib(n - 1) + fib(n * r + 1),
    calc
      fib (n * r.succ) = fib ( n * (r + 1))                            :by {refl,}
      ...              = fib ( n * r + n )                             :by {ring,}
      ...              = fib ( n * r + ((n - 1) + 1))                  :by {rw nat.sub_add_cancel h1,}
      ...              = fib ( n * r + (n - 1) + 1)                    :by {ring,}
      ...              = fib ( n * r) * fib (n - 1) + fib (n * r + 1) * fib (n) : by {rw fib_suma, rw nat.sub_add_cancel h1,}
      ...              = fib n * a1 * fib (n - 1) + fib (n * r + 1) * fib (n) : by {rw ha1,}
      ...              = fib n * (a1 * fib (n - 1) + fib (n * r + 1))  :by {ring,}
  }
end
