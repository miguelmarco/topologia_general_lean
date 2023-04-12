import data.real.basic
import tactic

example (a b : ℝ ) (h : a^2 = 3) : b * a ^2 = b * 3 :=
begin
  rw h,
end

example (a b : ℕ  ) (h : a^2 = 3) : b * a ^2 = 3  * b:=
begin
  rw h,
  rw mul_comm,
end

example ( a b c : ℕ ) : a * c + b * c  = (b + a) * c :=
begin
  rw ← add_mul,
  rw add_comm,
end

example (a b c : ℤ ) : a * b + c *a = a * (b + c) :=
begin
  ring,
end


