theory Ex2_10_11
  imports Main
begin

(* Exercise 2.10: Binary trees *)
datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 => nat" where
  "nodes Tip = 1" |
  "nodes (Node l r) = 1 + nodes l + nodes r"

fun explode :: "nat => tree0 => tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = Node (explode n t) (explode n t)"

lemma explode_0: "nodes (explode 0 t) = nodes t"
  apply(auto)
  done

lemma explode_S: "nodes (explode (Suc n) t) = 2 * nodes (explode n t) + 1"
  apply(simp)
  done

lemma one_le_pow2: "1 <= (2::nat) ^ n"
  apply(induction n)
   apply(simp_all)
done

lemma explode_n: "nodes (explode n t) = 2 ^ n * nodes t + (2 ^ n - 1)"
  apply(induction n arbitrary: t)
  apply(auto simp: explode_S)
  done

(* Exercise 2.11: Polynomials *)
datatype exp = Var | Const nat | Add exp exp | Mul exp exp

fun eval :: "exp => nat => nat" where
  "eval Var x = x" |
  "eval (Const n) x = n" |
  "eval (Add e1 e2) x = eval e1 x + eval e2 x" |
  "eval (Mul e1 e2) x = eval e1 x * eval e2 x"

type_synonym Poly = "nat list"

fun evalp_with_order :: "Poly => nat => nat => nat" where
  "evalp_with_order [] x n = 0" |
  "evalp_with_order (a # xs) x n = a * (x ^ n) + evalp_with_order xs x (Suc n)"

definition evalp :: "Poly => nat => nat" where
  "evalp l x = evalp_with_order l x 0"

fun poly_add :: "Poly => Poly => Poly" where
  "poly_add [] q = q" |
  "poly_add p [] = p" |
  "poly_add (a # p') (b # q') = (a + b) # poly_add p' q'"

fun poly_scalar_mul :: "nat => Poly => Poly" where
  "poly_scalar_mul a [] = []" |
  "poly_scalar_mul a (b # p') = (a * b) # poly_scalar_mul a p'"

definition poly_shift :: "Poly => Poly" where
  "poly_shift p = 0 # p"

fun poly_mul :: "Poly => Poly => Poly" where
  "poly_mul [] q = []" |
  "poly_mul (a # p') q = poly_add (poly_scalar_mul a q) (poly_shift (poly_mul p' q))"

fun exp_to_poly :: "exp => Poly" where
  "exp_to_poly Var = [0, 1]" |
  "exp_to_poly (Const n) = [n]" |
  "exp_to_poly (Add e1 e2) = poly_add (exp_to_poly e1) (exp_to_poly e2)" |
  "exp_to_poly (Mul e1 e2) = poly_mul (exp_to_poly e1) (exp_to_poly e2)"

definition coeffs :: "exp => nat list" where
  "coeffs e = exp_to_poly e"

lemma evalp_of_var: "evalp [0, 1] x = x"
  apply(auto simp: evalp_def)
  done

lemma evalp_of_const: "evalp [n] x = n"
  apply(auto simp: evalp_def)
  done

lemma evalp_with_order_add: "evalp_with_order (poly_add p q) x n = 
  evalp_with_order p x n + evalp_with_order q x n"
  apply(induction p arbitrary: q n)
   apply(auto split: list.split)
  apply(case_tac q)
   apply(auto)
  apply(simp add: algebra_simps)
  done

lemma evalp_add: "evalp (poly_add p q) x = evalp p x + evalp q x"
  apply(auto simp: evalp_def evalp_with_order_add)
  done

lemma evalp_with_order_scalar_mul: "evalp_with_order (poly_scalar_mul a p) x n = 
  a * evalp_with_order p x n"
  apply(induction p arbitrary: n)
   apply(auto)
  apply(simp add: algebra_simps)
  done

lemma evalp_with_order_shift: "evalp_with_order (poly_shift p) x n = 
  evalp_with_order p x (Suc n)"
  apply(auto simp: poly_shift_def)
  done

lemma evalp_with_order_succ: "evalp_with_order p x (Suc n) = x * evalp_with_order p x n"
  apply(induction p arbitrary: n)
  apply(simp_all add: algebra_simps power_commutes)
  done

lemma evalp_with_order_scale: "evalp_with_order q x n = x ^ n * evalp_with_order q x 0"
  apply(induction n)
   apply(simp)
  apply(simp add: evalp_with_order_succ)
  done


lemma evalp_with_order_mul: "evalp_with_order (poly_mul p q) x n = 
  evalp_with_order p x n * evalp_with_order q x 0"
  apply(induction p arbitrary: q n)
   apply(simp)
  apply(simp add: evalp_with_order_add evalp_with_order_scalar_mul evalp_with_order_shift)
  apply(subst evalp_with_order_scale)
  apply(simp add: algebra_simps power_add)
  done

lemma evalp_mul: "evalp (poly_mul p q) x = evalp p x * evalp q x"
  apply(auto simp: evalp_def evalp_with_order_mul)
  done


theorem eval_correct: "eval e x = evalp (coeffs e) x"
  apply(induction e)
     apply(simp add: coeffs_def evalp_def)
     apply(simp)
    apply(simp add: coeffs_def evalp_def)
   apply(simp add: coeffs_def evalp_add)
     apply(simp add: coeffs_def evalp_mul)
  done
end
