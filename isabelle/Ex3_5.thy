theory Ex3_5
  imports Main
begin

(* Exercise 3.5: Context-free grammars for balanced parentheses *)

datatype alpha = a | b

(* Grammar S: S \<rightarrow> \<epsilon> | aSb | SS *)
inductive S :: "alpha list \<Rightarrow> bool" where
  S_eps:  "S []"
| S_aSb:  "S w \<Longrightarrow> S ([a] @ w @ [b])"
| S_SS:   "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1 @ w2)"

(* Grammar T: T \<rightarrow> \<epsilon> | TaTb *)
inductive T :: "alpha list \<Rightarrow> bool" where
  T_eps:  "T []"
| T_TaTb: "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ [a] @ w2 @ [b])"

(* ===== Direction 1: T w \<Longrightarrow> S w ===== *)

(* Helper: S is closed under the TaTb production *)
lemma S_from_TaTb: "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1 @ [a] @ w2 @ [b])"
  apply(rule S_SS)
  apply(simp)
  apply(rule S_aSb)
  apply(auto)
done

theorem T_implies_S: "T w \<Longrightarrow> S w"
  apply(induction rule: T.induct)
  apply(rule S_eps)
  apply(rule S_from_TaTb)
  apply(auto)
done

(* ===== Direction 2: S w \<Longrightarrow> T w ===== *)

(* Key lemma: T is closed under concatenation *)
lemma T_concat: "T w2 \<Longrightarrow> T w1 \<Longrightarrow> T (w1 @ w2)"
  apply(induction arbitrary: w1 rule: T.induct)
   apply(simp)
  apply(metis T_TaTb append_assoc)
done

theorem S_implies_T: "S w \<Longrightarrow> T w"
  apply(induction rule: S.induct)
  apply(rule T_eps)
  apply(subgoal_tac "T ([] @ [a] @ w @ [b])")
  apply(simp)
  apply(rule T_TaTb)
  apply(rule T_eps)
  apply(auto)
  apply(rule T_concat)
  apply(auto)
 done

(* ===== Equivalence ===== *)

theorem S_iff_T: "S w \<longleftrightarrow> T w"
  apply(auto intro: S_implies_T T_implies_S)
done

end
