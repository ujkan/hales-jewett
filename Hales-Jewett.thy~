theory "Hales-Jewett"
  imports Main "HOL-Library.FuncSet"
begin

type_synonym 'a vector = "(nat \<Rightarrow> 'a)"

fun nat_upto :: "nat \<Rightarrow> nat list"
  where
    "nat_upto 0 = []"
  | "nat_upto (Suc x) = nat_upto x @ [x]"

lemma nat_upto_len: "length (nat_upto n) = n"
  apply (induction n)
  apply auto
  done

lemma nat_upto_elems: "\<forall>x \<in> set (nat_upto n). x \<ge> 0 \<and> x < n"
  apply (induction n)
   apply auto
  done

lemma A: "set (nat_upto n) \<subseteq> {i . i < n}"
  apply (induction n)
  apply auto
  done


lemma B: "{i . i < n} \<subseteq> set (nat_upto n)"
  apply (induction n)
   apply auto
proof-
  fix n x
  assume assms: "{i. i<n} \<subseteq> set (nat_upto n)" "x \<notin> set (nat_upto n)" "x < Suc n"
  then have "x \<notin> {i. i<n}" by blast
  then have "x \<ge> n" by simp
  then show "x = n" using assms(3) by auto
qed

lemma nat_upto_set: "set (nat_upto n) = {i. i < n}"
  using A B by blast




definition cube :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "cube n t \<equiv> {..<(n::nat)} \<rightarrow>\<^sub>E {..<(t::nat)}"
term Pi
(*
  {..<n} \<longrightarrow>\<^sub>E {..<t} 
  {(x_1,...,x_n) | x_i \<in> {0,...,t-1}} = {0,...,t-1}^n
*)


lemma "\<forall>xs \<in> set (cube n t). length xs = n"
  apply (induction n)
  apply auto
  done

lemma "\<forall>xs \<in> set (cube n t). \<forall>x \<in> set xs. x < t"
  apply (induction n)
   apply (auto simp: nat_upto_elems)
  done

lemma "length (cube n t) \<equiv> t^n"
  apply (induction n)
   apply (auto)
  sorry


  
  

end