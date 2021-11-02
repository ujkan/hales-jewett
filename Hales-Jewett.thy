theory "Hales-Jewett"
  imports Main "HOL-Library.FuncSet" "HOL-Library.Disjoint_Sets"
begin

lemma "f \<in> A \<rightarrow>\<^sub>E B \<longleftrightarrow> ((\<forall>a. (a \<in> A \<longrightarrow> f a \<in> B) \<and> (a \<notin> A \<longrightarrow> f a = undefined)))" 
  by auto

definition cube :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "cube n t \<equiv> {..<(n::nat)} \<rightarrow>\<^sub>E {..<(t::nat)}"
term Pi\<^sub>E
(*
  {..<n} \<longrightarrow>\<^sub>E {..<t} 
  {(x_1,...,x_n) | x_i \<in> {0,...,t-1}} = {0,...,t-1}^n
*)

lemma aux: "\<exists>!f. f \<in> {} \<rightarrow>\<^sub>E A " 
proof -

  let ?f = "\<lambda>x. undefined"
  have "\<forall>x. (x \<in> {} \<longrightarrow> ?f x \<in> A) \<and> (x \<notin> {} \<longrightarrow> ?f x = undefined)" by simp
  then have *: "?f \<in> {} \<rightarrow>\<^sub>E A" by simp

  have "\<forall>g. g \<in> {} \<rightarrow>\<^sub>E A \<longrightarrow> g = ?f" by simp
  then show "\<exists>!f. f \<in> {} \<rightarrow>\<^sub>E A" using * by simp
qed

lemma "card ({} \<rightarrow>\<^sub>E A) = 1"
  using aux by auto

lemma "card ({..<n::nat} \<rightarrow>\<^sub>E {..<t::nat}) = t ^ n"
  apply (induction n)
   apply auto
  sorry
  
definition isLine :: "(nat \<Rightarrow> (nat \<Rightarrow> nat)) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "isLine L n t \<equiv> (L \<in> {..<t} \<rightarrow>\<^sub>E (cube n t) \<and> ((\<forall>j<n. (\<forall>x<t. \<forall>y<t. L x j =  L y j) \<or> (\<forall>s<t. L s j = s)) \<and> (\<exists>j < n. (\<forall>s < t. L s j = s))))"

lemma "isLine L n t \<Longrightarrow> L ` {..<t} \<subseteq> cube n t"
  unfolding cube_def isLine_def
  by auto

lemma "isLine L n t \<Longrightarrow> (\<forall>s<t. L s \<in> cube n t)"
  unfolding cube_def isLine_def
  by auto




definition isSubspace
  where "isSubspace f' k n t \<equiv> (\<exists>B f. disjoint (B ` {..k}) \<and> (\<Union>(B ` {..k})) = {..<n} \<and> (\<forall>i\<in>{..<k}. B i \<noteq> {}) \<and> f \<in> (B k) \<rightarrow>\<^sub>E {..<t} \<and> f' \<in> (cube k t) \<rightarrow>\<^sub>E (cube n t) \<and> (\<forall>y \<in> cube k t. (\<forall>i \<in> B k. f' y i = f i) \<and> (\<forall>j<k. \<forall>i \<in> B j. (f' y) i = y j)))"
(*
definition isSubspace
  where "isSubspace S k n t \<equiv> (\<exists>B f f'. disjoint (B ` {..k}) \<and> (\<Union>(B ` {..k})) = {..<n} \<and> (\<forall>i\<in>{..<k}. B i \<noteq> {}) \<and> f \<in> (B k) \<rightarrow>\<^sub>E {..<t} \<and> f' \<in> (cube k t) \<rightarrow>\<^sub>E (cube n t) \<and> f' = (\<lambda>y i. (if i \<in> B k then f i else y (SOME j. j < k \<and> i \<in> B j))) \<and> S = f' ` (cube k t))"

*)
lemma AUX: "cube n t \<subseteq> cube n (t + 1)"
  unfolding cube_def
  by (meson PiE_mono le_add1 lessThan_subset_iff)

definition classes
  where "classes n t \<equiv> (\<lambda>i. {x . x \<in> (cube n (t + 1)) \<and> {t} = x ` {(n - i)..<n} \<and> t \<notin> x ` {..<(n - i)}})"

lemma disjunct_classes: "n \<ge> 0 \<Longrightarrow> i < j \<and> j \<le> n \<Longrightarrow> classes n t i \<inter> classes n t j = {}"
proof (rule ccontr)
  assume assms: "n \<ge> 0" "i < j \<and> j \<le> n" "classes n t i \<inter> classes n t j \<noteq> {}"
  then have "\<exists>x.  x\<in> classes n t i \<inter> classes n t j" by blast
  then obtain x where x_def: "x \<in> classes n t i \<inter> classes n t j" by blast

  have "n - i > n - j" using assms(1, 2) by auto
  then have *: "n - i - 1 \<ge> n - j" by simp

  have "x ` {(n - j)..<n} = {t}" using x_def unfolding classes_def 
    by blast
  moreover have "{(n-j)..<n} \<noteq> {}" using assms 
    by (metis calculation empty_iff image_empty insertCI)
  ultimately have  "x (n - j) = t" by auto

  have "n - i - 1 < n" 
    by (metis Suc_diff_Suc assms(2) cancel_comm_monoid_add_class.diff_cancel diff_diff_eq diff_less_Suc less_imp_diff_less less_le_trans linorder_neqE_nat plus_1_eq_Suc zero_less_diff)
  then have "n - i - 1 \<in> {n - j..<n}" using * by simp
  then have A: "x (n-i-1) = t" using x_def unfolding classes_def by blast

  have "(n - i - 1 < n - i)" 
    by (meson assms(2) diff_less less_le_trans zero_less_diff zero_less_one)
  then have "n - i - 1 \<in> {..<n-i}" by simp
  then have B: "x (n-i-1) \<noteq> t" using x_def unfolding classes_def by blast

  from A B show False by simp
qed

lemma "\<forall>\<chi> r t k. \<exists>M'. \<forall>M \<ge> M'. \<chi> \<in> (cube M (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. isSubspace S k M (t + 1) \<and> (\<forall>i \<in> {..M}. \<exists>c < r. \<chi> ` (classes M t i) = {c}))"
  sorry


lemma "A \<noteq> {} \<Longrightarrow> A \<rightarrow>\<^sub>E {} = {}"
  by auto

lemma "A = {} \<Longrightarrow> \<exists>!f. f \<in> A \<rightarrow>\<^sub>E B"
  by simp
  
lemma "B \<noteq> {} \<Longrightarrow> A \<rightarrow>\<^sub>E B \<noteq> {}"
  
  by (meson PiE_eq_empty_iff)
lemma thm4_k_1: assumes "t > 0" "(\<forall>r. \<exists>N'. \<forall>N \<ge> N'. \<chi> \<in> (cube N t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. isLine L N t \<and> \<chi> ` (L ` {..<t}) = {c}))" shows "(\<forall>r. \<exists>M'. \<forall>M \<ge> M'. \<chi> \<in> (cube M (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. isSubspace S 1 M (t + 1) \<and> (\<forall>i \<in> {..M}. \<exists>c < r. \<chi> ` (classes M t i) = {c})))"
proof
  fix r
  have "\<exists>N'. \<forall>N\<ge>N'. \<chi> \<in> cube N t \<rightarrow>\<^sub>E {..<r} \<longrightarrow> (\<exists>L c. c < r \<and> isLine L N t \<and> \<chi> ` L ` {..<t} = {c})" using assms(2) by simp
  then obtain N' where N'_def: "\<forall>N\<ge>N'. \<chi> \<in> cube N t \<rightarrow>\<^sub>E {..<r} \<longrightarrow> (\<exists>L c. c < r \<and> isLine L N t \<and> \<chi> ` L ` {..<t} = {c})" by blast
  then have "\<chi> \<in> cube N' t \<rightarrow>\<^sub>E {..<r} \<longrightarrow> (\<exists>L c. c < r \<and> isLine L N' t \<and> \<chi> ` L ` {..<t} = {c})" by simp

  have **: "\<forall>n. cube n t \<noteq> {}" 
    by (metis PiE_eq_empty_iff assms(1) cube_def lessThan_0 lessThan_eq_iff neq_iff)
  
  have *: "\<forall>n. cube n (t + 1) \<noteq> {}" using PiE_eq_empty_iff unfolding cube_def assms(1) 
    by (metis add.right_neutral assms(1) lessThan_0 lessThan_eq_iff less_add_eq_less less_imp_le less_numeral_extra(1) not_less) 
  show "\<exists>M'. \<forall>M\<ge>M'. \<chi> \<in> cube M (t + 1) \<rightarrow>\<^sub>E {..<r} \<longrightarrow> (\<exists>S. isSubspace S 1 M (t + 1) \<and> (\<forall>i\<in>{..M}. \<exists>c<r. \<chi> ` classes M t i = {c}))" 
  proof (cases r)
    case 0
    then have "{..<r} = {}" by simp
    then have "\<forall>n. cube n (t + 1) \<rightarrow>\<^sub>E {..<r} = {}" using * by auto
    then show ?thesis by simp
  next
    case (Suc nat)
    then have "{..<r} ~= {}" by auto
    then have "\<forall>n. cube n (t + 1) \<rightarrow>\<^sub>E {..<r} \<noteq> {}" using PiE_eq_empty_iff by metis
    then obtain \<chi> where \<chi>_def: "\<chi> \<in> cube N' (t + 1) \<rightarrow>\<^sub>E {..<r}" by auto

    from Suc have "{..<r} ~= {}" by auto
    then have "\<forall>n. cube n (t) \<rightarrow>\<^sub>E {..<r} \<noteq> {}" using PiE_eq_empty_iff by metis

    
    have "\<forall>M\<ge>N'. \<chi> \<in> cube M (t + 1) \<rightarrow>\<^sub>E {..<r} \<longrightarrow> (\<exists>S. isSubspace S 1 M (t + 1) \<and> (\<forall>i\<in>{..M}. \<exists>c<r. \<chi> ` classes M t i = {c}))"
    proof (rule allI, rule impI, rule impI)
      fix M
      assume asms: "N' \<le> M" "\<chi> \<in> cube M (t + 1) \<rightarrow>\<^sub>E {..<r}"
      let ?S = "{x . x \<in> cube M (t + 1) \<and> (\<forall>j<M. x j \<noteq> t)}"
      {
      have "?S \<subseteq> cube M t" 
      proof 
        fix x
        assume a: "x \<in> {x . x \<in> cube M (t + 1) \<and> (\<forall>j<M. x j \<noteq> t)}"
        then have "\<forall>j\<in>{..<M}. x j \<in> {..<t + 1}" unfolding cube_def by blast
        then have "\<forall>j<M. x j \<in> {..<t} \<union> {t}" by force
        then have "\<forall>j<M. x j \<in> {..<t}" using a by auto

        moreover have "\<forall>j. \<not>(j\<in>{..<M}) \<longrightarrow> x j = undefined" using a unfolding cube_def by blast
        ultimately show "x \<in> cube M t" unfolding cube_def by blast
      qed
    }
    moreover
    {
      have "cube M t \<subseteq> ?S"
      proof
        fix x
        assume a: "x \<in> cube M t"
        then have "x \<in> cube M (t + 1)" using AUX  by auto
        moreover have "\<forall>j\<in>{..<M}. x j \<in> {..<t}" using a unfolding cube_def by blast
        moreover have "\<forall>j<M. x j \<noteq> t" using calculation(2) by blast
        ultimately show "x \<in> {x \<in> cube M (t + 1). \<forall>j<M. x j \<noteq> t} " by simp
      qed
    }
    ultimately have ***: "?S = cube M t" by simp


    qed
    then show ?thesis sorry
  qed

  



qed
definition isSubspace_alt
  where "isSubspace_alt S k n t \<equiv> (\<exists>\<phi>. k \<le> n \<and> bij_betw \<phi> S (cube k t))"
thm fun_upd_upd
lemma "n > 0 \<Longrightarrow> t > 1 \<Longrightarrow> isLine L n t \<Longrightarrow> isSubspace (\<lambda>f x. L (f 0) x) 1 n t"
proof -
  assume assms: " n > 0" " 1 < t" "isLine L n t"
  let ?B1 = "{i::nat . i < n \<and> (\<forall>x<t. \<forall>y<t. L x i =  L y i)}"
  let ?B0 = "{i::nat . i < n \<and> (\<forall>s < t. L s i = s)}"
  let ?K = "(\<lambda>i::nat. {}::nat set)(0:=?B0, 1:=?B1)"
  have "(?B0) \<noteq> {}" using assms(3) unfolding isLine_def by simp

  have L1: "?B0 \<union> ?B1 = {..<n}" using assms(3) unfolding isLine_def by auto

  have "\<forall>i < n. (\<forall>s < t. L s i = s) \<longrightarrow> \<not>(\<forall>x<t. \<forall>y<t. L x i =  L y i)" using assms(2) 
    using less_trans by auto 
  then have *:"\<forall>i \<in> ?B1. i \<notin>?B0" by blast

  have "\<forall>i < n. (\<forall>x<t. \<forall>y<t. L x i =  L y i) \<longrightarrow> \<not>(\<forall>s < t. L s i = s)" 
  proof(rule allI, rule impI, rule impI)
    fix i
    assume asm: "i<n" "\<forall>x<t. \<forall>y<t. L x i = L y i"
    have "L 0 i = L 1 i" using assms(2) asm(1,2) 
      by blast
    then show "\<not> (\<forall>s<t. L s i = s)" 
      by (metis assms(2) less_numeral_extra(1) less_trans zero_neq_one)
  qed
  then have **: "\<forall>i \<in> ?B0. i \<notin> ?B1" 
    by blast

  have L2: "?B0 \<inter> ?B1 = {}" using * ** by blast
  have A1: "disjoint (?K ` {..1::nat})" using L2 
    by (smt (verit) Int_commute atMost_iff disjnt_def fun_upd_other fun_upd_same less_one nat_less_le pairwise_imageI)
  have A2: "\<Union>(?K ` {..1::nat}) = ?K 0 \<union> ?K 1" by auto
  have A3: "\<forall>i \<in> {..<1::nat}. ?K i \<noteq> {}" 
    using \<open>{i. i < n \<and> (\<forall>s<t. L s i = s)} \<noteq> {}\<close> fun_upd_same lessThan_iff less_one by auto

  let ?f = "(\<lambda>i. if i \<in> ?K 1 then L 0 i else undefined)"

  have A4: "?f \<in> (?K 1) \<rightarrow>\<^sub>E {..<t}" 
  proof
    fix i
    assume asm: "i \<in> (?K 1)"
    then have *:" i < n \<and> (\<forall>x<t. \<forall>y<t. L x i =  L y i)" 
      by (smt (verit) fun_upd_same mem_Collect_eq)
    then have "?f i = L 0 i" using asm 
      by metis
    have g: " 0 \<in> {..<t}" using assms(2) by simp
    have h: "i \<in> {..<n}" using * by simp
    
    have "\<forall>a \<in> {..<t}. \<forall>b \<in> {..<n}. L a b \<in> {..<t}" using assms(3) unfolding isLine_def cube_def by auto
    then have "L 0 i \<in> {..<t}" using g h by simp
    then show "?f i \<in> {..<t}" using \<open>?f i = L 0 i\<close> by simp
  next
    fix i
    assume asm: "i \<notin> (?K 1)"
    then show "?f i = undefined" by auto
  qed

(*f' = (\<lambda>y i. (if i \<in> B k then f i else y (SOME j. j < k \<and> i \<in> B j)))*)
  let ?F = "(\<lambda>y i. (if i \<in> ?K 1 then ?f i else y (SOME j. j < 1 \<and> i \<in> ?K 1)))"
  have "?F \<in> (cube 1 t) \<rightarrow>\<^sub>E (cube n t)"
    sorry


  show "isSubspace (\<lambda>f. L (f 0)) 1 n t" sorry


qed


lemma hales_jewett: "\<forall>\<chi> r t. \<exists>N'. \<forall>N \<ge> N'. \<chi> \<in> (cube N t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. isLine L N t \<and> \<chi> ` (L ` {..<t}) = {c})"
  sorry
  
  

  
  

end