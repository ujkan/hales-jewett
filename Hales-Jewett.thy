theory "Hales-Jewett"
  imports Main "HOL-Library.FuncSet" "HOL-Library.Disjoint_Sets"
begin

text
\<open>
Goals for next week (8 Nov 2021)

- finish the base case
+ understand vdw proof
+ potentially look at other resources -> goal to understand
+ write comments, clean things up

Goals for next week (15 Nov 2021)
+ finish the base case
* start on the induction step / outline

Notes (14 nov 2021)
  * base case proof not strictly formulated; have proven only for particular N', not \<forall>N\<ge>N'.

Goals for next week (22 Nov 2021)
* clean up a few things in the base case
* base case trivialities (t = 0, n = 0)
* start on the induction step /outline

\<close>

lemma "f \<in> A \<rightarrow>\<^sub>E B \<longleftrightarrow> ((\<forall>a. (a \<in> A \<longrightarrow> f a \<in> B) \<and> (a \<notin> A \<longrightarrow> f a = undefined)))" 
  by auto

definition cube :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "cube n t \<equiv> {..<n} \<rightarrow>\<^sub>E {..<t}"

text \<open>Attempting to show (card {} ->E A) = 1\<close>
lemma aux: "\<exists>!f. f \<in> {} \<rightarrow>\<^sub>E A " 
  by simp

lemma "(\<lambda>x. undefined) \<in> {} \<rightarrow>\<^sub>E A"
  by simp
lemma AUX: "cube n t \<subseteq> cube n (t + 1)"
  unfolding cube_def
  by (meson PiE_mono le_add1 lessThan_subset_iff)


lemma cube0_def: "cube 0 t = {\<lambda>x. undefined}"
  unfolding cube_def by simp
lemma "card ({} \<rightarrow>\<^sub>E A) = 1"
  using aux by auto

thm card_PiE
lemma cube_card: "card ({..<n::nat} \<rightarrow>\<^sub>E {..<t::nat}) = t ^ n"
  apply (subst card_PiE)
  by auto
  
definition is_line :: "(nat \<Rightarrow> (nat \<Rightarrow> nat)) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "is_line L n t \<equiv> (L \<in> {..<t} \<rightarrow>\<^sub>E (cube n t) \<and> ((\<forall>j<n. (\<forall>x<t. \<forall>y<t. L x j =  L y j) \<or> (\<forall>s<t. L s j = s)) \<and> (\<exists>j < n. (\<forall>s < t. L s j = s))))"

lemma is_line_elim:
  assumes "is_line L n t" and "t > 1"
  shows "\<exists>B\<^sub>0 B\<^sub>1. B\<^sub>0 \<union> B\<^sub>1 = {..<n} \<and> B\<^sub>0 \<inter> B\<^sub>1 = {} \<and> B\<^sub>0 \<noteq> {} \<and> (\<forall>j \<in> B\<^sub>1. (\<forall>x<t. \<forall>y<t. L x j = L y j)) \<and> (\<forall>j \<in> B\<^sub>0. (\<forall>s<t. L s j = s))"
proof-
  define B0 where "B0 = {j \<in> {..<n}. (\<forall>s<t. L s j = s)}"
  define B1 where "B1 = {j \<in> {..<n}. (\<forall>x<t. \<forall>y<t. L x j = L y j)}"

  from assms have "B0 \<noteq> {}" unfolding is_line_def B0_def by simp
  moreover from assms have "B0 \<union> B1 = {..<n}" unfolding is_line_def B0_def B1_def by auto
  moreover have "\<forall>j \<in> B0. \<forall>s<t. L s j = s" unfolding B0_def by simp
  moreover have "\<forall>j \<in> B1. \<forall>x<t. \<forall>y<t. L x j = L y j" unfolding B1_def by blast
  moreover have "B0 \<inter> B1 = {}" 
  proof(safe)
    fix i assume "i \<in> B0" "i\<in>B1"
    then have "(\<forall>s < t. L s i = s) " unfolding B0_def by simp
    then have "\<not>(\<forall>x<t. \<forall>y<t. L x i = L y i)" using assms(2) less_trans 
      by (metis less_numeral_extra(1) zero_neq_one)
    then have False using \<open>i \<in> B1\<close> unfolding B1_def by blast
    then show "i \<in> {}" by simp
  qed
  ultimately show ?thesis by blast
qed


lemma aux2: "is_line L n t \<Longrightarrow> (\<forall>s<t. L s \<in> cube n t)"
  unfolding cube_def is_line_def
  by auto     

lemma aux2_exp: "is_line L n t \<Longrightarrow> (\<forall>s<t. \<forall>j<n. L s j \<in> {..<t})" 
  using aux2 unfolding cube_def by blast

lemma 
  assumes "is_line L n t" and "t > 1"
  shows "\<exists>L'. is_line L' n (t + 1) \<and> (\<forall>i\<in>{..<n}.\<forall>s<t. L s i = L' s i)"
proof-
  from assms obtain B0 B1 where Bdefs: "B0 \<union> B1 = {..<n} \<and> B0 \<inter> B1 = {} \<and> B0 \<noteq> {} \<and> (\<forall>j \<in> B1. (\<forall>x<t. \<forall>y<t. L x j = L y j)) \<and> (\<forall>j \<in> B0. (\<forall>s<t. L s j = s))" using is_line_elim by presburger
  define L' where "L' \<equiv> L(t:=(\<lambda>i. if i \<in> B0 then t else (if i \<in> B1 then L 0 i else undefined)))"
  have "L' \<in> {..<t+1} \<rightarrow>\<^sub>E (cube n (t + 1))"
  proof
    fix s assume "s \<in> {..<t+1}"
    then consider "s < t" | "s = t" by fastforce
    then show "L' s \<in> cube n (t + 1)"
    proof (cases)
      case 1
      then show ?thesis using assms(1) AUX unfolding L'_def is_line_def by auto
    next
      case 2
      show ?thesis 
      proof (unfold cube_def; intro PiE_I)
        fix j assume "j\<in>{..<n}"
        then have "j \<in> B0 \<union> B1" using Bdefs by simp
        then have "L' s j = t \<or> L' s j = L 0 j" using 2 unfolding L'_def by auto
        then show "L' s j \<in> {..<t+1}" using assms(1) aux2_exp[of "L" "n" "t"] 
          by (metis "2" \<open>j \<in> {..<n}\<close> \<open>s \<in> {..<t + 1}\<close> assms(2) lessThan_iff less_numeral_extra(1) less_trans)
      next
        fix j assume "j \<notin>{..<n}"
        then have "j \<notin> B0 \<union> B1" using Bdefs by simp
        then show "L' s j = undefined" unfolding L'_def 
          by (simp add: "2")
      qed
    qed
  next
    fix s assume "s \<notin> {..<t+1}"
    then show "L' s = undefined" using assms(1) unfolding L'_def is_line_def 
      by (metis (no_types, lifting) PiE_restrict add.commute fun_upd_apply lessThan_iff less_Suc_eq plus_1_eq_Suc restrict_apply)
  qed

  show ?thesis sorry
qed

lemma "is_line L n t \<Longrightarrow> L ` {..<t} \<subseteq> cube n t"
  unfolding cube_def is_line_def
  by auto


term disjoint_family_on
term partition_on
definition is_subspace
  where "is_subspace f' k n t \<equiv> (\<exists>B f. disjoint_family_on B {..k} \<and> \<Union>(B ` {..k}) = {..<n} \<and> ({} \<notin> B ` {..<k}) \<and> f \<in> (B k) \<rightarrow>\<^sub>E {..<t} \<and> f' \<in> (cube k t) \<rightarrow>\<^sub>E (cube n t) \<and> (\<forall>y \<in> cube k t. (\<forall>i \<in> B k. f' y i = f i) \<and> (\<forall>j<k. \<forall>i \<in> B j. (f' y) i = y j)))"

lemma dim0_subspace: assumes "t > 0" shows "\<exists>S. is_subspace S 0 n t"
proof-
  define B where "B \<equiv> (\<lambda>x::nat. undefined)(0:={..<n})"

  have "{..<t} \<noteq> {}" using assms by auto
  then have "\<exists>f. f \<in> (B 0) \<rightarrow>\<^sub>E {..<t}" 
    by (meson PiE_eq_empty_iff all_not_in_conv)
  then obtain f where f_prop: "f \<in> (B 0) \<rightarrow>\<^sub>E {..<t}" by blast
  define S where "S \<equiv> (\<lambda>x::(nat \<Rightarrow> nat). undefined)((\<lambda>x. undefined):=f)"

  have "disjoint_family_on B {..0}" unfolding disjoint_family_on_def by simp
  moreover have "\<Union>(B ` {..0}) = {..<n}" unfolding B_def by simp
  moreover have "({} \<notin> B ` {..<0})" by simp
  moreover have "S \<in> (cube 0 t) \<rightarrow>\<^sub>E (cube n t)"
    using f_prop PiE_I unfolding B_def cube_def S_def by auto
  moreover have "(\<forall>y \<in> cube 0 t. (\<forall>i \<in> B 0. S y i = f i) \<and> (\<forall>j<0. \<forall>i \<in> B j. (S y) i = y j))" unfolding cube_def S_def by force
  ultimately have "is_subspace S 0 n t" using f_prop unfolding is_subspace_def by blast
  then show "\<exists>S. is_subspace S 0 n t" by auto
qed

text \<open>Defining the equivalence classes of (cube n (t + 1)). {classes n t 0, ..., classes n t n}\<close>
definition classes
  where "classes n t \<equiv> (\<lambda>i. {x . x \<in> (cube n (t + 1)) \<and> (\<forall>u \<in> {(n-i)..<n}. x u = t) \<and> t \<notin> x ` {..<(n - i)}})"

definition layered_subspace
  where "layered_subspace S k n t r \<chi> \<equiv> (is_subspace S k n (t + 1) \<and> (\<forall>i \<in> {..k}. \<exists>c<r. \<forall>x \<in> classes k t i. \<chi> (S x) = c))"

lemma dim0_layered_subspace_ex: assumes "\<chi> \<in> (cube n (t + 1)) \<rightarrow>\<^sub>E {..<r::nat}" shows "\<exists>S. layered_subspace S (0::nat) n t r \<chi>"
proof-
  obtain S where S_prop: "is_subspace S (0::nat) n (t+1)" using dim0_subspace by auto

(* {x . x \<in> (cube 0 (t + 1)) \<and> (\<forall>u \<in> {(0-0)..<0}. x u = t) \<and> t \<notin> x ` {..<(0 - 0)}} *)
  have "classes (0::nat) t 0 = cube 0 (t+1)" unfolding classes_def by simp
  moreover have "(\<forall>i \<in> {..0::nat}. \<exists>c<r. \<forall>x \<in> classes (0::nat) t i. \<chi> (S x) = c)"
  proof(safe)
    fix i
    have "\<forall>x \<in> classes 0 t 0. \<chi> (S x) = \<chi> (S (\<lambda>x. undefined))" using cube0_def 
      using \<open>classes 0 t 0 = cube 0 (t + 1)\<close> by auto
    moreover have "S (\<lambda>x. undefined) \<in> cube n (t+1)" using S_prop cube0_def unfolding is_subspace_def by auto
    then have "\<chi> (S (\<lambda>x. undefined)) < r" using assms by auto
    ultimately show "\<exists>c<r. \<forall>x\<in>classes 0 t 0. \<chi> (S x) = c" by auto
  qed
  ultimately have "layered_subspace S 0 n t r \<chi>" using S_prop unfolding layered_subspace_def by blast
  then show "\<exists>S. layered_subspace S (0::nat) n t r \<chi>" by auto
qed

lemma "is_subspace S 1 n t \<Longrightarrow> layered_subspace S 1 n t r \<chi> \<Longrightarrow> (\<exists>c. \<forall>y\<in>cube 1 t. \<chi> (S y) = c)" sorry

text \<open>Proving they are equivalence classes.\<close>

lemma disjoint_family_onI [intro]:
  assumes "\<And>m n. m \<in> S \<Longrightarrow> n \<in> S \<Longrightarrow> m \<noteq> n \<Longrightarrow> A m \<inter> A n = {}"
  shows   "disjoint_family_on A S"
  using assms by (auto simp: disjoint_family_on_def)

lemma disjoint_classes2: "disjoint_family_on (classes n t) {..n}"
proof
  fix i j
  assume "i \<in> {..n}" "j \<in> {..n}" "i \<noteq> j"
  thus "classes n t i \<inter> classes n t j = {}"
  proof (induction i j rule: linorder_wlog)
    case (le a b)
    then show ?case sorry
  next
    case (sym a b)
    thus ?case by (simp add: Int_commute)
  qed
qed

lemma disjoint_classes: "i < j \<and> j \<le> n \<Longrightarrow> classes n t i \<inter> classes n t j = {}"
proof (rule ccontr)
  assume assms: "i < j \<and> j \<le> n" "classes n t i \<inter> classes n t j \<noteq> {}"
  then have "\<exists>x.  x\<in> classes n t i \<inter> classes n t j" by blast
  then obtain x where x_def: "x \<in> classes n t i \<inter> classes n t j" by blast

  have "n - i > n - j" using assms(1, 2) by auto
  then have *: "n - i - 1 \<ge> n - j" by simp

  have "n - i - 1 < n" 
    using Suc_diff_Suc Suc_le_lessD assms(1) by linarith
  then have "n - i - 1 \<in> {n - j..<n}" using * by simp
  then have A: "x (n-i-1) = t" using x_def unfolding classes_def by blast

  have "(n - i - 1 < n - i)" 
    by (meson assms(1) diff_less less_le_trans zero_less_diff zero_less_one)
  then have "n - i - 1 \<in> {..<n-i}" by simp
  then have B: "x (n-i-1) \<noteq> t" using x_def unfolding classes_def by blast

  from A B show False by simp
qed

text \<open>LHJ(r, t, k).\<close>
lemma "\<forall>\<chi> r t k. \<exists>M'. \<forall>M \<ge> M'. \<chi> \<in> (cube M (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. is_subspace S k M (t + 1) \<and> (\<forall>i \<in> {..M}. \<exists>c < r. \<chi> ` (classes M t i) = {c}))"
  sorry

text \<open>Experiments to see how \<rightarrow> behaves.\<close>
lemma "A \<noteq> {} \<Longrightarrow> A \<rightarrow>\<^sub>E {} = {}"
  by auto

lemma "A = {} \<Longrightarrow> \<exists>!f. f \<in> A \<rightarrow>\<^sub>E B"
  by simp
  
lemma "B \<noteq> {} \<Longrightarrow> A \<rightarrow>\<^sub>E B \<noteq> {}"
  by (meson PiE_eq_empty_iff)

lemma "bij_betw f A B \<Longrightarrow> (\<forall>a \<in> A. \<exists>!b \<in> B. f a = b)"
  unfolding bij_betw_def by blast

lemma fun_ex: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> \<exists>f \<in> A \<rightarrow>\<^sub>E B. f a = b" 
proof-
  assume assms: "a \<in> A" "b \<in> B"
  then obtain g where g_def: "g \<in> A \<rightarrow> B \<and> g a = b" by fast
  let ?f = "restrict g A" 
  have "?f \<in> A \<rightarrow>\<^sub>E B" using g_def by auto
  then show "\<exists>f \<in> A \<rightarrow>\<^sub>E B. f a = b" 
    by (metis assms(1) g_def restrict_apply')
qed

lemma one_dim_cube_eq_nat_set: "bij_betw (\<lambda>f. f 0) (cube 1 k) {..<k}"
proof (unfold bij_betw_def)
  have A2: "(\<lambda>f. f 0) ` cube 1 k = {..<k}"
  proof(safe)
    fix x f
    assume "f \<in> cube 1 k"
    then show "f 0 < k" unfolding cube_def by blast
  next
    fix x
    assume "x < k"
    then have "x \<in> {..<k}" by simp
    moreover have "0 \<in> {..<1::nat}" by simp
    ultimately have "\<exists>y \<in> {..<1::nat} \<rightarrow>\<^sub>E {..<k}. y 0 = x" using fun_ex[of "0" "{..<1::nat}" "x" "{..<k}"] by auto 
    then show "x \<in> (\<lambda>f. f 0) ` cube 1 k" unfolding cube_def by blast
  qed
  have "card (cube 1 k) = k" using cube_card by (simp add: cube_def)
  moreover have "card {..<k} = k" by simp
  ultimately have A1: "inj_on (\<lambda>f. f 0) (cube 1 k)" 
    by (metis A2 card.infinite empty_iff eq_card_imp_inj_on image_is_empty inj_on_def lessThan_0)

  from A1 A2 show "inj_on (\<lambda>f. f 0) (cube 1 k) \<and> (\<lambda>f. f 0) ` cube 1 k = {..<k}" by simp
qed

lemma nat_set_eq_one_dim_cube: "bij_betw (\<lambda>x. \<lambda>y\<in>{..<1::nat}. x) {..<k::nat} (cube 1 k)"
proof (unfold bij_betw_def)
  have A2: "(\<lambda>x. \<lambda>y\<in>{..<1::nat}. x) ` {..<k} = cube 1 k"
  proof (safe)
    fix x y
    assume "y < k"
    then show "(\<lambda>z\<in>{..<1}. y) \<in> cube 1 k" unfolding cube_def by simp
  next
    fix x
    assume "x \<in> cube 1 k"
    then have "x = (\<lambda>z. \<lambda>y\<in>{..<1::nat}. z) (x 0::nat)" unfolding cube_def 
      by (smt (verit, best) PiE_iff extensionalityI lessThan_iff less_one restrict_apply restrict_extensional)
    moreover have "x 0 \<in> {..<k}" using \<open>x \<in> cube 1 k\<close> by (auto simp add: cube_def)
    ultimately show "x \<in> (\<lambda>z. \<lambda>y\<in>{..<1}. z) ` {..<k}"  by blast
  qed

  have "card (cube 1 k) = k" using cube_card by (simp add: cube_def)
  moreover have "card {..<k} = k" by simp
  ultimately have A1:  "inj_on (\<lambda>x. \<lambda>y\<in>{..<1::nat}. x) {..<k}" using A2 
    by (metis eq_card_imp_inj_on finite_lessThan)
  from A1 A2 show "inj_on (\<lambda>x. \<lambda>y\<in>{..<1::nat}. x) {..<k} \<and> (\<lambda>x. \<lambda>y\<in>{..<1::nat}. x) ` {..<k} = cube 1 k" by blast
qed

lemma bij_domain_PiE:
  assumes "bij_betw f A1 A2" 
      and "g \<in> A2 \<rightarrow>\<^sub>E B"
    shows "(restrict (g \<circ> f) A1) \<in> A1 \<rightarrow>\<^sub>E B"
  using bij_betwE assms by fastforce

lemma props_over_bij: "bij_betw h X Y \<Longrightarrow> (\<forall>x \<in> X. P a x) \<Longrightarrow> (\<forall>x \<in> X. P a x = Q a (h x)) \<Longrightarrow> (\<forall>y \<in> Y. Q a y)"
  by (smt (verit, ccfv_SIG) bij_betwE bij_betw_the_inv_into f_the_inv_into_f_bij_betw)


text \<open>Relating lines and 1-dimensional subspaces.\<close>
(* use assumes and shows *)
lemma line_is_dim1_subspace: "n > 0 \<Longrightarrow> t > 1 \<Longrightarrow> is_line L n t \<Longrightarrow> is_subspace (restrict (\<lambda>y. L (y 0)) (cube 1 t)) 1 n t"
proof -
  assume assms: "n > 0" "1 < t" "is_line L n t"
  let ?B1 = "{i::nat . i < n \<and> (\<forall>x<t. \<forall>y<t. L x i =  L y i)}"
  let ?B0 = "{i::nat . i < n \<and> (\<forall>s < t. L s i = s)}"
  let ?K = "(\<lambda>i::nat. {}::nat set)(0:=?B0, 1:=?B1)"
  have "(?B0) \<noteq> {}" using assms(3) unfolding is_line_def by simp

  have L1: "?B0 \<union> ?B1 = {..<n}" using assms(3) unfolding is_line_def by auto

  have "\<forall>i < n. (\<forall>s < t. L s i = s) \<longrightarrow> \<not>(\<forall>x<t. \<forall>y<t. L x i =  L y i)" using assms(2) 
    using less_trans by auto 
  then have *:"\<forall>i \<in> ?B1. i \<notin>?B0" by blast

  have "\<forall>i < n. (\<forall>x<t. \<forall>y<t. L x i =  L y i) \<longrightarrow> \<not>(\<forall>s < t. L s i = s)" 
  proof(intro allI impI)
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

  have "{..1::nat} = {0, 1}" by auto
  then have "\<Union>(?K ` {..1::nat}) = ?K 0 \<union> ?K 1" by simp
  then have "\<Union>(?K ` {..1::nat}) = ?B0 \<union> ?B1" by simp
  then have A1: "disjoint_family_on ?K {..1::nat}" using L2 
    by (simp add: Int_commute disjoint_family_onI)
    
  have "\<Union>(?K ` {..1::nat}) = ?K 0 \<union> ?K 1" by auto
  then have A2: "\<Union>(?K ` {..1::nat}) = {..<n}" using L1 by simp
  have "\<forall>i \<in> {..<1::nat}. ?K i \<noteq> {}" 
    using \<open>{i. i < n \<and> (\<forall>s<t. L s i = s)} \<noteq> {}\<close> fun_upd_same lessThan_iff less_one by auto
  then have A3: "{} \<notin> ?K ` {..<1::nat}" by blast

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
    
    have "\<forall>a \<in> {..<t}. \<forall>b \<in> {..<n}. L a b \<in> {..<t}" using assms(3) unfolding is_line_def cube_def by auto
    then have "L 0 i \<in> {..<t}" using g h by simp
    then show "?f i \<in> {..<t}" using \<open>?f i = L 0 i\<close> by simp
  next
    fix i
    assume asm: "i \<notin> (?K 1)"
    then show "?f i = undefined" by auto
  qed


  have L_prop: "L \<in> {..<t} \<rightarrow>\<^sub>E (cube n t)" using assms(3) by (simp add: is_line_def)
  let ?L = "(\<lambda>y \<in> cube 1 t. L (y 0))"
  have A5: "?L \<in> (cube 1 t) \<rightarrow>\<^sub>E (cube n t)"
    using bij_domain_PiE[of "(\<lambda>f. f 0)" "(cube 1 t)" "{..<t}" "L" "cube n t"] one_dim_cube_eq_nat_set[of "t"] L_prop by auto

  have A6: "\<forall>y \<in> cube 1 t. (\<forall>i \<in> ?K 1. ?L y i = ?f i) \<and> (\<forall>j < 1. \<forall>i \<in> ?K j. (?L y) i = y j)"
  proof
    fix y 
    assume "y \<in> cube 1 t"
    then have "y 0 \<in> {..<t}" unfolding cube_def by blast

    have A: "(\<forall>i \<in> ?K 1. ?L y i = ?f i)"
    proof
      fix i
      assume "i \<in> ?K 1"
      then have "?f i = L 0 i" 
        by meson
      moreover have "?L y i = L (y 0) i" using \<open>y \<in> cube 1 t\<close> by simp
      moreover have "L (y 0) i = L 0 i" using assms(3) \<open>i \<in> ?K 1\<close> unfolding is_line_def 
        by (smt (verit) \<open>y 0 \<in> {..<t}\<close> assms(2) fun_upd_same lessThan_iff less_trans mem_Collect_eq zero_less_one)
      ultimately show "?L y i = ?f i" by simp
    qed

    have B: "(\<forall>j < 1. \<forall>i \<in> ?K j. (?L y) i = y j)"
    proof(rule allI, rule impI)
      fix j
      assume "j < (1::nat)"
      then have "j = 0" by simp
      show "\<forall>i \<in> ?K j. (?L y) i = y j"
      proof
        fix i
        assume "i \<in> ?K j"
        then have "i \<in> ?K 0" using \<open>j=0\<close> by auto
        then have "(\<forall>s < t. L s i = s)" by simp
        moreover have "y 0 < t" using \<open>y \<in> cube 1 t\<close> unfolding cube_def by auto
        ultimately have "L (y 0) i = y 0" by simp

        have "?L y i = L (y 0) i" using \<open>y \<in> cube 1 t\<close> by simp
        then show "?L y i = y j" 
          using \<open>L (y 0) i = y 0\<close> \<open>j = 0\<close> by presburger
      qed
    qed
    from A B show "(\<forall>i \<in> ?K 1. ?L y i = ?f i) \<and> (\<forall>j < 1. \<forall>i \<in> ?K j. (?L y) i = y j)" 
      by blast
  qed

  from A1 A2 A3 A4 A5 A6 show "is_subspace ?L 1 n t" unfolding is_subspace_def by blast
qed

definition hj 
  where "hj t \<equiv> (\<forall>r. \<exists>N>0. \<forall>N' \<ge> N. \<forall>\<chi>. \<chi> \<in> (cube N' t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. is_line L N' t \<and> \<chi> ` (L ` {..<t}) = {c}))"

definition lhj
  where "lhj t \<equiv> (\<forall>r k. \<exists>M > 0. \<forall>M' \<ge> M. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. layered_subspace S k M' t r \<chi>))"

text \<open>The base case of Theorem 4 in the book.\<close>
(* outside quantifier unnecessary *)


lemma thm4_k_1: 
  fixes   r 
  assumes "t > 1"
      and "hj t" 
  shows   "(\<exists>M > 0. \<forall>M' \<ge> M. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. layered_subspace S 1 M' t r \<chi>))"
proof-
  obtain N where N_def: "N > 0 \<and> (\<forall>N' \<ge> N. \<forall>\<chi>. \<chi> \<in> (cube N' t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. is_line L N' t \<and> \<chi> ` (L ` {..<t}) = {c}))" using assms(2) unfolding hj_def by metis
  
  have "\<forall>N' \<ge> N. \<forall>\<chi>. \<chi> \<in> (cube N' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. is_subspace S 1 N' (t + 1) \<and> (\<forall>i \<in> {..1}. \<exists>c < r. (\<forall>x \<in> classes 1 t i. \<chi> (S x) = c)))"
  proof(safe)
    fix N' \<chi>
    assume asm: "N' \<ge> N" "\<chi> \<in> cube N' (t + 1) \<rightarrow>\<^sub>E {..<r::nat}"
    then have N'_props: "N' > 0 \<and> (\<forall>\<chi>. \<chi> \<in> (cube N' t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. is_line L N' t \<and> \<chi> ` (L ` {..<t}) = {c}))" using N_def by simp
    let ?chi_t = "(\<lambda>x \<in> cube N' t. \<chi> x)"
    have "?chi_t \<in> cube N' t \<rightarrow>\<^sub>E {..<r::nat}" using AUX asm by auto
    then obtain L where L_def: "\<exists>c<r. is_line L N' t \<and> ?chi_t ` (L ` {..<t}) = {c}" using N'_props by presburger

    have "is_subspace (restrict (\<lambda>y. L (y 0)) (cube 1 t)) 1 N' t" using line_is_dim1_subspace N'_props L_def 
      using assms(1) by auto 
    then obtain B f where Bf_defs: "disjoint_family_on B {..1} \<and> \<Union>(B ` {..1}) = {..<N'} \<and> ({} \<notin> B ` {..<1}) \<and> f \<in> (B 1) \<rightarrow>\<^sub>E {..<t} \<and> (restrict (\<lambda>y. L (y 0)) (cube 1 t)) \<in> (cube 1 t) \<rightarrow>\<^sub>E (cube N' t) \<and> (\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. (restrict (\<lambda>y. L (y 0)) (cube 1 t)) y i = f i) \<and> (\<forall>j<1. \<forall>i \<in> B j. ((restrict (\<lambda>y. L (y 0)) (cube 1 t)) y) i = y j))" unfolding is_subspace_def by auto 

    have "{..1::nat} = {0,1}" by auto
    then have B_props: "B 0 \<union> B 1 = {..<N'} \<and> (B 0 \<inter> B 1 = {})" using Bf_defs unfolding disjoint_family_on_def by auto
    let ?L' = "L(t:=(\<lambda>j. if j \<in> B 1 then L (t - 1) j else (if j \<in> B 0 then t else undefined)))" 
    have line_prop: "is_line ?L' N' (t + 1)"
    proof-
      have A1:"?L' \<in> {..<t+1} \<rightarrow>\<^sub>E cube N' (t + 1)" 
      proof
        fix x
        assume asm: "x \<in> {..<t + 1}"
        then show "?L' x \<in> cube N' (t + 1)"
        proof (cases "x < t")
          case True
          then have "?L' x = L x" by simp
          then have "?L' x \<in> cube N' t" using L_def True unfolding is_line_def by auto
          then show "?L' x \<in> cube N' (t + 1)" using AUX by blast
        next
          case False
          then have "x = t" using asm by simp
          show "?L' x \<in> cube N' (t + 1)"
          proof(unfold cube_def, intro PiE_I)
            fix j
            assume "j \<in> {..<N'}"
            have "j \<in> B 1 \<or> j \<in> B 0 \<or> j \<notin> (B 0 \<union> B 1)" by blast
            then show "?L' x j \<in> {..<t + 1}"
            proof (elim disjE)
              assume "j \<in> B 1"
              then have "?L' x j = L (t - 1) j" 
                by (simp add: \<open>x = t\<close>)
              have "L (t - 1) \<in> cube N' t" using aux2 L_def by auto
              then have "L (t - 1) j < t" using \<open>j \<in> {..<N'}\<close> unfolding cube_def by auto 
              then show "?L' x j \<in> {..<t + 1}" using \<open>?L' x j = L (t - 1) j\<close> by simp
            next
              assume "j \<in> B 0"
              then have "j \<notin> B 1" using Bf_defs unfolding disjoint_family_on_def by auto
              then have "?L' x j = t"  by (simp add: \<open>j \<in> B 0\<close> \<open>x = t\<close>)
              then show "?L' x j \<in> {..<t + 1}" by simp
            next
              assume a: "j \<notin> (B 0 \<union> B 1)"
              have "{..1::nat} = {0, 1}" by auto
              then have "B 0 \<union> B 1 = (\<Union>(B ` {..1::nat}))" by simp
              then have "B 0 \<union> B 1 = {..<N'}" using Bf_defs unfolding partition_on_def by simp
              then have "\<not>(j \<in> {..<N'})" using a by simp
              then have False using \<open>j \<in> {..<N'}\<close> by simp
              then show ?thesis by simp
            qed
          next
            fix j 
            assume "j \<notin> {..<N'}"
            then have "j \<notin> (B 0) \<and> j\<notin> B 1" using Bf_defs unfolding partition_on_def by auto
            then show "?L' x j = undefined" using \<open>x = t\<close> by simp
          qed
        qed
      next
        fix x
        assume asm: "x \<notin> {..<t+1}" 
        then have "x \<notin> {..<t} \<and> x \<noteq> t" by simp
        then show "?L' x = undefined"  by (metis (no_types, lifting) L_def PiE_E fun_upd_apply is_line_def)
      qed


      have A2: "(\<exists>j<N'. (\<forall>s < (t + 1). ?L' s j = s))"
      proof-
        have "(\<exists>j<N'. (\<forall>s < t. ?L' s j = s))" using L_def unfolding is_line_def by auto
        then obtain j where j_def: "j < N' \<and> (\<forall>s < t. ?L' s j = s)" by blast
        (* following not very clean, overreliance on sledgehammer *)
        have "j \<notin> B 1"
        proof 
          assume "j \<in> B 1"
          then have "(\<forall>y \<in> cube 1 t. (restrict (\<lambda>y. L (y 0)) (cube 1 t)) y j = f j)" using Bf_defs by simp
          then have "\<forall>y \<in> cube 1 t. L (y 0) j = f j" by simp
          moreover have "\<forall>y \<in> cube 1 t. (\<exists>!i. i < t \<and> y 0 = i)" using one_dim_cube_eq_nat_set[of "t"] unfolding bij_betw_def by blast
          moreover have "\<forall>i<t. (\<exists>!y. y \<in> cube 1 t \<and> y 0 = i)" using one_dim_cube_eq_nat_set[of "t"] unfolding bij_betw_def 
            by (smt (verit, best) image_iff inj_on_def lessThan_iff)
          moreover have "\<forall>i<t. L i j = f j" using calculation by blast
          moreover have "(\<exists>j<N'. (\<forall>s < t. L s j = s))" using \<open>(\<exists>j<N'. (\<forall>s < t. ?L' s j = s))\<close> by simp
          ultimately show False 
            by (metis (no_types, lifting) assms(1) fun_upd_other j_def less_numeral_extra(1) less_trans nat_neq_iff)
        qed
        then have "j \<in> B 0" using \<open>j \<notin> B 1\<close> j_def B_props by auto

        then have "?L' t j = t" using \<open>j \<notin> B 1\<close> by simp
        then have "(\<forall>s < (t + 1). ?L' s j = s)" using j_def by simp
        then show ?thesis using j_def by blast
      qed

      have A3: "(\<forall>j<N'. (\<forall>x<t+1. \<forall>y<t+1. ?L' x j =  ?L' y j) \<or> (\<forall>s<t+1. ?L' s j = s))"
      proof(intro allI impI)
        fix j
        assume "j < N'"
        show "(\<forall>x<t+1. \<forall>y<t+1. ?L' x j =  ?L' y j) \<or> (\<forall>s<t+1. ?L' s j = s)"
        proof (cases "j \<in> B 1")
          case True
          then have "(\<forall>y \<in> cube 1 t. (restrict (\<lambda>y. L (y 0)) (cube 1 t)) y j = f j)" using Bf_defs by simp
          moreover have "\<forall>y \<in> cube 1 t. (\<exists>!i. i < t \<and> y 0 = i)" using one_dim_cube_eq_nat_set[of "t"] unfolding bij_betw_def by blast
          moreover have "\<forall>i<t. (\<exists>!y. y \<in> cube 1 t \<and> y 0 = i)" using one_dim_cube_eq_nat_set[of "t"] unfolding bij_betw_def 
            by (smt (verit, best) image_iff inj_on_def lessThan_iff)
          moreover have "\<forall>i<t. L i j = f j" using calculation by auto
          ultimately have  "\<forall>x<t. \<forall>i<t. L i j = L x j" by simp
          then have *: "\<forall>x<t.\<forall>y<t. ?L' x j = ?L' y j" 
            by (metis (no_types, lifting) fun_upd_apply nat_neq_iff)

          have "?L' t j = ?L' (t - 1) j" using \<open>j \<in> B 1\<close> by simp
          then have "\<forall>x<t. ?L' x j = ?L' t j" using *  
            by (metis (no_types, lifting) assms(1) diff_less less_trans zero_less_one)
          then have "\<forall>x<t+1. \<forall>y<t+1. ?L' x j = ?L' y j" using * 
            by (simp add: less_Suc_eq)
          then show ?thesis by blast
        next
          case False
          then have "j \<in> B 0" using B_props \<open>j <N'\<close> by auto
          then have "\<forall>y \<in> cube 1 t. ((restrict (\<lambda>y. L (y 0)) (cube 1 t)) y) j = y 0" using \<open>j \<in> B 0\<close> Bf_defs by auto
          then have "\<forall>y \<in> cube 1 t. L (y 0) j = y 0"  by auto
          moreover have "\<forall>i<t. (\<exists>!y. y \<in> cube 1 t \<and> y 0 = i)" using one_dim_cube_eq_nat_set[of "t"] unfolding bij_betw_def 
            by (smt (verit, best) image_iff inj_on_def lessThan_iff)
          ultimately have "\<forall>s<t. L s j = s" by auto
          then have "\<forall>s<t. ?L' s j = s" by simp
          moreover have "?L' t j = t" using False \<open>j \<in> B 0\<close> by auto
          ultimately have "\<forall>s<t+1. ?L' s j = s" by simp
          then show ?thesis by blast
        qed
            



      qed
      from A1 A2 A3 show ?thesis unfolding is_line_def by simp


    qed
    then have F1: "is_subspace (restrict (\<lambda>y. ?L' (y 0)) (cube 1 (t + 1))) 1 N' (t + 1)" using line_is_dim1_subspace[of "N'" "t+1"] N'_props assms(1) by force

    define S1 where "S1 \<equiv> (restrict (\<lambda>y. ?L' (y (0::nat))) (cube 1 (t+1)))"
(* have F2: "\<exists>c < r. \<forall>x \<in> classes 1 t i. \<chi> (S1 x) = c" if i: "i \<in> {..1}" for i
proof - *)
    have F2: "(\<forall>i \<in> {..1}. \<exists>c < r. (\<forall>x \<in> classes 1 t i. \<chi> (S1 x) = c))"
    proof(safe)                    
      fix i
      assume "i \<le> (1::nat)"
      have "\<exists>c < r. ?chi_t ` (?L' ` {..<t}) = {c}" using L_def by auto
      have "\<forall>x \<in> (L ` {..<t}). x \<in> cube N' t" using L_def 
        using aux2 by blast
      then have "\<forall>x \<in> (?L' ` {..<t}). x \<in> cube N' t" by simp
      then have "\<forall>x \<in> (?L' ` {..<t}). \<chi> x = ?chi_t x" by simp
      then have "?chi_t ` (?L' ` {..<t}) = \<chi> ` (?L' ` {..<t})" by force
      then have "\<exists>c < r. \<chi> ` (?L' ` {..<t}) = {c}" using \<open>\<exists>c < r. ?chi_t ` (?L' ` {..<t}) = {c}\<close> by simp
      then obtain linecol where lc_def: "linecol < r \<and> \<chi> ` (?L' ` {..<t}) = {linecol}" by blast
      have "i = 0 \<or> i = 1" using \<open>i \<le> 1\<close> by auto
      then show "\<exists>c < r. (\<forall>x \<in> classes 1 t i. \<chi> (S1 x) = c)"
      proof (elim disjE)
        assume "i = 0"
        have *: "\<forall>a t. a \<in> {..<t+1} \<and> a \<noteq> t \<longleftrightarrow> a \<in> {..<(t::nat)}" by auto
        from \<open>i = 0\<close> have "classes 1 t 0 = {x . x \<in> (cube 1 (t + 1)) \<and> (\<forall>u \<in> {((1::nat) - 0)..<1}. x u = t) \<and> t \<notin> x ` {..<(1 - (0::nat))}}" using classes_def by simp
        also have "... = {x . x \<in> cube 1 (t+1) \<and> t \<notin> x ` {..<(1::nat)}}" by simp
        also have "... = {x . x \<in> cube 1 (t+1) \<and> (x 0 \<noteq> t)}" by blast 
        also have " ... = {x . x \<in> cube 1 (t+1) \<and> (x 0 \<in> {..<t+1} \<and> x 0 \<noteq> t)}" unfolding cube_def by blast
        also have " ... = {x . x \<in> cube 1 (t+1) \<and> (x 0 \<in> {..<t})}" using * by simp
        finally have redef: "classes 1 t 0 = {x . x \<in> cube 1 (t+1) \<and> (x 0 \<in> {..<t})}" by simp

         (* (\<lambda>x. x 0) ` (classes 1 t 0) *)
        have "{x 0 | x . x \<in> classes 1 t 0} \<subseteq> {..<t}" using redef by auto
        moreover have "{..<t} \<subseteq> {x 0 | x . x \<in> classes 1 t 0}" 
        proof
         fix x assume x: "x \<in> {..<t}"
         hence "\<exists>a\<in>cube 1 t. a 0 = x"
           unfolding cube_def by (intro fun_ex) auto
         then show "x \<in> {x 0 |x. x \<in> classes 1 t 0}"
           using x AUX unfolding redef by auto
        qed
        ultimately have **: "{x 0 | x . x \<in> classes 1 t 0} = {..<t}" by blast

        have "\<forall>x \<in> classes 1 t 0. \<chi> (S1 x) = linecol"
        proof
          fix x
          assume "x \<in> classes 1 t 0"
          then have "x \<in> cube 1 (t+1)" unfolding classes_def by simp
          then have "S1 x = ?L' (x 0)" unfolding S1_def by simp
          moreover have "x 0 \<in> {..<t}" using ** using \<open>x \<in> classes 1 t 0\<close> by blast
          ultimately show "\<chi> (S1 x) = linecol" using lc_def 
            using fun_upd_triv image_eqI by blast
        qed
        then show ?thesis using lc_def \<open>i = 0\<close> by auto
      next
        assume "i = 1"
        have "classes 1 t 1 = {x . x \<in> (cube 1 (t + 1)) \<and> (\<forall>u \<in> {0::nat..<1}. x u = t) \<and> t \<notin> x ` {..<0}}" unfolding classes_def by simp
        also have " ... = {x . x \<in> cube 1 (t+1) \<and> (\<forall>u \<in> {0}. x u = t)}" by simp
        finally have redef: "classes 1 t 1 = {x . x \<in> cube 1 (t+1) \<and> (x 0 = t)}" by auto
        have "\<forall>s \<in> {..<t+1}. \<exists>!x \<in> cube 1 (t+1). (\<lambda>p. \<lambda>y\<in>{..<1::nat}. p) s = x" using nat_set_eq_one_dim_cube[of "t+1"] unfolding bij_betw_def by blast
        then have "\<exists>!x \<in>cube 1 (t+1). (\<lambda>p. \<lambda>y\<in>{..<1::nat}. p) t = x" by auto
        then have "\<exists>!x \<in> cube 1 (t+1). (\<lambda>p. \<lambda>y\<in>{0}. p)  t  = x "  by force
        then have "\<exists>!x \<in> cube 1 (t+1). ((\<lambda>p. \<lambda>y\<in>{0}. p) t) 0  = x 0 "  
          by (smt (verit, ccfv_SIG) One_nat_def PiE_iff cube_def extensionalityI image_empty insertCI lessThan_0 lessThan_Suc_eq_insert_0 restrict_apply singletonD)
        then have "\<exists>!x \<in> cube 1 (t+1). x 0 = t" by auto
        then have "\<exists>!x \<in> classes 1 t 1. True" using redef by simp
        then obtain x where x_def: "x \<in> classes 1 t 1 \<and> (\<forall>y \<in> classes 1 t 1. x = y)" by auto

        have "\<exists>c < r. \<forall>x \<in> classes 1 t 1. \<chi> (S1 x) = c" 
        proof-
          have "\<forall>y \<in> classes 1 t 1. y = x" using x_def by auto
          then have "\<forall>y\<in>classes 1 t 1. \<chi> (S1 y) = \<chi> (S1 x)" by auto
          moreover have "x \<in> cube 1 (t+1)" using x_def  using redef by simp
          moreover have "S1 x \<in> cube N' (t+1)" using line_prop unfolding S1_def is_line_def 
            by (smt (z3) aux2 less_add_same_cancel1 less_numeral_extra(1) line_prop mem_Collect_eq redef restrict_apply x_def) 
          moreover have "\<chi> (S1 x) < r"  unfolding cube_def 
          by (metis PiE_mem asm(2) calculation(3) lessThan_iff)
          then show "\<exists>c < r. \<forall>x \<in> classes 1 t 1. \<chi> (S1 x) = c" using calculation by auto
        qed
        then show ?thesis using lc_def \<open>i = 1\<close> by auto
      qed


    qed
    show "(\<exists>S. is_subspace S 1 N' (t + 1) \<and> (\<forall>i \<in> {..1}. \<exists>c < r. (\<forall>x \<in> classes 1 t i. \<chi> (S x) = c))) " using F1 F2 unfolding S1_def by blast
  qed
  then show "\<exists>M>0. \<forall>M' \<ge> M. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. layered_subspace S 1 M' t r \<chi>)" using N_def unfolding layered_subspace_def by blast
qed


text \<open>Claiming k-dimensional subspaces of (cube n t) are isomorphic to (cube k t)\<close>
definition is_subspace_alt
  where "is_subspace_alt S k n t \<equiv> (\<exists>\<phi>. k \<le> n \<and> bij_betw \<phi> S (cube k t))"


thm "nat_induct"
lemma nat_01_induct [case_names 0 1 SSuc induct_type nat]: 
  fixes n
  assumes "P (0::nat)" and "P 1" and "(\<And>k. P k \<Longrightarrow> P (Suc k))" shows "P n"
  using assms by (induction n; auto)
  
lemma assumes "hj t" shows "lhj t"
proof-
  have "\<forall>r. \<exists>M>0. \<forall>M'\<ge>M. \<forall>\<chi>. \<chi> \<in> cube M' (t + 1) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. layered_subspace S k M' t r \<chi>)" for k
  proof (induction k rule: nat_01_induct)
    case 0
    then show ?case using dim0_layered_subspace_ex by blast
  next
    case 1
    then show ?case
    proof (cases "t > 1")
      case True
      then show ?thesis using thm4_k_1[of "t"] assms by simp
    next
      case False
      then show ?thesis sorry
    qed
  next
    case (SSuc k)
    then show ?case sorry
  qed
  then show "lhj t" unfolding lhj_def by simp
(* have F2: "\<exists>c < r. \<forall>x \<in> classes 1 t i. \<chi> (S1 x) = c" if i: "i \<in> {..1}" for i
proof - *)
qed


lemma dim1_subspace_elims: 
  assumes "disjoint_family_on B {..1::nat}" and "\<Union>(B ` {..1::nat}) = {..<n}" and "({} \<notin> B ` {..<1::nat})" and  "f \<in> (B 1) \<rightarrow>\<^sub>E {..<t}" and "S \<in> (cube 1 t) \<rightarrow>\<^sub>E (cube n t)" and "(\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. S y i = f i) \<and> (\<forall>j<1. \<forall>i \<in> B j. (S y) i = y j))"
  shows "B 0 \<union> B 1 = {..<n}"
    and "B 0 \<inter> B 1 = {}"
and "(\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. S y i = f i) \<and> (\<forall>i \<in> B 0. (S y) i = y 0))"
and "B 0 \<noteq> {}"
proof -
  have "{..1} = {0::nat, 1}" by auto
  then show "B 0 \<union> B 1 = {..<n}"  using assms(2) by simp
next
  show "B 0 \<inter> B 1 = {}" using assms(1) unfolding disjoint_family_on_def by simp
next
  show "(\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. S y i = f i) \<and> (\<forall>i \<in> B 0. (S y) i = y 0))" using assms(6) by simp
next
  show "B 0 \<noteq> {}" using assms(3) by auto
qed

lemma dim1_subspace_is_line: 
  assumes "t > 1" 
      and "is_subspace S 1 n t" 
    shows   "is_line (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) n t"
proof-
  have *: "\<forall>s \<in> {..<t}. \<exists>p \<in> cube 1 t. p 0 = s" unfolding cube_def by (simp add: fun_ex)
  have **: "\<forall>s \<in> {..<t}. (SOME p. p \<in> cube 1 t \<and> p 0 = s) 0 = s"
  proof(safe)
    fix s
    assume "s < t"
    then have "\<exists>p \<in> cube 1 t. p 0 = s" 
      using \<open>\<forall>s\<in>{..<t}. \<exists>p\<in>cube 1 t. p 0 = s\<close> by blast
    then show "(SOME p. p \<in> cube 1 t \<and>  p 0 = s) 0 = s" using someI_ex[of "\<lambda>x. x \<in> cube 1 t \<and> x 0 = s"] by auto
  qed
  define L where "L \<equiv> (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s))"

  have ***: "\<forall>s \<in> {..<t}. L s = L ((SOME p. p \<in> cube 1 t \<and> p 0 = s) 0)" using ** by simp
  have ****: "\<forall>s \<in> {..<t}. (SOME p. p \<in> cube 1 t \<and> p 0 = s) \<in> cube 1 t" using * 
    by (metis (mono_tags, lifting) verit_sko_ex')

  have "{..1} = {0::nat, 1}" by auto
  obtain B f where Bf_props: "disjoint_family_on B {..1::nat} \<and> \<Union>(B ` {..1::nat}) = {..<n} \<and> ({} \<notin> B ` {..<1::nat}) \<and> f \<in> (B 1) \<rightarrow>\<^sub>E {..<t} \<and> S \<in> (cube 1 t) \<rightarrow>\<^sub>E (cube n t) \<and> (\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. S y i = f i) \<and> (\<forall>j<1. \<forall>i \<in> B j. (S y) i = y j))" using assms(2) unfolding is_subspace_def by auto
  then have 1: "B 0 \<union> B 1 = {..<n} \<and> B 0 \<inter> B 1 = {}" using dim1_subspace_elims(1, 2)[of "B" "n" "f" "t" "S" ] by simp

  have "L \<in> {..<t} \<rightarrow>\<^sub>E cube n t"
  proof
    fix s assume a: "s \<in> {..<t}"
    then have "L s = S (SOME p. p\<in>cube 1 t \<and> p 0 = s)" unfolding L_def by simp
    moreover have "(SOME p. p\<in>cube 1 t \<and> p 0 = s) \<in> cube 1 t" using * a 
      by (metis (mono_tags, lifting) tfl_some) 
    moreover have "S (SOME p. p\<in>cube 1 t \<and> p 0 = s) \<in> cube n t"
      using assms(2) calculation(2) is_subspace_def by auto
    ultimately show "L s \<in> cube n t" by simp
  next
    fix s assume a: "s \<notin> {..<t}"
    then show "L s = undefined" unfolding L_def by simp
  qed
  moreover have "(\<forall>j<n. (\<forall>x<t. \<forall>y<t. L x j = L y j) \<or> (\<forall>s<t. L s j = s))"
  proof(intro allI impI)
    fix j assume a: "j < n"
    then consider "j \<in> B 0" | "j \<in> B 1" using 1 by blast
    then show "(\<forall>x<t. \<forall>y<t. L x j = L y j) \<or> (\<forall>s<t. L s j = s)"
    proof (cases)
      case 1
      have "(\<forall>s<t. L s j = s)"
      proof(intro allI impI)
        fix s 
        assume "s < t"
        then have "\<forall>y \<in> cube 1 t. (S y) j = y 0" using Bf_props 1 by simp
        then show "L s j = s" using \<open>s < t\<close> ** *** **** unfolding L_def by auto
      qed
      then show ?thesis by blast
    next
      case 2
      have "(\<forall>x<t. \<forall>y<t. L x j = L y j)"
      proof (intro allI impI)
        fix x y assume aa: "x < t" "y < t"
        have "\<forall>y \<in> cube 1 t. S y j = f j" using 2 Bf_props by simp
        then have "L y j = f j" using aa(2) ** **** lessThan_iff restrict_apply unfolding L_def by fastforce
        moreover from \<open>\<forall>y \<in> cube 1 t. S y j = f j \<close> have "L x j = f j" using aa(1) ** **** lessThan_iff restrict_apply unfolding L_def by fastforce
        ultimately show "L x j = L y j" by simp
      qed
      then show ?thesis by blast
    qed
  qed
  moreover have "(\<exists>j<n. \<forall>s<t. (L s j = s))"
  proof -
    obtain j where j_prop: "j \<in> B 0 \<and> j < n" using Bf_props by blast
    then have "\<forall>y \<in> cube 1 t. (S y) j = y 0" using Bf_props by auto
    then have "\<forall>s < t. L s j = s" using ** *** **** unfolding L_def by auto
    then show "(\<exists>j<n. \<forall>s<t. (L s j = s))" using j_prop by blast
  qed
  ultimately show "is_line (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) n t" unfolding L_def is_line_def by auto
qed

definition join
  where
    "join f g n m \<equiv> (\<lambda>x. if x \<in> {..<n} then f x else (if x \<in> {n..<n+m} then g (x - n) else undefined))"

lemma join_cubes: assumes "f \<in> cube n (t+1)" and "g \<in> cube m (t+1)" shows "join f g n m \<in> cube (n+m) (t+1)"
proof (unfold cube_def; intro PiE_I)
  fix i
  assume "i \<in> {..<n+m}"
  then consider "i < n" | "i \<ge> n \<and> i < n+m" by fastforce
  then show "join f g n m i \<in> {..<t + 1}"
  proof (cases)
    case 1
    then have "join f g n m i = f i" unfolding join_def by simp
    moreover have "f i \<in> {..<t+1}" using assms(1) 1 unfolding cube_def by blast
    ultimately show ?thesis by simp
  next
    case 2
    then have "join f g n m i = g (i - n)" unfolding join_def by simp
    moreover have "i - n \<in> {..<m}" using 2 by auto
    moreover have "g (i - n) \<in> {..<t+1}" using calculation(2) assms(2) unfolding cube_def by blast
    ultimately show ?thesis by simp
  qed
next
  fix i
  assume "i \<notin> {..<n+m}"
  then show "join f g n m i = undefined" unfolding join_def by simp
qed

lemma thm4_step: 
  fixes   r k
  assumes "t > 1"
      and "k \<ge> 2"
      and "hj t" 
      and "(\<And>r k'. k' \<le> k \<Longrightarrow> \<exists>M > 0. \<forall>M' \<ge> M. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. layered_subspace S k' M' t r \<chi>))" 
  shows   "(\<exists>M > 0. \<forall>M' \<ge> M. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. layered_subspace S (k + 1) M' t r \<chi>))"
proof-
  obtain m where m_props: "(m > 0 \<and> (\<forall>M' \<ge> m. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. layered_subspace S k M' t r \<chi>)))" using assms(4) by blast
  define s where "s \<equiv> r^((t + 1)^m)"
  obtain m' where m'_props: "(m' > 0 \<and> (\<forall>M' \<ge> m'. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<s::nat} \<longrightarrow> (\<exists>S. layered_subspace S 1 M' t s \<chi>)))" using assms(2) assms(4)[of "1" "s"] by auto 

  have "(\<exists>S. layered_subspace S (k + 1) (m + m') t r \<chi>)" if \<chi>_prop: "\<chi> \<in> cube (m + m') (t + 1) \<rightarrow>\<^sub>E {..<r}" for \<chi>
  proof -
    have "\<forall>\<chi>. \<chi> \<in> (cube m' (t + 1)) \<rightarrow>\<^sub>E {..<s::nat} \<longrightarrow> (\<exists>S. layered_subspace S 1 m' t s \<chi>)" using  m'_props by simp
    have "\<forall>\<chi>. \<chi> \<in> (cube m' (t + 1)) \<rightarrow>\<^sub>E {..<s::nat} \<longrightarrow> (\<exists>S. layered_subspace S 1 m' t s \<chi> \<and> is_line (\<lambda>s\<in>{..<t+1}. S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) m' (t+1))"
    proof(safe)
      fix \<chi>
      assume a: "\<chi> \<in> cube m' (t + 1) \<rightarrow>\<^sub>E {..<s}"
      then have "(\<exists>S. layered_subspace S 1 m' t s \<chi>)" 
        using \<open>\<forall>\<chi>. \<chi> \<in> cube m' (t + 1) \<rightarrow>\<^sub>E {..<s} \<longrightarrow> (\<exists>S. layered_subspace S 1 m' t s \<chi>)\<close> by presburger
      then obtain Sm' where "layered_subspace Sm' 1 m' t s \<chi>" by blast
      then have "is_subspace Sm' 1 m' (t+1)" unfolding layered_subspace_def by simp
      then have "is_line (\<lambda>s\<in>{..<t+1}. Sm' (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) m' (t + 1)" using dim1_subspace_is_line[of "t+1" "Sm'" "m'"] assms(1) by simp
      then show "\<exists>S. layered_subspace S 1 m' t s \<chi> \<and> is_line (\<lambda>s\<in>{..<t + 1}. S (SOME p. p \<in> cube 1 (t+1) \<and> p 0 = s)) m' (t + 1)" using \<open>layered_subspace Sm' 1 m' t s \<chi>\<close> by auto
    qed

    define \<chi>m' where "\<chi>m' \<equiv> (\<lambda>x \<in> cube m' (t+1). (\<lambda>y \<in> cube m (t + 1). \<chi> (join x y m' m)))"
    have A: "\<forall>x \<in> cube m' (t+1). \<forall>y \<in> cube m (t+1). \<chi> (join x y m' m) \<in> {..<r}"
    proof(safe)
      fix x y
      assume "x \<in> cube m' (t+1)" "y \<in> cube m (t+1)"
      then have "join x y m' m \<in> cube (m'+m) (t+1)" using join_cubes[of x m' t y m] by simp
      then show "\<chi> (join x y m' m) < r" using \<chi>_prop unfolding cube_def 
        by (metis PiE_mem add.commute lessThan_iff)
    qed
    have \<chi>m'_prop: "\<chi>m' \<in> cube m' (t+1) \<rightarrow>\<^sub>E cube m (t+1) \<rightarrow>\<^sub>E {..<r}"
    proof
      fix x assume xasm: "x \<in> cube m' (t+1)"
      show "\<chi>m' x \<in> cube m (t + 1) \<rightarrow>\<^sub>E {..<r}"
      proof
        fix y
        assume yasm: "y \<in> cube m (t + 1)"
        then have "\<chi>m' x y = \<chi> (join x y m' m)" using xasm unfolding \<chi>m'_def by simp
        then show "\<chi>m' x y \<in> {..<r}" using A xasm yasm by auto      
      next
        fix y
        assume "y \<notin> cube m (t+1)"
        then show "\<chi>m' x y = undefined" using xasm unfolding \<chi>m'_def by auto
      qed
    qed (auto simp: \<chi>m'_def)
    have "card (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) = (card {..<r}) ^ (card (cube m (t+1)))"  apply (subst card_PiE) unfolding cube_def apply (meson finite_PiE finite_lessThan)  
      using prod_constant by blast
    also have "... = r ^ (card (cube m (t+1)))" by simp
    also have "... = r ^ ((t+1)^m)" using cube_card unfolding cube_def by simp
    finally have "card (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) = r ^ ((t+1)^m)" .
    then have s_colored: "card (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) = s" unfolding s_def by simp


    show "\<exists>S. layered_subspace S (k + 1) (m + m') t r \<chi>" sorry
    


  qed
  
  show "\<exists>M>0. \<forall>M'\<ge>M. \<forall>\<chi>. \<chi> \<in> cube M' (t + 1) \<rightarrow>\<^sub>E {..<r} \<longrightarrow> (\<exists>S. layered_subspace S (k + 1) M' t r \<chi>)" sorry



qed



lemma hales_jewett: "\<forall>\<chi> r t. \<exists>N'. \<forall>N \<ge> N'. \<chi> \<in> (cube N t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. is_line L N t \<and> \<chi> ` (L ` {..<t}) = {c})"
  sorry
  
  

  
  

end