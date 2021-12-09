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

thm ex_bij_betw_nat_finite_1
lemma ex_bij_betw_nat_finite_2: "card A = n \<Longrightarrow> n > 0 \<Longrightarrow> \<exists>f. bij_betw f A {..<n}"
  by (metis atLeast0LessThan card_ge_0_finite ex_bij_betw_finite_nat)

lemma "f \<in> A \<rightarrow>\<^sub>E B \<longleftrightarrow> ((\<forall>a. (a \<in> A \<longrightarrow> f a \<in> B) \<and> (a \<notin> A \<longrightarrow> f a = undefined)))" 
  by auto

definition cube :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "cube n t \<equiv> {..<n} \<rightarrow>\<^sub>E {..<t}"



lemma cube_restrict: assumes "j < n" "y \<in> cube n t" shows "(\<lambda>g \<in> {..<j}. y g) \<in> cube j t" using assms unfolding cube_def by force
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

lemma is_line_elim_alt:
  assumes "is_line L n t" and "t > 1"
  shows "\<exists>BL. BL \<subseteq> {..<n} \<and> BL \<noteq> {} \<and> (\<forall>j \<in> {..<n} - BL. (\<forall>x<t. \<forall>y<t. L x j = L y j)) \<and> (\<forall>j \<in> BL. (\<forall>s<t. L s j = s))"
  using is_line_elim[of L n t]
  by (metis Diff_Diff_Int Int_Diff_Un Int_commute Un_Diff Un_empty_right Un_upper1 assms(1) assms(2))

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


definition shiftset :: "nat \<Rightarrow> nat set \<Rightarrow> nat set"
  where
  	"shiftset n S \<equiv> (\<lambda>a. a + n) ` S"


lemma shiftset_disjnt: "disjnt A B \<Longrightarrow> disjnt (shiftset n A) (shiftset n B)" 
  unfolding disjnt_def shiftset_def by force
lemma shiftset_disjoint_family: "disjoint_family_on B {..k} \<Longrightarrow> disjoint_family_on (\<lambda>i. shiftset n (B i)) {..k}" using shiftset_disjnt unfolding disjoint_family_on_def 
  by (meson disjnt_def)


lemma shiftset_altdef: "shiftset n S = (+) n ` S"
  by (auto simp: shiftset_def)
lemma shiftset_image_2:
  assumes "(\<Union>i\<in>{..k}. B i) = {..<n}"
  shows "(\<Union>i\<in>{..k}. shiftset m (B i)) = {m..<m+n}"
  using assms by (simp add: shiftset_altdef add.commute flip: image_UN atLeast0LessThan)

lemma shiftset_image:
  assumes "(\<Union>i\<in>{..k}. B i) = {..<n}"
  shows "(\<Union>i\<in>{..k}. shiftset m (B i)) = {m..<m+n}"
proof -
  have "(\<Union>i\<in>{..k}. shiftset m (B i)) = (\<Union>i\<in>{..k}. (+) m ` (B i))"
    unfolding shiftset_def by auto
  also have "\<dots> = (+) m ` (\<Union>i\<in>{..k}. (B i))"
    by blast
  also note assms
  also have "(+) m ` {..<n} = {m..<m+n}"
    by (simp add: add.commute lessThan_atLeast0)
  finally show ?thesis .
qed

(* lemma shiftset_image: assumes "(\<Union>i\<in>{..k}.(B i)) = {..<n}" shows "(\<Union>i\<in>{..k}. (shiftset m (B i))) = {m..<m+n}"
proof
  show "(\<Union>i\<le>k. shiftset m (B i)) \<subseteq> {m..<m + n}"
  proof 
    fix x assume "x \<in> (\<Union>i\<le>k. shiftset m (B i))"
    then obtain i where i_prop: "x \<in> shiftset m (B i) \<and> i\<le>k" by auto
    then obtain s where s_prop: "s \<in> B i \<and> x = m + s" unfolding shiftset_def sorry
    then have "s \<in> {..<n}" using assms i_prop by auto
    then show "x \<in> {m..<m+n}" using s_prop by simp
  qed

  show "{m..<m + n} \<subseteq> (\<Union>i\<le>k. shiftset m (B i))"
  proof
    fix x assume "x \<in> {m..<m+n}"
    then have "x - m \<in> {..<n}" by auto
    then obtain i where i_prop: "x - m \<in> B i \<and> i \<le> k" using assms by blast
    then have "x \<in> shiftset m (B i)" unfolding shiftset_def 
      using \<open>x \<in> {m..<m + n}\<close> by force
    then show "x \<in>  (\<Union>i\<le>k. shiftset m (B i))" using i_prop by auto
  qed
qed
*)


lemma union_shift: "(\<Union>i \<in> {a::nat..<a+b}. B (i - a)) = (\<Union>i \<in> {..<b::nat}. B i)"
proof-
  have   "(\<Union>i \<in> {a::nat..<a+b}. B (i - a)) = (\<Union>i \<in> (\<lambda>i. i - a) ` {a::nat..<a+b}. B i)" by blast
  also have "(\<lambda>i. i - a) ` {a::nat..<a+b} = {..<b::nat}"
    by (subst image_minus_const_atLeastLessThan_nat) auto
  finally show ?thesis .
qed
  

lemma split_cube: assumes "x \<in> cube (k+1) t" shows "(\<lambda>y \<in> {..<1}. x y) \<in> cube 1 t" and "(\<lambda>y \<in> {..<k}. x (y + 1)) \<in> cube k t"
  using assms unfolding cube_def by auto

term disjoint_family_on
term partition_on
definition is_subspace
  where "is_subspace S k n t \<equiv> (\<exists>B f. 
disjoint_family_on B {..k} \<and> \<Union>(B ` {..k}) = {..<n} \<and> ({} \<notin> B ` {..<k}) \<and> f \<in> (B k) \<rightarrow>\<^sub>E {..<t} \<and> S \<in> (cube k t) \<rightarrow>\<^sub>E (cube n t) \<and> (\<forall>y \<in> cube k t. (\<forall>i \<in> B k. S y i = f i) \<and> (\<forall>j<k. \<forall>i \<in> B j. (S y) i = y j)))"

lemma subspace_inj_on_cube: assumes "is_subspace S k n t" shows "inj_on S (cube k t)"
proof 
	fix x y
	assume a: "x \<in> cube k t" "y \<in> cube k t" "S x = S y"
	from assms obtain B f where Bf_props: "disjoint_family_on B {..k} \<and> \<Union>(B ` {..k}) = {..<n} \<and> ({} \<notin> B ` {..<k}) \<and> f \<in> (B k) \<rightarrow>\<^sub>E {..<t} \<and> S \<in> (cube k t) \<rightarrow>\<^sub>E (cube n t) \<and> (\<forall>y \<in> cube k t. (\<forall>i \<in> B k. S y i = f i) \<and> (\<forall>j<k. \<forall>i \<in> B j. (S y) i = y j))" unfolding is_subspace_def by auto
	have "\<forall>i<k. x i = y i"
	proof (intro allI impI)
		fix j assume "j < k"
	  then have "B j \<noteq> {}" using Bf_props by auto
	  then obtain i where i_prop: "i \<in> B j" by blast
	  then have "y j = S y i" using Bf_props a(2) \<open>j < k\<close> by auto
	  also have " ... = S x i" using a by simp
	  also have " ... = x j" using Bf_props a(1) \<open>j < k\<close> i_prop by blast
	  finally show "x j = y j" by simp
	qed
	then show "x = y" using a(1,2) unfolding cube_def by (meson PiE_ext lessThan_iff)
qed
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

lemma classes_subset_cube: "classes n t i \<subseteq> cube n (t+1)" unfolding classes_def by blast

definition layered_subspace
  where "layered_subspace S k n t r \<chi> \<equiv> (is_subspace S k n (t + 1) \<and> (\<forall>i \<in> {..k}. \<exists>c<r. \<forall>x \<in> classes k t i. \<chi> (S x) = c))"

lemma layered_eq_classes: assumes"layered_subspace S k n t r \<chi>" shows "\<forall>i \<in> {..k}. \<forall>x \<in> classes k t i. \<forall>y \<in> classes k t i. \<chi> (S x) = \<chi> (S y)" 
  using assms unfolding layered_subspace_def by metis

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

lemma "inj_on f A \<Longrightarrow> b \<in> f ` A \<Longrightarrow> (\<exists>!a. a \<in> A \<and> f a = b)" 
  using inj_onD by fastforce 

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
  where "hj r t \<equiv> (\<exists>N>0. \<forall>N' \<ge> N. \<forall>\<chi>. \<chi> \<in> (cube N' t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. is_line L N' t \<and> \<chi> ` (L ` {..<t}) = {c}))"

definition lhj
  where "lhj r t k \<equiv> (\<exists>M > 0. \<forall>M' \<ge> M. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. layered_subspace S k M' t r \<chi>))"


text \<open>Base case of Theorem 4\<close>
lemma thm4_k_1: 
  fixes   r t
  assumes "t > 1"
    and "\<And>r'. hj r' t" 
  shows "lhj r t 1"

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
  then show ?thesis using N_def unfolding layered_subspace_def lhj_def by blast
qed


text \<open>Claiming k-dimensional subspaces of (cube n t) are isomorphic to (cube k t)\<close>
definition is_subspace_alt
  where "is_subspace_alt S k n t \<equiv> (\<exists>\<phi>. k \<le> n \<and> bij_betw \<phi> S (cube k t))"

thm "less_induct"
thm "nat_induct"
lemma nat_01_induct [case_names 0 1 SSuc induct_type nat]: 
  fixes n
  assumes "P (0::nat)" and "P 1" and "(\<And>k. k \<ge> ((Suc 0)) \<Longrightarrow> P k \<Longrightarrow> P (Suc k))" shows "P n"
  using assms by (induction n; auto; metis less_Suc0 not_le)



text \<open>Some useful facts about 1-dimensional subspaces.\<close>
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

text \<open>Useful properties about cubes.\<close>
lemma cube_props:
  shows "\<forall>s \<in> {..<t}. \<exists>p \<in> cube 1 t. p 0 = s"
    and "\<forall>s \<in> {..<t}. (SOME p. p \<in> cube 1 t \<and> p 0 = s) 0 = s"
    and "\<forall>s \<in> {..<t}. (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) s = (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) ((SOME p. p \<in> cube 1 t \<and> p 0 = s) 0)"
    and "\<forall>s \<in> {..<t}. (SOME p. p \<in> cube 1 t \<and> p 0 = s) \<in> cube 1 t"
proof -
  show 1: "\<forall>s \<in> {..<t}. \<exists>p \<in> cube 1 t. p 0 = s" unfolding cube_def by (simp add: fun_ex)
  show 2: "\<forall>s \<in> {..<t}. (SOME p. p \<in> cube 1 t \<and> p 0 = s) 0 = s"
  proof(safe)
    fix s
    assume "s < t"
    then have "\<exists>p \<in> cube 1 t. p 0 = s" 
      using \<open>\<forall>s\<in>{..<t}. \<exists>p\<in>cube 1 t. p 0 = s\<close> by blast
    then show "(SOME p. p \<in> cube 1 t \<and>  p 0 = s) 0 = s" using someI_ex[of "\<lambda>x. x \<in> cube 1 t \<and> x 0 = s"] by auto
  qed

  show 3: "\<forall>s \<in> {..<t}. (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) s = (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) ((SOME p. p \<in> cube 1 t \<and> p 0 = s) 0)" using 2 by simp
  show 4: "\<forall>s \<in> {..<t}. (SOME p. p \<in> cube 1 t \<and> p 0 = s) \<in> cube 1 t" using 1 by (metis (mono_tags, lifting) verit_sko_ex')
qed

lemma dim1_subspace_is_line: 
  assumes "t > 1" 
    and "is_subspace S 1 n t" 
  shows   "is_line (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) n t"
proof-

  define L where "L \<equiv> (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s))"
  have "{..1} = {0::nat, 1}" by auto
  obtain B f where Bf_props: "disjoint_family_on B {..1::nat} \<and> \<Union>(B ` {..1::nat}) = {..<n} \<and> ({} \<notin> B ` {..<1::nat}) \<and> f \<in> (B 1) \<rightarrow>\<^sub>E {..<t} \<and> S \<in> (cube 1 t) \<rightarrow>\<^sub>E (cube n t) \<and> (\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. S y i = f i) \<and> (\<forall>j<1. \<forall>i \<in> B j. (S y) i = y j))" using assms(2) unfolding is_subspace_def by auto
  then have 1: "B 0 \<union> B 1 = {..<n} \<and> B 0 \<inter> B 1 = {}" using dim1_subspace_elims(1, 2)[of "B" "n" "f" "t" "S" ] by simp

  have "L \<in> {..<t} \<rightarrow>\<^sub>E cube n t"
  proof
    fix s assume a: "s \<in> {..<t}"
    then have "L s = S (SOME p. p\<in>cube 1 t \<and> p 0 = s)" unfolding L_def by simp
    moreover have "(SOME p. p\<in>cube 1 t \<and> p 0 = s) \<in> cube 1 t" using cube_props(1) a 
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
        then show "L s j = s" using \<open>s < t\<close> cube_props(2,4)  unfolding L_def by auto
      qed
      then show ?thesis by blast
    next
      case 2
      have "(\<forall>x<t. \<forall>y<t. L x j = L y j)"
      proof (intro allI impI)
        fix x y assume aa: "x < t" "y < t"
        have "\<forall>y \<in> cube 1 t. S y j = f j" using 2 Bf_props by simp
        then have "L y j = f j" using aa(2) cube_props(2,4) lessThan_iff restrict_apply unfolding L_def by fastforce
        moreover from \<open>\<forall>y \<in> cube 1 t. S y j = f j \<close> have "L x j = f j" using aa(1) cube_props(2,4) lessThan_iff restrict_apply unfolding L_def by fastforce
        ultimately show "L x j = L y j" by simp
      qed
      then show ?thesis by blast
    qed
  qed
  moreover have "(\<exists>j<n. \<forall>s<t. (L s j = s))"
  proof -
    obtain j where j_prop: "j \<in> B 0 \<and> j < n" using Bf_props by blast
    then have "\<forall>y \<in> cube 1 t. (S y) j = y 0" using Bf_props by auto
    then have "\<forall>s < t. L s j = s" using cube_props(2,4) unfolding L_def by auto
    then show "(\<exists>j<n. \<forall>s<t. (L s j = s))" using j_prop by blast
  qed
  ultimately show "is_line (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) n t" unfolding L_def is_line_def by auto
qed


lemma dim1_layered_subspace_as_line:
  assumes "t > 1"
    and "layered_subspace S 1 n t r \<chi>"
  shows "\<exists>c1 c2. c1<r \<and> c2<r \<and> (\<forall>s<t. \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) = c1) \<and> \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = t)) = c2"
  sorry

lemma dim1_layered_subspace_mono_line: assumes "t > 1" and "layered_subspace S 1 n t r \<chi>"
  shows "\<forall>s<t. \<forall>l<t.  \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) =  \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = l)) \<and>  \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) < r"
  using dim1_layered_subspace_as_line[of t S n r \<chi>] assms by auto



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

lemma subspace_elems_embed: assumes "is_subspace S k n t"
  shows "S ` (cube k t) \<subseteq> cube n t"
proof 
  fix x assume a: "x \<in> S ` cube k t"
  then have "\<exists>y \<in> cube k t. S y = x" by auto
  then obtain y where y_prop: "y \<in> cube k t \<and> S y = x" by blast

  show "x \<in> cube n t" using a assms(1) y_prop unfolding is_subspace_def cube_def by blast

qed


text \<open>The induction step of theorem 4. Heart of the proof\<close>
text \<open>
Proof sketch/idea:
  * we prove lhj r t (k+1) for all r at once. That means we assume hj r t for all r, and lhj r t k' for all r (and all dimensions k' less than k+1)
  * remember: hj -> statement about monochromatic lines, lhj -> statement about layered subspaces (k-dimensional)
  * core idea: to construct (k+1)-dimensional subspace, use (by induction) k-dimensional subspace and (by assumption) 1-dimensional subspace (line) in some natural way (ensuring the colorings satisfy the requisite conditions)

In detail:
  - let \<chi> be an r-coloring, for which we wish to show that there exists a layered (k+1)-dimensional subspace.
  - (SECTION 1) by our assumptions, we can obtain a layered k-dimensional subspace S (w.r.t. r-colorings) and a layered line Sm' (w.r.t. to s-colorings, where s=f(r) is constructed from r to facilitate our main proof; details irrelevant)
  - let m be the dimension of the cube in which the layered k-dimensional subspace S exists
  - let m' be the dimension of the cube in which the layered line Sm' exists
  - we claim that the layered (k+1)-dimensional subspace we are looking for exists in the (m+m')-dimensional cube
    # concretely, we construct these (m+m')-dimensional elements (i.e. tuples) by setting the first m' coordinates to points on the line, and the last m coordinates to points on the subspace.
    # (SECTION 2) this construction yields a subspace (i.e. satisfying the subspace properties). We call this T''. 
    # We prove it is a subspace in SECTION 3. In SECTION 4, we show it is layered.
\<close>
lemma thm4_step: 
  fixes   r k
  assumes "t > 1"
    and "k \<ge> 1"
    and "\<And>r'. hj r' t" 
    and "(\<And>r k'. k' \<le> k \<Longrightarrow> lhj r t k')" 
    and "r > 0"
  shows   "lhj r t (k+1)"
proof-
  obtain m where m_props: "(m > 0 \<and> (\<forall>M' \<ge> m. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. layered_subspace S k M' t r \<chi>)))" using assms(4)[of "k" "r"] unfolding lhj_def  by blast
  define s where "s \<equiv> r^((t + 1)^m)"
  obtain m' where m'_props: "(m' > 0 \<and> (\<forall>M' \<ge> m'. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<s::nat} \<longrightarrow> (\<exists>S. layered_subspace S 1 M' t s \<chi>)))" using assms(2) assms(4)[of "1" "s"] unfolding lhj_def by auto 

  have "(\<exists>S. layered_subspace S (k + 1) (m + m') t r \<chi>)" if \<chi>_prop: "\<chi> \<in> cube (m + m') (t + 1) \<rightarrow>\<^sub>E {..<r}" for \<chi>
  proof -
    have "\<forall>\<chi>. \<chi> \<in> (cube m' (t + 1)) \<rightarrow>\<^sub>E {..<s::nat} \<longrightarrow> (\<exists>S. layered_subspace S 1 m' t s \<chi>)" using  m'_props by simp
    have line_subspace_s: "\<forall>\<chi>. \<chi> \<in> (cube m' (t + 1)) \<rightarrow>\<^sub>E {..<s::nat} \<longrightarrow> (\<exists>S. layered_subspace S 1 m' t s \<chi> \<and> is_line (\<lambda>s\<in>{..<t+1}. S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) m' (t+1))"
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

(** SECTION 1: OBTAINING THE SUBSPACES, CONSTRUCTING THE COLORINGS, AND PROVING RELEVANT FACTS **)

(* \<chi>m' is \<chi>* in the book, an s-coloring; see s_colored a couple of lines below *)
    define \<chi>m' where "\<chi>m' \<equiv> (\<lambda>x \<in> cube m' (t+1). (\<lambda>y \<in> cube m (t + 1). \<chi> (join x y m' m)))"
    have A: "\<forall>x \<in> cube m' (t+1). \<forall>y \<in> cube m (t+1). \<chi> (join x y m' m) \<in> {..<r}"
    proof(safe)
      fix x y
      assume "x \<in> cube m' (t+1)" "y \<in> cube m (t+1)"
      then have "join x y m' m \<in> cube (m'+m) (t+1)" using join_cubes[of x m' t y m] by simp
      then show "\<chi> (join x y m' m) < r" using \<chi>_prop unfolding cube_def 
        by (metis PiE_mem add.commute lessThan_iff)
    qed
    have \<chi>m'_prop: "\<chi>m' \<in> cube m' (t+1) \<rightarrow>\<^sub>E cube m (t+1) \<rightarrow>\<^sub>E {..<r}" using A by (auto simp: \<chi>m'_def)

    have "card (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) = (card {..<r}) ^ (card (cube m (t+1)))"  apply (subst card_PiE) unfolding cube_def apply (meson finite_PiE finite_lessThan)  
      using prod_constant by blast
    also have "... = r ^ (card (cube m (t+1)))" by simp
    also have "... = r ^ ((t+1)^m)" using cube_card unfolding cube_def by simp
    finally have "card (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) = r ^ ((t+1)^m)" .
    then have s_colored: "card (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) = s" unfolding s_def by simp
    have "s > 0" using assms(5) unfolding s_def by simp
    then obtain \<phi> where \<phi>_prop: "bij_betw \<phi> (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) {..<s}" using ex_bij_betw_nat_finite_2[of "cube m (t+1) \<rightarrow>\<^sub>E {..<r}" "s"] s_colored by blast
    define \<chi>m'_s where "\<chi>m'_s \<equiv> (\<lambda>x\<in>cube m' (t+1). \<phi> (\<chi>m' x))"
    have "\<chi>m'_s \<in> cube m' (t+1) \<rightarrow>\<^sub>E {..<s}"
    proof
      fix x assume a: "x \<in> cube m' (t+1)"
      then have "\<chi>m'_s x = \<phi> (\<chi>m' x)" unfolding \<chi>m'_s_def by simp
      moreover have "\<chi>m' x \<in> (cube m (t+1) \<rightarrow>\<^sub>E {..<r})" using a \<chi>m'_def \<chi>m'_prop unfolding \<chi>m'_def by blast
      moreover have "\<phi> (\<chi>m' x) \<in> {..<s}" using \<phi>_prop calculation(2) unfolding bij_betw_def by blast
      ultimately show "\<chi>m'_s x \<in> {..<s}" by auto
    qed (auto simp: \<chi>m'_s_def)
      (* Sm' is the layered line which we obtain from the monochromatic line guaranteed to exist in the assumption hj s t *)
    then obtain Sm' where Sm'_prop: "layered_subspace Sm' 1 m' t s \<chi>m'_s" using line_subspace_s by blast
    define Sm'_line where "Sm'_line \<equiv> (\<lambda>s\<in>{..<t+1}. Sm' (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s))"
    have Sm'_line_base_prop: "\<forall>s \<in> {..<t+1}. Sm'_line s \<in> cube m' (t+1)" using assms(1) dim1_subspace_is_line[of "t+1" "Sm'" "m'"] Sm'_prop aux2[of Sm'_line m' "t+1"] unfolding layered_subspace_def Sm'_line_def by auto

(* \<chi>m is \<chi>** in book, an r-coloring *)
    define \<chi>m where "\<chi>m \<equiv> (\<lambda>y\<in>cube m (t+1). \<chi> (join (Sm'_line 0) y m' m))"
    have "\<chi>m \<in> (cube m (t + 1)) \<rightarrow>\<^sub>E {..<r::nat}"
    proof
    	fix x assume a: "x \<in> cube m (t+1)"
    	then have "\<chi>m x = \<chi> (join (Sm'_line 0) x m' m)" unfolding \<chi>m_def by simp
    	moreover have "Sm'_line 0 = Sm' (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = 0)" using Sm'_prop assms(1) unfolding Sm'_line_def by simp
    	moreover have "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = 0) \<in> cube 1 (t+1)" using cube_props(4)[of "t+1"] using assms(1) by auto 
    	moreover have "Sm' \<in> cube 1 (t+1) \<rightarrow>\<^sub>E cube m' (t+1)" using Sm'_prop unfolding layered_subspace_def is_subspace_def by blast
    	moreover have "Sm' (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = 0) \<in> cube m' (t+1)" using calculation (3,4) unfolding cube_def by auto
    	moreover have "join (Sm'_line 0) x m' m \<in> cube (m' + m) (t+1)" using join_cubes a calculation(2, 5) by auto
    	ultimately show "\<chi>m x \<in> {..<r}" using A a by fastforce
    qed (auto simp: \<chi>m_def)
      (* S is the k-dimensional layered subspace as a consequence of the IH. Note the coloring is \<chi>m, an r-coloring *)
    then obtain S where S_prop: "layered_subspace S k m t r \<chi>m" using assms(4) m_props by blast
        (* Sm'_line i returns the i-th point of the line *)


(* ------------------------------------------------------------------------------------------------------------------------------ *)


(** SECTION 2: CONSTRUCTING THE GOAL SUBSPACE T'' **)

(* T is the set as defined in the book; it represents the (k+1)-dim subspace as a set. In this construction, subspaces are functions whose image is a set such as T. See below \<rightarrow> im_T''_eq_T *)
    define T where "T \<equiv> {join (Sm'_line i) s m' m | i s . i \<in> {..<t+1} \<and> s \<in> S ` (cube k (t+1))}" (* x\<^sub>is *)
    define T' where "T' \<equiv> (\<lambda>x \<in> cube 1 (t+1). \<lambda>y \<in> cube k (t+1). join (Sm'_line (x 0)) (S y) m' m)"
    have T'_prop: "T' \<in> cube 1 (t+1) \<rightarrow>\<^sub>E cube k (t+1) \<rightarrow>\<^sub>E cube (m' + m) (t+1)"
    proof
      fix x assume a: "x \<in> cube 1 (t+1)"
      show "T' x \<in> cube k (t + 1) \<rightarrow>\<^sub>E cube (m' + m) (t + 1)"
      proof
        fix y assume b: "y \<in> cube k (t+1)"
        then have "T' x y = join (Sm'_line (x 0)) (S y) m' m" using a unfolding T'_def by simp
        moreover have "Sm'_line (x 0) \<in> cube m' (t+1)" using a Sm'_line_base_prop unfolding cube_def by blast
        moreover have "S y \<in> cube m (t+1)" using subspace_elems_embed[of "S" "k" "m" "t+1"] S_prop b  unfolding layered_subspace_def by blast
        ultimately show "T' x y \<in> cube (m' + m) (t + 1)" using join_cubes by presburger
      next
      qed (unfold T'_def; use a in simp)
   	qed (auto simp: T'_def)

   	define T'' where "T'' \<equiv> (\<lambda>x \<in> cube (k + 1) (t+1). T' (\<lambda>y \<in> {..<1}. x y) (\<lambda>y \<in> {..<k}. x (y + 1)))"
   	have T''_prop: "T'' \<in> cube (k+1) (t+1) \<rightarrow>\<^sub>E cube (m'+m) (t+1)"
   	proof
   	  fix x assume a: "x \<in> cube (k+1) (t+1)"
   	  then have "T'' x = T' (\<lambda>y \<in> {..<1}. x y) (\<lambda>y \<in> {..<k}. x (y + 1))" unfolding T''_def by auto
   	  moreover have "(\<lambda>y \<in> {..<1}. x y) \<in> cube 1 (t+1)" using a unfolding cube_def by auto
   	  moreover have "(\<lambda>y \<in> {..<k}. x (y + 1)) \<in> cube k (t+1)" using a unfolding cube_def by auto
   	  moreover have "T' (\<lambda>y \<in> {..<1}. x y) (\<lambda>y \<in> {..<k}. x (y + 1)) \<in> cube (m' + m) (t+1)" using T'_prop calculation unfolding T'_def by blast
   	  ultimately show "T'' x \<in> cube (m' + m) (t+1)" by argo
   	qed (auto simp: T''_def)

   	have im_T''_eq_T: "T'' ` cube (k+1) (t+1) = T"
   	proof
   	  show "T'' ` cube (k + 1) (t + 1) \<subseteq> T"
   	  proof
   	    fix x assume "x \<in> T'' ` cube (k+1) (t+1)"
   	    then obtain y where y_prop: "y \<in> cube (k+1) (t+1) \<and> x = T'' y" by blast
   	    then have "T'' y = T' (\<lambda>i \<in> {..<1}. y i) (\<lambda>i \<in> {..<k}. y (i + 1))" unfolding T''_def by simp
   	    moreover have "(\<lambda>i \<in> {..<1}. y i) \<in> cube 1 (t+1)" using y_prop unfolding cube_def by auto
   	    moreover have "(\<lambda>i \<in> {..<k}. y (i + 1)) \<in> cube k (t+1)" using y_prop unfolding cube_def by auto
   	    moreover have " T' (\<lambda>i \<in> {..<1}. y i) (\<lambda>i \<in> {..<k}. y (i + 1)) = join (Sm'_line ((\<lambda>i \<in> {..<1}. y i) 0)) (S (\<lambda>i \<in> {..<k}. y (i + 1))) m' m" using calculation unfolding T'_def by auto
   	    ultimately have *: "T'' y = join (Sm'_line ((\<lambda>i \<in> {..<1}. y i) 0)) (S (\<lambda>i \<in> {..<k}. y (i + 1))) m' m" by simp

   	    have "(\<lambda>i \<in> {..<1}. y i) 0 \<in> {..<t+1}" using y_prop unfolding cube_def by auto
   	    moreover have "S (\<lambda>i \<in> {..<k}. y (i + 1)) \<in> S ` (cube k (t+1))" 
   	      using \<open>(\<lambda>i\<in>{..<k}. y (i + 1)) \<in> cube k (t + 1)\<close> by blast
   	    ultimately have "T'' y \<in> T" using * unfolding T_def by blast
   	    then show "x \<in> T" using y_prop by simp
   	  qed

   	  show "T \<subseteq> T'' ` cube (k + 1) (t + 1)" 
   	  proof
   	    fix x assume "x \<in> T"
   	    then obtain i sx sxinv where isx_prop: "x = join (Sm'_line i) sx m' m \<and> i \<in> {..<t+1} \<and> sx \<in> S ` (cube k (t+1)) \<and> sxinv \<in> cube k (t+1) \<and> S sxinv = sx" unfolding T_def by blast
   	    let ?f1 = "(\<lambda>j \<in> {..<1::nat}. i)"
   	    let ?f2 = "sxinv"
   	    have "?f1 \<in> cube 1 (t+1)" using isx_prop unfolding cube_def by simp
   	    moreover have "?f2 \<in> cube k (t+1)" using isx_prop by blast
   	    moreover have "x = join (Sm'_line (?f1 0)) (S ?f2) m' m" by (simp add: isx_prop)
   	    ultimately have *: "x = T' ?f1 ?f2" unfolding T'_def by simp 

   	    define f where "f \<equiv> (\<lambda>j \<in> {1..<k+1}. ?f2 (j - 1))(0:=i)"
   	    have "f \<in> cube (k+1) (t+1)"
   	    proof (unfold cube_def; intro PiE_I)
   	      fix j assume "j \<in> {..<k+1}"
   	      then consider "j = 0" | "j \<in> {1..<k+1}" by fastforce
   	      then show "f j \<in> {..<t+1}"
   	      proof (cases)
   	        case 1
   	        then have "f j = i" unfolding f_def by simp
   	        then show ?thesis using isx_prop by simp
   	      next
   	        case 2
   	        then have "j - 1 \<in> {..<k}" by auto
   	        moreover have "f j = ?f2 (j - 1)" using 2 unfolding f_def by simp
   	        moreover have "?f2 (j - 1) \<in> {..<t+1}" using calculation(1) isx_prop unfolding cube_def by blast
   	        ultimately show ?thesis by simp
   	      qed
   	    qed (auto simp: f_def)
   	    have "?f1 = (\<lambda>j \<in> {..<1}. f j)" unfolding f_def using isx_prop by auto
   	    moreover have "?f2 = (\<lambda>j\<in>{..<k}. f (j+1))" using calculation isx_prop unfolding cube_def f_def by fastforce
   	    ultimately have "T' ?f1 ?f2 = T'' f" using \<open>f \<in> cube (k+1) (t+1)\<close> unfolding T''_def by simp
   	    then show "x \<in> T'' ` cube (k + 1) (t + 1)" using * 
   	      using \<open>f \<in> cube (k + 1) (t + 1)\<close> by blast
   	  qed


   	qed
   	have "T \<subseteq> cube (m' + m) (t+1)"
   	proof
   	  fix x assume a: "x\<in>T"
   	  then obtain i sx where isx_props: "x = join (Sm'_line i) sx m' m \<and> i \<in> {..<t+1} \<and> sx \<in> S ` (cube k (t+1))" unfolding T_def by blast
   	  then have "Sm'_line i \<in> cube m' (t+1)" using Sm'_line_base_prop by blast
   	  moreover have "sx \<in> cube m (t+1)" using subspace_elems_embed[of "S" "k" "m" "t+1"] S_prop isx_props unfolding layered_subspace_def by blast
   	  ultimately show "x \<in> cube (m' + m) (t+1)" using join_cubes[of "Sm'_line i" "m'" "t" sx m] isx_props by simp 
   	qed

   	




(* ------------------------------------------------------------------------------------------------------------------------------ *)

(** SECTION 3: PROVING THAT T'' IS A SUBSPACE **)

(* To prove entities are subspaces, we have to provide the B and f satisfying the subspace properties. We construct BT and fT from BS, fS and BL, fL, which correspond to the k-dim subspace S and the 1-dimensional subspace (~ line) Sm', respectively. *)
   	obtain BS fS where BfS_props: "disjoint_family_on BS {..k}" "\<Union>(BS ` {..k}) = {..<m}" "({} \<notin> BS ` {..<k})" " fS \<in> (BS k) \<rightarrow>\<^sub>E {..<t+1}" "S \<in> (cube k (t+1)) \<rightarrow>\<^sub>E (cube m (t+1)) " "(\<forall>y \<in> cube k (t+1). (\<forall>i \<in> BS k. S y i = fS i) \<and> (\<forall>j<k. \<forall>i \<in> BS j. (S y) i = y j))" using S_prop unfolding layered_subspace_def is_subspace_def by auto

   	obtain BL fL where BfL_props: "disjoint_family_on BL {..1}" "\<Union>(BL ` {..1}) = {..<m'}"  "({} \<notin> BL ` {..<1})" "fL \<in> (BL 1) \<rightarrow>\<^sub>E {..<t+1}" "Sm' \<in> (cube 1 (t+1)) \<rightarrow>\<^sub>E (cube m' (t+1))" "(\<forall>y \<in> cube 1 (t+1). (\<forall>i \<in> BL 1. Sm' y i = fL i) \<and> (\<forall>j<1. \<forall>i \<in> BL j. (Sm' y) i = y j))" using Sm'_prop unfolding layered_subspace_def is_subspace_def by auto

   	define Bstat where "Bstat \<equiv> shiftset m' (BS k) \<union> BL 1"
   	define Bvar where "Bvar \<equiv> (\<lambda>i::nat. (if i = 0 then BL 0 else shiftset m' (BS (i - 1))))"
   	define BT where "BT \<equiv> (\<lambda>i \<in> {..<k+1}. Bvar i)((k+1):=Bstat)"
   	define fT where "fT \<equiv> (\<lambda>x. (if x \<in> BL 1 then fL x else (if x \<in> shiftset m' (BS k) then fS (x - m') else undefined)))"


(* useful facts *)
   	have fax1: "shiftset m' (BS k) \<inter> BL 1 = {}"  using BfL_props BfS_props unfolding shiftset_def by auto
    have fax2: "BL 0 \<inter> (\<Union>i\<in>{..<k}. shiftset m' (BS i)) = {}" using BfL_props BfS_props unfolding shiftset_def by auto
    have fax3: "\<forall>i \<in> {..<k}. BL 0 \<inter> shiftset m' (BS i) = {}" using BfL_props BfS_props unfolding shiftset_def by auto
    have fax4: "\<forall>i \<in> {..<k+1}. \<forall>j \<in> {..<k+1}. i \<noteq> j \<longrightarrow> shiftset m' (BS i) \<inter> shiftset m' (BS j) = {}" using shiftset_disjoint_family[of BS k] BfS_props unfolding disjoint_family_on_def by simp 
    have fax5: "\<forall>i \<in> {..<k+1}. Bvar i \<inter> Bstat = {}"
  	proof
  	  fix i assume a: "i \<in> {..<k+1}"
  	  show "Bvar i \<inter> Bstat = {}"
  	  proof (cases i)
  	    case 0
  	    then have "Bvar i = BL 0" unfolding Bvar_def by simp
  	    moreover have "BL 0 \<inter> BL 1 = {}" using BfL_props unfolding disjoint_family_on_def by simp
  	    moreover have "shiftset m' (BS k) \<inter> BL 0 = {}" using BfL_props BfS_props unfolding shiftset_def by auto
  	    ultimately show ?thesis unfolding Bstat_def by blast
  	  next
  	    case (Suc nat)
  	    then have "Bvar i = shiftset m' (BS nat)" unfolding Bvar_def by simp
  	    moreover have "shiftset m' (BS nat) \<inter> BL 1 = {}" using BfS_props BfL_props a Suc unfolding shiftset_def by auto
  	    moreover have "shiftset m' (BS nat) \<inter> shiftset m' (BS k) = {}" using a Suc fax4 by simp
  	    ultimately show ?thesis unfolding Bstat_def by blast
  	  qed
  	qed

  	have shiftsetnotempty: "\<forall>n i. BS i \<noteq> {} \<longrightarrow> shiftset n (BS i) \<noteq> {}" unfolding shiftset_def by blast

(* facts F1 ... F5 are the disjuncts in the subspace definition *)  
    have "Bvar ` {..<k+1} = BL ` {..<1} \<union> Bvar ` {1..<k+1}" unfolding Bvar_def by force
    also have " ... = BL ` {..<1} \<union> {shiftset m' (BS i) | i . i \<in> {..<k}} " unfolding Bvar_def by fastforce  
    moreover have "{} \<notin> BL ` {..<1}" using BfL_props by auto
    moreover have "{} \<notin> {shiftset m' (BS i) | i . i \<in> {..<k}}" using BfS_props shiftsetnotempty 
      by (smt (verit, best) image_eqI mem_Collect_eq)
    ultimately have "{} \<notin> Bvar ` {..<k+1}" by simp
    then have F1: "{} \<notin> BT ` {..<k+1}" unfolding BT_def by simp

    have F2_aux: "disjoint_family_on Bvar {..<k+1}"
    proof (unfold disjoint_family_on_def; safe)
      fix m n x assume a: "m < k + 1" "n < k + 1" "m \<noteq> n" "x \<in> Bvar m" "x \<in> Bvar n"
      show "x \<in> {}"
      proof (cases "n")
        case 0
        then show ?thesis using a unfolding Bvar_def 
          by (metis IntI fax3 lessThan_iff less_diff_conv2 less_one not_le)
      next
        case (Suc nnat)
        then have *: "n = Suc nnat" by simp
        then show ?thesis 
        proof (cases m)
          case 0
          then show ?thesis using a fax3 unfolding Bvar_def by auto
        next
          case (Suc mnat)
          then show ?thesis using a fax4  * unfolding Bvar_def by fastforce
        qed
      qed
  	qed

  	have F2: "disjoint_family_on BT {..k+1}"
  	proof
  	  fix m n assume a: "m\<in>{..k+1}" "n\<in>{..k+1}" "m \<noteq> n"
  	  (* have False if "x \<in> BT m \<inter> BT n" for x *)
      
  	  have "\<forall>x. x \<in> BT m \<inter> BT n \<longrightarrow> x \<in> {}" 
  	  proof (intro allI impI)
  	    fix x assume b: "x \<in> BT m \<inter> BT n"
  	    have "m < k + 1 \<and> n < k + 1 \<or> m = k + 1 \<and> n = k + 1 \<or> m < k + 1 \<and> n = k + 1 \<or> m = k + 1 \<and> n < k + 1" using a le_eq_less_or_eq by auto
  	    then show "x \<in> {}"
  	    proof (elim disjE)
  	      assume c: "m < k + 1 \<and> n < k + 1"
  	      then have "BT m = Bvar m \<and> BT n = Bvar n" unfolding BT_def by simp
  	      then show "x \<in> {}" using a b fax4 unfolding Bvar_def 
  	        by (metis \<open>BT m = Bvar m \<and> BT n = Bvar n\<close> \<open>disjoint_family_on Bvar {..<k + 1}\<close> c disjoint_family_on_def lessThan_iff)
  	    qed (use a b fax5 in \<open>auto simp: BT_def\<close>)
  	  qed
  	  then show "BT m \<inter> BT n = {}" by auto
  	qed


  	have F3: "\<Union>(BT ` {..k+1}) = {..<m' + m}"
  	proof 
  	  show "\<Union> (BT ` {..k + 1}) \<subseteq> {..<m' + m}"
  	  proof
  	    fix x assume "x \<in> \<Union> (BT ` {..k + 1})"
  	    then obtain i where i_prop: "i \<in> {..k+1} \<and> x \<in> BT i" by blast
  	    then consider "i = k +1" | "i \<in> {..<k+1}" by fastforce
  	    then show "x \<in> {..<m' + m}"
  	    proof (cases)
  	      case 1
  	      then have "x \<in> Bstat" using i_prop unfolding BT_def by simp
  	      then have "x \<in> BL 1 \<or> x \<in> shiftset m' (BS k)" unfolding Bstat_def by blast
  	      then have "x \<in> {..<m'} \<or> x \<in> {m'..<m'+m}" using BfL_props shiftset_image[of BS k m m'] 
  	        by (metis BfS_props(2) UN_iff atMost_iff order_refl) 
  	      then show ?thesis by auto
  	    next
  	      case 2
  	      then have "x \<in> Bvar i" using i_prop unfolding BT_def by simp
  	      then have "x \<in> BL 0 \<or> x \<in> shiftset m' (BS (i - 1))" unfolding Bvar_def by metis
  	      then show ?thesis
  	      proof (elim disjE)
  	        assume "x \<in> BL 0"
  	        then have "x \<in> {..<m'}" using BfL_props by auto
  	        then show "x \<in> {..<m' + m}" by simp
  	      next
  	        assume a: "x \<in> shiftset m' (BS (i - 1))"
  	        then have "i - 1 \<le> k" 
  	          by (meson atMost_iff i_prop le_diff_conv) 
  	        then have "shiftset m' (BS (i - 1)) \<subseteq> {m'..<m'+m}" using shiftset_image[of BS k m m'] BfS_props by auto
  	        then show "x \<in> {..<m'+m}" using a by auto
  	      qed
  	    qed
  	  qed

  	  show "{..<m' + m} \<subseteq> \<Union> (BT ` {..k + 1})"
  	  proof 
  	    fix x assume "x \<in> {..<m' + m}"
  	    then consider "x \<in> {..<m'}" | "x \<in> {m'..<m'+m}" by fastforce
  	    then show "x \<in> \<Union> (BT ` {..k + 1})"
  	    proof (cases)
  	      case 1
  	      have *: "{..1::nat} = {0, 1::nat}" by auto
  	      from 1 have "x \<in> \<Union> (BL ` {..1::nat})" using BfL_props by simp
  	      then have "x \<in> BL 0 \<or> x \<in> BL 1" using * by simp
  	      then show ?thesis 
  	      proof (elim disjE)
  	        assume "x \<in> BL 0"
  	        then have "x \<in> Bvar 0" unfolding Bvar_def by simp
  	        then have "x \<in> BT 0" unfolding BT_def by simp
  	        then show "x \<in> \<Union> (BT ` {..k + 1})" by auto
  	      next
  	        assume "x \<in> BL 1"
  	        then have "x \<in> Bstat" unfolding Bstat_def by simp
  	        then have "x \<in> BT (k+1)" unfolding BT_def by simp
  	        then show "x \<in> \<Union> (BT ` {..k + 1})" by auto
  	      qed
  	    next
  	      case 2
  	      then have "x \<in> (\<Union>i\<le>k. shiftset m' (BS i))" using shiftset_image[of BS k m m'] BfS_props by simp
  	      then obtain i where i_prop: "i \<le> k \<and> x \<in> shiftset m' (BS i)" by blast
  	      then consider "i = k" | "i < k" by fastforce
  	      then show ?thesis
  	      proof (cases)
  	        case 1
  	        then have "x \<in> Bstat" unfolding Bstat_def using i_prop by auto
  	        then have "x \<in> BT (k+1)" unfolding BT_def by simp
  	        then show ?thesis by auto
  	      next
  	        case 2
  	        then have "x \<in> Bvar (i + 1)" unfolding Bvar_def using i_prop by simp
  	        then have "x \<in> BT (i + 1)" unfolding BT_def using 2 by force
  	        then show ?thesis using 2 by auto
  	      qed
  	    qed
  	  qed
  	qed


  	have F4: "fT \<in> (BT (k+1)) \<rightarrow>\<^sub>E {..<t+1}"
  	proof
  	  fix x assume "x \<in> BT (k+1)"
  	  then have "x \<in> Bstat" unfolding BT_def by simp
  	  then have "x \<in> BL 1 \<or> x \<in> shiftset m' (BS k)" unfolding Bstat_def by auto
  	  then show "fT x \<in> {..<t + 1}"
  	  proof (elim disjE)
  	    assume "x \<in> BL 1"
  	    then have "fT x = fL x" unfolding fT_def by simp
  	    then show "fT x \<in> {..<t+1}" using BfL_props \<open>x \<in> BL 1\<close> by auto
  	  next
  	    assume a: "x \<in> shiftset m' (BS k)"
  	    then have "fT x = fS (x - m')" unfolding fT_def by (metis IntI emptyE fax1)
  	    moreover have "x - m' \<in> BS k" using a unfolding shiftset_def by auto
  	    ultimately show "fT x \<in> {..<t+1}" using BfS_props by auto
  	  qed
  	qed(auto simp: BT_def Bstat_def fT_def)
  	find_theorems "\<forall>_\<in>_._"

  	have F5: "((\<forall>i \<in> BT (k + 1). T'' y i = fT i) \<and> (\<forall>j<k+1. \<forall>i \<in> BT j. (T'' y) i = y j))" if "y \<in> cube (k + 1) (t + 1)" for y
  	proof(intro conjI allI impI ballI)
  	  fix i assume "i \<in> BT (k + 1)"
  	  then have "i \<in> Bstat" unfolding BT_def by simp
  	  then consider "i \<in> shiftset m' (BS k)" |  "i \<in> BL 1" unfolding Bstat_def by blast
  	  then show "T'' y i = fT i"
  	  proof (cases)
  	    case 1
  	    then have "\<exists>s<m. i = m' + s" unfolding shiftset_def using BfS_props(2) by auto
  	    then obtain s where s_prop: "s < m \<and> i = m' + s" by blast
  	    then have *: " i \<in> {m'..<m'+m}" by simp
  	    have "i \<notin> BL 1" using 1 fax1 by auto
  	    then have "fT i = fS (i - m')" using 1 unfolding fT_def by simp
  	    then have **: "fT i = fS s" using s_prop by simp

  	    have XX: "(\<lambda>z \<in> {..<k}. y (z + 1)) \<in> cube k (t+1)" using split_cube that by simp
  	    have XY: "s \<in> BS k" using  s_prop  1 unfolding shiftset_def by auto

  	    from that have "T'' y i = (T' (\<lambda>z \<in> {..<1}. y z) (\<lambda>z \<in> {..<k}. y (z + 1))) i" unfolding T''_def by auto
  	    also have "... = (join (Sm'_line ((\<lambda>z \<in> {..<1}. y z) 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) m' m) i" using split_cube that unfolding T'_def by simp
  	    also have "... = (join (Sm'_line (y 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) m' m) i" by simp
  	    also have "... = (S (\<lambda>z \<in> {..<k}. y (z + 1))) s" using * s_prop unfolding join_def by simp
  	    also have "... = fS s" using XX XY BfS_props(6) by blast
  	    finally show ?thesis using ** by simp
  	  next
  	    case 2
  	    have XZ: "y 0 \<in> {..<t+1}" using that unfolding cube_def by auto
  	    have XY: "i \<in> {..<m'}" using 2 BfL_props(2) by blast
  	    have XX: "(\<lambda>z \<in> {..<1}. y z)  \<in> cube 1 (t+1)" using that split_cube by simp

        have some_eq_restrict: "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = ((\<lambda>z \<in> {..<1}. y z) 0)) = (\<lambda>z \<in> {..<1}. y z)"
        proof 
          show "restrict y {..<1} \<in> cube 1 (t + 1) \<and> restrict y {..<1} 0 = restrict y {..<1} 0" using XX by simp
        next
          fix p
          assume "p \<in> cube 1 (t+1) \<and> p 0 = restrict y {..<1} 0"
          moreover have "p u = restrict y {..<1} u" if "u \<notin> {..<1}" for u using that calculation XX unfolding cube_def using PiE_arb[of "restrict y {..<1}" "{..<1}" "\<lambda>x. {..<t + 1}" u]  PiE_arb[of p "{..<1}" "\<lambda>x. {..<t + 1}" u] by metis
          ultimately show "p = restrict y {..<1}" by auto 
        qed

  	    from that have "T'' y i = (T' (\<lambda>z \<in> {..<1}. y z) (\<lambda>z \<in> {..<k}. y (z + 1))) i" unfolding T''_def by auto
  	    also have "... = (join (Sm'_line ((\<lambda>z \<in> {..<1}. y z) 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) m' m) i" using split_cube that unfolding T'_def by simp
  	    also have "... = (Sm'_line ((\<lambda>z \<in> {..<1}. y z) 0)) i" using XY unfolding join_def by simp
  	    also have "... = Sm' (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = ((\<lambda>z \<in> {..<1}. y z) 0)) i" using XZ unfolding Sm'_line_def by auto
  	    also have "... = Sm' (\<lambda>z \<in> {..<1}. y z) i" using some_eq_restrict by simp
  	    also have "... = fL i" using BfL_props(6) XX 2 by blast
  	    also have "... = fT i" using 2 unfolding fT_def by simp
  	    finally show ?thesis .
  	  qed

  	next

(*  	define Bstat where "Bstat \<equiv> shiftset m' (BS k) \<union> BL 1"
   	define Bvar where "Bvar \<equiv> (\<lambda>i::nat. (if i = 0 then BL 0 else shiftset m' (BS (i - 1))))"
   	define BT where "BT \<equiv> (\<lambda>i \<in> {..<k+1}. Bvar i)((k+1):=Bstat)"
   	define fT where "fT \<equiv> (\<lambda>x. (if x \<in> BL 1 then fL x else (if x \<in> shiftset m' (BS k) then fS (x - m') else undefined)))"
    define T'' where "T'' \<equiv> (\<lambda>x \<in> cube (k + 1) (t+1). T' (\<lambda>y \<in> {..<1}. x y) (\<lambda>y \<in> {..<k}. x (y + 1)))"
    define T' where "T' \<equiv> (\<lambda>x \<in> cube 1 (t+1). \<lambda>y \<in> cube k (t+1). join (Sm'_line (x 0)) (S y) m' m)"
        "join f g n m \<equiv> (\<lambda>x. if x \<in> {..<n} then f x else (if x \<in> {n..<n+m} then g (x - n) else undefined))"


  obtain BS fS where BfS_props: "disjoint_family_on BS {..k}" "\<Union>(BS ` {..k}) = {..<m}" "({} \<notin> BS ` {..<k})" " fS \<in> (BS k) \<rightarrow>\<^sub>E {..<t+1}" "S \<in> (cube k (t+1)) \<rightarrow>\<^sub>E (cube m (t+1)) " "(\<forall>y \<in> cube k (t+1). (\<forall>i \<in> BS k. S y i = fS i) \<and> (\<forall>j<k. \<forall>i \<in> BS j. (S y) i = y j))" using S_prop unfolding layered_subspace_def is_subspace_def by auto

   	obtain BL fL where BfL_props: "disjoint_family_on BL {..1}" "\<Union>(BL ` {..1}) = {..<m'}"  "({} \<notin> BL ` {..<1})" "fL \<in> (BL 1) \<rightarrow>\<^sub>E {..<t+1}" "Sm' \<in> (cube 1 (t+1)) \<rightarrow>\<^sub>E (cube m' (t+1))" "(\<forall>y \<in> cube 1 (t+1). (\<forall>i \<in> BL 1. Sm' y i = fL i) \<and> (\<forall>j<1. \<forall>i \<in> BL j. (Sm' y) i = y j))" using Sm'_prop unfolding layered_subspace_def is_subspace_def by auto


"(\<forall>y \<in> cube k (t+1). (\<forall>i \<in> BS k. S y i = fS i) \<and> (\<forall>j<k. \<forall>i \<in> BS j. (S y) i = y j))"
*)
  	  fix j i assume "j < k + 1" "i \<in> BT j"
  	  then have i_prop: "i \<in> Bvar j" unfolding BT_def by auto
      consider "j = 0" | "j > 0" by auto
  	  then show "T'' y i = y j"
  	  proof cases
  	    case 1
  	    then have "i \<in> BL 0" using i_prop unfolding Bvar_def by auto
  	    then have XY: "i \<in> {..<m'}" using 1 BfL_props(2) by blast
  	    have XX: "(\<lambda>z \<in> {..<1}. y z)  \<in> cube 1 (t+1)" using that split_cube by simp
          	    have XZ: "y 0 \<in> {..<t+1}" using that unfolding cube_def by auto

        have some_eq_restrict: "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = ((\<lambda>z \<in> {..<1}. y z) 0)) = (\<lambda>z \<in> {..<1}. y z)"
        proof 
          show "restrict y {..<1} \<in> cube 1 (t + 1) \<and> restrict y {..<1} 0 = restrict y {..<1} 0" using XX by simp
        next
          fix p
          assume "p \<in> cube 1 (t+1) \<and> p 0 = restrict y {..<1} 0"
          moreover have "p u = restrict y {..<1} u" if "u \<notin> {..<1}" for u using that calculation XX unfolding cube_def using PiE_arb[of "restrict y {..<1}" "{..<1}" "\<lambda>x. {..<t + 1}" u]  PiE_arb[of p "{..<1}" "\<lambda>x. {..<t + 1}" u] by metis
          ultimately show "p = restrict y {..<1}" by auto 
        qed

  	    from that have "T'' y i = (T' (\<lambda>z \<in> {..<1}. y z) (\<lambda>z \<in> {..<k}. y (z + 1))) i" unfolding T''_def by auto
  	    also have "... = (join (Sm'_line ((\<lambda>z \<in> {..<1}. y z) 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) m' m) i" using split_cube that unfolding T'_def by simp
  	    also have "... = (Sm'_line ((\<lambda>z \<in> {..<1}. y z) 0)) i" using XY unfolding join_def by simp
  	    also have "... = Sm' (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = ((\<lambda>z \<in> {..<1}. y z) 0)) i" using XZ unfolding Sm'_line_def by auto
  	    also have "... = Sm' (\<lambda>z \<in> {..<1}. y z) i" using some_eq_restrict by simp
  	    also have "... =  (\<lambda>z \<in> {..<1}. y z) j" using BfL_props(6) XX 1  \<open>i \<in> BL 0\<close> by blast 
  	    also have "... = (\<lambda>z \<in> {..<1}. y z) 0" using 1 by blast
  	    also have "... = y 0" by simp
  	    also have "... = y j" using 1 by simp
  	    finally show ?thesis .
  	  next
  	    case 2
  	    then have "i \<in> shiftset m' (BS (j - 1))" using i_prop unfolding Bvar_def by simp
  	    then have "\<exists>s<m. m' + s = i" using BfS_props(2) \<open>j < k + 1\<close> unfolding shiftset_def by force 
  	    then obtain s where s_prop: "s < m" "i = s + m'" by auto
         then have *: " i \<in> {m'..<m'+m}" by simp

  	    have XX: "(\<lambda>z \<in> {..<k}. y (z + 1)) \<in> cube k (t+1)" using split_cube that by simp
  	    have XY: "s \<in> BS (j - 1)" using s_prop 2 \<open>i \<in> shiftset m' (BS (j - 1))\<close> unfolding shiftset_def by force

  	    from that have "T'' y i = (T' (\<lambda>z \<in> {..<1}. y z) (\<lambda>z \<in> {..<k}. y (z + 1))) i" unfolding T''_def by auto
  	    also have "... = (join (Sm'_line ((\<lambda>z \<in> {..<1}. y z) 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) m' m) i" using split_cube that unfolding T'_def by simp
  	    also have "... = (join (Sm'_line (y 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) m' m) i" by simp
  	    also have "... = (S (\<lambda>z \<in> {..<k}. y (z + 1))) s" using * s_prop unfolding join_def by simp
  	    also have "... = (\<lambda>z \<in> {..<k}. y (z + 1)) (j-1)" using XX XY BfS_props(6) 2 \<open>j < k + 1\<close> by auto
  	    also have "... = y j" using 2 \<open>j < k + 1\<close> by force
  	    finally show ?thesis .
  	  qed
  	qed
  	


  	from F1 F2 F3 F4 F5 have subspace_T'': "is_subspace T'' (k+1) (m'+m) (t+1)" unfolding is_subspace_def using T''_prop by metis


(* ------------------------------------------------------------------------------------------------------------------------------ *)


(** SECTION 4: PROVING T'' IS LAYERED **)

    (* This redefinition of the classes makes proving the layered property easier *)
    define T_class where "T_class \<equiv> (\<lambda>j\<in>{..k}. {join (Sm'_line i) s m' m | i s . i \<in> {..<t} \<and> s \<in> S ` (classes k t j)})(k+1:= {join (Sm'_line t) (SOME s. s \<in> S ` (cube m (t+1))) m' m})"
    (* Proving the equivalence *) 
    have classprop: "T_class j = T'' ` classes (k + 1) t j" if j_prop: "j \<le> k" for j
    proof
      show "T_class j \<subseteq> T'' ` classes (k + 1) t j"
      proof
        fix x assume "x \<in> T_class j"
        from that have "T_class j = {join (Sm'_line i) s m' m | i s . i \<in> {..<t} \<and> s \<in> S ` (classes k t j)}" unfolding T_class_def by simp
        then obtain i s where is_defs: "x = join (Sm'_line i) s m' m \<and> i < t \<and> s \<in> S ` (classes k t j)" using \<open>x \<in> T_class j\<close> unfolding T_class_def by auto
        moreover have *:"classes k t j \<subseteq> cube k (t+1)" unfolding classes_def by simp
        moreover have "\<exists>!y. y \<in> classes k t j \<and> s = S y" using subspace_inj_on_cube[of S k m "t+1"] S_prop inj_onD[of S "cube k (t+1)"] calculation unfolding layered_subspace_def inj_on_def by blast
        ultimately obtain y where y_prop: "y \<in> classes k t j \<and> s = S y \<and> (\<forall>z\<in>classes k t j. s = S z \<longrightarrow> y = z)" by auto

        define p where "p \<equiv> join (\<lambda>g\<in>{..<1}. i) y 1 k"
        have "(\<lambda>g\<in>{..<1}. i) \<in> cube 1 (t+1)" using is_defs unfolding cube_def by simp
        then have p_in_cube: "p \<in> cube (k + 1) (t+1)" using join_cubes[of "(\<lambda>g\<in>{..<1}. i)" 1 t y k]  y_prop * unfolding p_def by auto
        then have **: "p 0 = i \<and> (\<forall>l < k. p (l + 1) = y l)" unfolding p_def join_def by simp 

        have "t \<notin> y ` {..<(k - j)}" using y_prop unfolding classes_def by simp
        then have "\<forall>u < k - j. y u \<noteq> t" by auto
        then have "\<forall>u < k - j. p (u + 1) \<noteq> t" using ** by simp
        moreover have "p 0 \<noteq> t" using is_defs ** by simp
        moreover have "\<forall>u < k - j + 1. p u \<noteq> t" using calculation
          by (metis One_nat_def le_add_diff_inverse2 less_Suc0 less_diff_conv2 linorder_not_less)
        ultimately have "\<forall>u < (k + 1) - j. p u \<noteq> t" using that by auto
        then have A1: " t \<notin> p ` {..<((k+1) - j)}" by blast


        have "p u = t" if "u \<in> {k - j + 1..<k+1}" for u
        proof -
          from that have "u - 1 \<in> {k - j..<k}" by auto
          then have "y (u - 1) = t" using y_prop unfolding classes_def by blast
          then show "p u = t" using ** 
            by (metis \<open>u - 1 \<in> {k - j..<k}\<close> add_diff_cancel_left' atLeastLessThan_iff diff_is_0_eq' le_add_diff_inverse2 nat_less_le not_less that)
        qed
        then have A2: "\<forall>u\<in>{(k+1) - j..<k+1}. p u = t" using that by auto
        
        from A1 A2 p_in_cube have "p \<in> classes (k+1) t j" unfolding classes_def by blast

        moreover have "x = T'' p"
        proof-
          have loc_useful:"(\<lambda>y \<in> {..<k}. p (y + 1)) = (\<lambda>z \<in> {..<k}. y z)" using ** by auto
          have "T'' p = T' (\<lambda>y \<in> {..<1}. p y) (\<lambda>y \<in> {..<k}. p (y + 1))" using p_in_cube unfolding T''_def by auto
     
          have "T' (\<lambda>y \<in> {..<1}. p y) (\<lambda>y \<in> {..<k}. p (y + 1)) = join (Sm'_line ((\<lambda>y \<in> {..<1}. p y) 0)) (S (\<lambda>y \<in> {..<k}. p (y + 1))) m' m" using split_cube p_in_cube unfolding T'_def by simp
          also have "... = join (Sm'_line (p 0)) (S (\<lambda>y \<in> {..<k}. p (y + 1))) m' m" by simp
          also have "... = join (Sm'_line i) (S (\<lambda>y \<in> {..<k}. p (y + 1))) m' m" by (simp add: **)
          also have "... = join (Sm'_line i) (S (\<lambda>z \<in> {..<k}. y z)) m' m" using loc_useful by simp
          also have "... = join (Sm'_line i) (S y) m' m" using y_prop * unfolding cube_def by auto
          also have "... = x" using is_defs y_prop by simp
          finally show "x = T'' p" 
            using \<open>T'' p = T' (restrict p {..<1}) (\<lambda>y\<in>{..<k}. p (y + 1))\<close> by presburger
        qed
        ultimately show "x \<in> T'' ` classes (k + 1) t j" by blast
      qed
    next
      show "T'' ` classes (k + 1) t j \<subseteq> T_class j"
      proof
        fix x assume "x \<in> T'' ` classes (k+1) t j"
        then obtain y where y_prop: "y \<in> classes (k+1) t j \<and> T'' y = x" by blast
        then have y_props: "(\<forall>u \<in> {((k+1)-j)..<k+1}. y u = t) \<and> t \<notin> y ` {..<(k+1) - j }" unfolding classes_def by blast

        define z where "z \<equiv> (\<lambda>v \<in> {..<k}. y (v+1))" 
        have "z \<in> cube k (t+1)" using  y_prop classes_subset_cube[of "k+1" t j] unfolding z_def cube_def by auto
        moreover
        {
          have "z ` {..<k - j} = y ` ((+) 1 ` {..<k-j}) "  unfolding z_def by fastforce
          also have "... = y ` {1..<k-j+1}" by (simp add: atLeastLessThanSuc_atLeastAtMost image_Suc_lessThan)
          also have "... = y ` {1..<(k+1)-j}" using j_prop by auto
          finally have "z ` {..<k - j} \<subseteq> y ` {..<(k+1)-j}" by auto
          then have "t \<notin> z ` {..<k - j}" using y_props by blast
        
        }
        moreover have "\<forall>u \<in> {k-j..<k}. z u = t" unfolding z_def using y_props by auto
        ultimately have z_in_classes: "z \<in> classes k t j" unfolding classes_def by blast

        have "y 0 \<noteq> t" using y_props that 
          by (metis One_nat_def add.right_neutral add_Suc_right image_eqI le_imp_less_Suc lessThan_iff zero_less_diff)
        then have tr: "y 0 < t" using y_prop classes_subset_cube[of "k+1" t j] unfolding cube_def by fastforce

        have "(\<lambda>g \<in> {..<1}. y g) \<in> cube 1 (t+1)" using y_prop classes_subset_cube[of "k+1" t j] cube_restrict[of 1 "(k+1)" y "t+1"] 
          by (metis One_nat_def add_mono_thms_linordered_field(4) assms(2) in_mono less_numeral_extra(1) plus_1_eq_Suc) 
        then have "T'' y = T' (\<lambda>g \<in> {..<1}. y g) z  " using y_prop classes_subset_cube[of "k+1" t j] unfolding T''_def z_def by auto
        also have " ... = join (Sm'_line ((\<lambda>g \<in> {..<1}. y g) 0)) (S z) m' m" unfolding T'_def using \<open>(\<lambda>g \<in> {..<1}. y g) \<in> cube 1 (t+1)\<close> \<open>z \<in> cube k (t+1)\<close> by auto
        also have " ... = join (Sm'_line (y 0)) (S z) m' m" by simp
        also have " ... \<in> T_class j" using tr z_in_classes that unfolding T_class_def by force
        finally show "x \<in> T_class j" using y_prop by simp
      qed
    qed
    (* The core case i \<le> k. The case i = k+1 is trivial since k+1 has only one point. *)
    have "\<forall>x \<in> T'' ` classes (k+1) t i. \<forall>y \<in> T'' ` classes (k+1) t i.  \<chi> x = \<chi> y \<and> \<chi> x < r" if i_assm: "i \<le> k" for i
    proof (intro ballI)
      fix x y assume a: "x \<in> T'' ` classes (k + 1) t i" "y \<in> T'' ` classes (k + 1) t i"
      from that have *: "T'' ` classes (k+1) t i = T_class i" by (simp add: classprop)
      then have  "x \<in> T_class i " using a by simp
      moreover have **: "T_class i = {join (Sm'_line l) s m' m | l s . l \<in> {..<t} \<and> s \<in> S ` (classes k t i)}" using that unfolding T_class_def by simp
      ultimately obtain xs xi where xdefs:  "x = join (Sm'_line xi) xs m' m \<and> xi < t \<and> xs \<in> S ` (classes k t i)" by blast

      from * ** obtain ys yi where ydefs: "y = join (Sm'_line yi) ys m' m \<and> yi < t \<and> ys \<in> S ` (classes k t i)" using a by auto

      have "(Sm'_line xi) \<in> cube m' (t+1)" using Sm'_line_base_prop xdefs by simp
      moreover have "xs \<in> cube m (t+1)" using xdefs S_prop subspace_elems_embed imageE image_subset_iff mem_Collect_eq unfolding layered_subspace_def classes_def  by blast
      ultimately have AA1: "\<chi> x = \<chi>m' (Sm'_line xi) xs" using xdefs unfolding \<chi>m'_def by simp

      have "(Sm'_line yi) \<in> cube m' (t+1)" using Sm'_line_base_prop ydefs by simp
      moreover have "ys \<in> cube m (t+1)" using ydefs S_prop subspace_elems_embed imageE image_subset_iff mem_Collect_eq unfolding layered_subspace_def classes_def  by blast
      ultimately have AA2: "\<chi> y = \<chi>m' (Sm'_line yi) ys" using ydefs unfolding \<chi>m'_def by simp

      have "\<forall>s<t. \<forall>l < t. \<chi>m'_s (Sm' (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) = \<chi>m'_s (Sm' (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = l))" using dim1_layered_subspace_mono_line[of t Sm' m' s \<chi>m'_s] Sm'_prop assms(1) by blast
      then have mykey: "\<forall>s<t. \<forall>l<t. \<chi>m'_s (Sm'_line s) = \<chi>m'_s (Sm'_line l)" unfolding Sm'_line_def 
        by (metis (no_types, lifting) add.commute lessThan_iff less_Suc_eq plus_1_eq_Suc restrict_apply)
      have BIGKEY: "\<forall>s<t. \<forall>l<t. \<chi>m' (Sm'_line s) = \<chi>m' (Sm'_line l)"
      proof (intro allI impI)
        fix s l assume "s < t" "l < t"
        have L1: "\<chi>m' (Sm'_line s) \<in> cube m (t + 1) \<rightarrow>\<^sub>E {..<r}" unfolding \<chi>m'_def using A Sm'_line_base_prop \<open>s < t\<close> by simp
        have L2: "\<chi>m' (Sm'_line l) \<in> cube m (t + 1) \<rightarrow>\<^sub>E {..<r}" unfolding \<chi>m'_def using A Sm'_line_base_prop \<open>l < t\<close> by simp
        have "\<phi> (\<chi>m' (Sm'_line s)) = \<chi>m'_s (Sm'_line s)" unfolding \<chi>m'_s_def using \<open>s < t\<close> Sm'_line_base_prop by simp
        also have " ... =  \<chi>m'_s (Sm'_line l)" using mykey \<open>s <t\<close> \<open>l < t\<close> by blast
        also have " ... = \<phi> (\<chi>m' (Sm'_line l))" unfolding \<chi>m'_s_def using Sm'_line_base_prop \<open>l<t\<close> by simp
        finally have "\<phi> (\<chi>m' (Sm'_line s)) = \<phi> (\<chi>m' (Sm'_line l))" by simp
        then show "\<chi>m' (Sm'_line s) = \<chi>m' (Sm'_line l)" using \<phi>_prop Sm'_line_base_prop L1 L2 unfolding bij_betw_def inj_on_def by blast
      qed
      then have "\<chi>m' (Sm'_line xi) xs = \<chi>m' (Sm'_line 0) xs" using xdefs 
        by (metis assms(1) less_numeral_extra(1) less_trans)
      also have " ... =  \<chi>m xs" unfolding \<chi>m_def \<chi>m'_def using xdefs Sm'_line_base_prop by auto
      also have " ... = \<chi>m ys" using xdefs ydefs layered_eq_classes[of S k m t r \<chi>m] S_prop i_assm by blast
      also have " ... = \<chi>m' (Sm'_line 0) ys"  unfolding \<chi>m_def \<chi>m'_def using xdefs Sm'_line_base_prop by auto
      also have " ... = \<chi>m' (Sm'_line yi) ys" using ydefs 
        by (metis BIGKEY assms(1) less_trans zero_less_one)
      finally have CORE: "\<chi>m' (Sm'_line xi) xs =  \<chi>m' (Sm'_line yi) ys" by simp


      then have "\<chi> x = \<chi> y" using AA1 AA2 by simp      
      then show " \<chi> x = \<chi> y \<and> \<chi> x < r" 
        by (metis AA1 BIGKEY PiE_mem \<open>\<chi>m \<in> cube m (t + 1) \<rightarrow>\<^sub>E {..<r}\<close> \<open>\<chi>m xs = \<chi>m ys\<close> \<open>\<chi>m' (Sm'_line 0) xs = \<chi>m xs\<close> \<open>ys \<in> cube m (t + 1)\<close> assms(1) lessThan_iff less_numeral_extra(1) less_trans xdefs)

    qed
    then have "\<forall>i\<le>k. \<exists>c<r. \<forall>x \<in> T'' ` classes (k+1) t i. \<chi> x = c" 
      by (meson assms(5))

    have " (\<forall>i \<in> {..k+1}. \<exists>c<r. \<forall>x \<in> T'' ` classes (k+1) t i. \<chi> x = c)" sorry
    then have "(\<forall>i \<in> {..k+1}. \<exists>c<r. \<forall>x \<in> classes (k+1) t i. \<chi> (T'' x) = c)" by simp
    then have "layered_subspace T'' (k+1) (m' + m) t r \<chi>"  using subspace_T'' unfolding layered_subspace_def by simp

  	then show ?thesis  by (metis add.commute)


  qed
  show ?thesis sorry
qed

theorem thm4: fixes k assumes "\<And>r'. hj r' t" shows "lhj r t k"
proof (induction k arbitrary: r rule: less_induct)
  case (less k)
  consider "k = 0" | "k = 1" | "k \<ge> 2" by linarith
  then show ?case
  proof (cases)
    case 1
    then show ?thesis using dim0_layered_subspace_ex unfolding lhj_def by auto
  next
    case 2
    then show ?thesis
    proof (cases "t > 1")
      case True
      then show ?thesis using thm4_k_1[of "t"] assms 2 by blast
    next
      case False
      then show ?thesis sorry
    qed
  next
    case 3
    note less
    then show ?thesis
    proof (cases "t > 1 \<and> r > 0")
    	case True
    	then show ?thesis  using thm4_step[of t "k-1" r]
    	  using assms less.IH 3 One_nat_def Suc_pred by fastforce
    next
      case False
      then show ?thesis sorry
    qed
  qed
qed



lemma hales_jewett: "\<forall>\<chi> r t. \<exists>N'. \<forall>N \<ge> N'. \<chi> \<in> (cube N t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. is_line L N t \<and> \<chi> ` (L ` {..<t}) = {c})"
  sorry






end