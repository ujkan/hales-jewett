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

lemma nemp_emp:"A \<noteq> {} \<Longrightarrow> A \<rightarrow>\<^sub>E {} = {}"
  by blast

definition cube :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "cube n t \<equiv> {..<n} \<rightarrow>\<^sub>E {..<t}"

lemma PiE_uniqueness: "f ` A \<subseteq> B \<Longrightarrow> \<exists>!g \<in> A \<rightarrow>\<^sub>E B. \<forall>a\<in>A. g a = f a"
  using exI[of "\<lambda>x. x \<in> A \<rightarrow>\<^sub>E B \<and> (\<forall>a\<in>A. x a = f a)" "restrict f A"] PiE_ext PiE_iff by fastforce

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


lemma linorder_wlog_fun[case_names le sym]: "(\<And>a b. (f::('a \<Rightarrow> 'c) \<Rightarrow> ('b :: linorder)) a  \<le> f b \<Longrightarrow> P (f a) (f b)) \<Longrightarrow> (\<And>a b. P (f b) (f a) \<Longrightarrow> P (f a) (f b)) \<Longrightarrow> P (f a) (f b)"
  by (cases rule: le_cases[of "f a" "f b"]; blast+)

lemma cube1: "cube n 1 = {\<lambda>x\<in>{..<n}. 0}" unfolding cube_def by (simp add: lessThan_Suc)

definition is_line :: "(nat \<Rightarrow> (nat \<Rightarrow> nat)) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "is_line L n t \<equiv> (L \<in> {..<t} \<rightarrow>\<^sub>E cube n t \<and> ((\<forall>j<n. (\<forall>x<t. \<forall>y<t. L x j =  L y j) \<or> (\<forall>s<t. L s j = s)) \<and> (\<exists>j < n. (\<forall>s < t. L s j = s))))"

lemma is_line_elim_t_1:
  assumes "is_line L n t" and "t = 1"
  shows "\<exists>B\<^sub>0 B\<^sub>1. B\<^sub>0 \<union> B\<^sub>1 = {..<n} \<and> B\<^sub>0 \<inter> B\<^sub>1 = {} \<and> B\<^sub>0 \<noteq> {} \<and> (\<forall>j \<in> B\<^sub>1. (\<forall>x<t. \<forall>y<t. L x j = L y j)) \<and> (\<forall>j \<in> B\<^sub>0. (\<forall>s<t. L s j = s))"
proof -
  define B0 where "B0 = {..<n}"
  define B1 where "(B1::nat set) = {}"
  have "B0 \<union> B1 = {..<n}" unfolding B0_def B1_def by simp
  moreover have "B0 \<inter> B1 = {}" unfolding B0_def B1_def by simp
  moreover have "B0 \<noteq> {}" using assms unfolding B0_def is_line_def by auto
  moreover have "(\<forall>j \<in> B1. (\<forall>x<t. \<forall>y<t. L x j = L y j))" unfolding B1_def by simp
  moreover have "(\<forall>j \<in> B0. (\<forall>s<t. L s j = s))" using assms(1, 2) cube1 unfolding B0_def is_line_def by auto
  ultimately show ?thesis by blast
qed

lemma is_line_elim:
  assumes "is_line L n t" and "t > 0"
  shows "\<exists>B\<^sub>0 B\<^sub>1. B\<^sub>0 \<union> B\<^sub>1 = {..<n} \<and> B\<^sub>0 \<inter> B\<^sub>1 = {} \<and> B\<^sub>0 \<noteq> {} \<and> (\<forall>j \<in> B\<^sub>1. (\<forall>x<t. \<forall>y<t. L x j = L y j)) \<and> (\<forall>j \<in> B\<^sub>0. (\<forall>s<t. L s j = s))"
proof -
  consider "t = 1" | "t > 1" using assms(2) by linarith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using is_line_elim_t_1 assms(1) by simp
  next
    case 2
    define B0 where "B0 = {j \<in> {..<n}. (\<forall>s<t. L s j = s)}"
    define B1 where "B1 = {j \<in> {..<n}. (\<forall>x<t. \<forall>y<t. L x j = L y j)}"

    from 2 assms(1) have "B0 \<noteq> {}" unfolding is_line_def B0_def by simp 
    moreover from assms have "B0 \<union> B1 = {..<n}" unfolding is_line_def B0_def B1_def by auto
    moreover have "\<forall>j \<in> B0. \<forall>s<t. L s j = s" unfolding B0_def by simp
    moreover have "\<forall>j \<in> B1. \<forall>x<t. \<forall>y<t. L x j = L y j" unfolding B1_def by blast
    moreover have "B0 \<inter> B1 = {}" 
    proof(safe)
      fix i assume "i \<in> B0" "i\<in>B1"
      then have "(\<forall>s < t. L s i = s) " unfolding B0_def by simp
      then have "\<not>(\<forall>x<t. \<forall>y<t. L x i = L y i)" using 2 less_trans 
        by (metis less_numeral_extra(1) zero_neq_one)
      then have False using \<open>i \<in> B1\<close> unfolding B1_def by blast
      then show "i \<in> {}" by simp
    qed
    ultimately show ?thesis by blast
  qed
  
qed

lemma "\<not>is_line L 0 t" 
  unfolding is_line_def by blast

lemma "n > 0 \<Longrightarrow> \<exists>!L. is_line L n (0::nat)"
  unfolding is_line_def by auto

lemma is_line_elim_alt:
  assumes "is_line L n t" and "t > 0"
  shows "\<exists>BL. BL \<subseteq> {..<n} \<and> BL \<noteq> {} \<and> (\<forall>j \<in> {..<n} - BL. (\<forall>x<t. \<forall>y<t. L x j = L y j)) \<and> (\<forall>j \<in> BL. (\<forall>s<t. L s j = s))"
  using is_line_elim[of L n t]
  by (metis Diff_Diff_Int Int_Diff_Un Int_commute Un_Diff Un_empty_right Un_upper1 assms(1) assms(2))

lemma aux2: "is_line L n t \<Longrightarrow> (\<forall>s<t. L s \<in> cube n t)"
  unfolding cube_def is_line_def
  by auto     

lemma aux2_exp: "is_line L n t \<Longrightarrow> (\<forall>s<t. \<forall>j<n. L s j \<in> {..<t})" 
  using aux2 unfolding cube_def by blast

lemma 
  assumes "is_line L n t" and "t > 0"
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
          by (metis "2" \<open>j \<in> {..<n}\<close> \<open>s \<in> {..<t + 1}\<close> assms(2) lessThan_iff less_trans)
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

lemma subspace_card: assumes "is_subspace S k n t" and "t > 1" shows "k \<le> n" 
proof -
  from assms have "S \<in> cube k t \<rightarrow>\<^sub>E cube n t" unfolding is_subspace_def by blast
  then have "S ` cube k t \<subseteq> cube n t" by blast
  then have "card (S ` cube k t) \<le> card (cube n t)" 
    by (simp add: card_mono cube_def finite_PiE)
  moreover have "card (S ` cube k t) = card (cube k t)" using subspace_inj_on_cube[of S k n t] assms card_image by blast
  ultimately have "card (cube k t) \<le> card (cube n t)" by auto
  then have "t ^ k \<le> t ^ n" using cube_card by (simp add: cube_def)
  then show "k \<le> n" using assms(2) by auto



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
  where "layered_subspace S k n t r \<chi> \<equiv> (is_subspace S k n (t + 1)  \<and> (\<forall>i \<in> {..k}. \<exists>c<r. \<forall>x \<in> classes k t i. \<chi> (S x) = c)) \<and> \<chi> \<in> cube n (t + 1) \<rightarrow>\<^sub>E {..<r}"
 
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
  ultimately have "layered_subspace S 0 n t r \<chi>" using S_prop assms unfolding layered_subspace_def by blast
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

lemma exI2: "P x y \<Longrightarrow> \<exists>x y. P x y"
  by blast
text \<open>Relating lines and 1-dimensional subspaces.\<close>
  (* use assumes and shows *)

lemma line_is_dim1_subspace_t_1: assumes "n > 0" and "is_line L n 1" shows "is_subspace (restrict (\<lambda>y. L (y 0)) (cube 1 1)) 1 n 1"
proof -
  obtain B\<^sub>0 B\<^sub>1 where B_props: "B\<^sub>0 \<union> B\<^sub>1 = {..<n} \<and> B\<^sub>0 \<inter> B\<^sub>1 = {} \<and> B\<^sub>0 \<noteq> {} \<and> (\<forall>j \<in> B\<^sub>1. (\<forall>x<1. \<forall>y<1. L x j = L y j)) \<and> (\<forall>j \<in> B\<^sub>0. (\<forall>s<1. L s j = s))" using is_line_elim_t_1[of L n 1] assms by auto

  define B where "B \<equiv> (\<lambda>i::nat. {}::nat set)(0:=B\<^sub>0, 1:=B\<^sub>1)" 
  define f where "f \<equiv> (\<lambda>i \<in> B 1. L 0 i)"
  thm is_subspace_def
  have *: "L 0 \<in> {..<n} \<rightarrow>\<^sub>E {..<1}" using assms(2) unfolding cube_def is_line_def by auto
  have "disjoint_family_on B {..1}" unfolding B_def using B_props 
    by (simp add: Int_commute disjoint_family_onI)
  moreover have " \<Union> (B ` {..1}) = {..<n}" unfolding B_def using B_props by auto
  moreover have "{} \<notin> B ` {..<1}" unfolding B_def using B_props by auto
  moreover have " f \<in> B 1 \<rightarrow>\<^sub>E {..<1}" using * calculation(2) unfolding f_def by auto
  moreover have "(restrict (\<lambda>y. L (y 0)) (cube 1 1)) \<in> cube 1 1 \<rightarrow>\<^sub>E cube n 1" using assms(2) cube1 unfolding is_line_def by auto
  moreover have "(\<forall>y\<in>cube 1 1. (\<forall>i\<in>B 1. (restrict (\<lambda>y. L (y 0)) (cube 1 1)) y i = f i) \<and> (\<forall>j<1. \<forall>i\<in>B j. (restrict (\<lambda>y. L (y 0)) (cube 1 1)) y i = y j))" using cube1 B_props * unfolding B_def f_def by auto
  ultimately show ?thesis unfolding is_subspace_def by blast 
qed

lemma assumes "f \<in> A \<rightarrow>\<^sub>E B" and "g \<in> B \<rightarrow>\<^sub>E C" and "undefined \<notin> B" shows "g \<circ> f \<in> A \<rightarrow>\<^sub>E C"
proof
  fix x
  assume "x \<in> A"
  have "(g \<circ> f) x = g (f x)" by simp
  moreover have "f x \<in> B" using assms(1) \<open>x \<in> A\<close> by blast
  ultimately have "g (f x) \<in> C" using assms(2) by blast
  then show "(g \<circ> f) x \<in> C" by simp
next
  fix x
  assume "x \<notin> A"
  then have "(g \<circ> f) x = g (f x)" by simp
  also have " ... = g (undefined)" using assms \<open>x \<notin> A\<close> by auto
  also have " ... = undefined" using assms by blast
  finally show "(g \<circ> f) x = undefined" .
qed

lemma assumes "is_subspace S k n t" and "is_line L k t"
  shows "is_line (S \<circ> L) n t"
proof -
  (*
S \<circ> L \<in> {..<t} \<rightarrow>\<^sub>E cube n t \<and> (\<forall>j<n. (\<forall>x<t. \<forall>y<t. (S \<circ> L) x j = (S \<circ> L) y j) \<or> (\<forall>s<t. (S \<circ> L) s j = s)) \<and> (\<exists>j<n. \<forall>s<t. (S \<circ> L) s j = s)
*)
  have "L \<in> {..<t} \<rightarrow>\<^sub>E cube k t" using assms(2) unfolding is_line_def by linarith
  moreover have "S \<in> cube k t \<rightarrow>\<^sub>E cube n t" using assms(1) unfolding is_subspace_def by blast
  ultimately have "S \<circ> L \<in> {..<t} \<rightarrow>\<^sub>E cube n t" sorry

  show "is_line (S \<circ> L) n t" sorry

qed



lemma line_is_dim1_subspace_t_ge_1: "n > 0 \<Longrightarrow> t > 1 \<Longrightarrow> is_line L n t \<Longrightarrow> is_subspace (restrict (\<lambda>y. L (y 0)) (cube 1 t)) 1 n t"
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

lemma line_is_dim1_subspace: assumes "n > 0" "t > 0" "is_line L n t" shows "is_subspace (restrict (\<lambda>y. L (y 0)) (cube 1 t)) 1 n t"
  using line_is_dim1_subspace_t_1[of n L] line_is_dim1_subspace_t_ge_1[of n t L] assms 
  by (metis less_one linorder_cases nat_less_le) 

definition hj 
  where "hj r t \<equiv> (\<exists>N>0. \<forall>N' \<ge> N. \<forall>\<chi>. \<chi> \<in> (cube N' t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. is_line L N' t \<and> (\<forall>y \<in> L ` {..<t}. \<chi> y = c)))"

definition lhj
  where "lhj r t k \<equiv> (\<exists>M > 0. \<forall>M' \<ge> M. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. layered_subspace S k M' t r \<chi>))"


text \<open>Base case of Theorem 4\<close>

lemma thm4_k_1: 
  fixes   r t
  assumes "t > 0"
    and "\<And>r'. hj r' t" 
  shows "lhj r t 1"

proof-
  obtain N where N_def: "N > 0 \<and> (\<forall>N' \<ge> N. \<forall>\<chi>. \<chi> \<in> (cube N' t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. is_line L N' t \<and> (\<forall>y \<in> L ` {..<t}. \<chi> y = c)))" using assms(2) unfolding hj_def by metis

  have "\<forall>N' \<ge> N. \<forall>\<chi>. \<chi> \<in> (cube N' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. is_subspace S 1 N' (t + 1) \<and> (\<forall>i \<in> {..1}. \<exists>c < r. (\<forall>x \<in> classes 1 t i. \<chi> (S x) = c)))"
  proof(safe)
    fix N' \<chi>
    assume asm: "N' \<ge> N" "\<chi> \<in> cube N' (t + 1) \<rightarrow>\<^sub>E {..<r::nat}"
    then have N'_props: "N' > 0 \<and> (\<forall>\<chi>. \<chi> \<in> (cube N' t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. is_line L N' t \<and> (\<forall>y \<in> L ` {..<t}. \<chi> y = c)))" using N_def by simp
    let ?chi_t = "(\<lambda>x \<in> cube N' t. \<chi> x)"
    have "?chi_t \<in> cube N' t \<rightarrow>\<^sub>E {..<r::nat}" using AUX asm by auto
    then obtain L where L_def: "\<exists>c<r. (is_line L N' t \<and> (\<forall>y \<in> L ` {..<t}. ?chi_t y = c))" using N'_props by presburger

    have "is_subspace (restrict (\<lambda>y. L (y 0)) (cube 1 t)) 1 N' t" using line_is_dim1_subspace N'_props L_def 
      using assms(1) by auto 
    then obtain B f where Bf_defs: "disjoint_family_on B {..1} \<and> \<Union>(B ` {..1}) = {..<N'} \<and> ({} \<notin> B ` {..<1}) \<and> f \<in> (B 1) \<rightarrow>\<^sub>E {..<t} \<and> (restrict (\<lambda>y. L (y 0)) (cube 1 t)) \<in> (cube 1 t) \<rightarrow>\<^sub>E (cube N' t) \<and> (\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. (restrict (\<lambda>y. L (y 0)) (cube 1 t)) y i = f i) \<and> (\<forall>j<1. \<forall>i \<in> B j. ((restrict (\<lambda>y. L (y 0)) (cube 1 t)) y) i = y j))" unfolding is_subspace_def by auto 

    have "{..1::nat} = {0,1}" by auto
    then have B_props: "B 0 \<union> B 1 = {..<N'} \<and> (B 0 \<inter> B 1 = {})" using Bf_defs unfolding disjoint_family_on_def by auto
    define L' where  "L' \<equiv> L(t:=(\<lambda>j. if j \<in> B 1 then L (t - 1) j else (if j \<in> B 0 then t else undefined)))" 
    have line_prop: "is_line L' N' (t + 1)"
    proof-
      have A1:"L' \<in> {..<t+1} \<rightarrow>\<^sub>E cube N' (t + 1)" 
      proof
        fix x
        assume asm: "x \<in> {..<t + 1}"
        then show "L' x \<in> cube N' (t + 1)"
        proof (cases "x < t")
          case True
          then have "L' x = L x" by (simp add: L'_def)
          then have "L' x \<in> cube N' t" using L_def True unfolding is_line_def by auto
          then show "L' x \<in> cube N' (t + 1)" using AUX by blast
        next
          case False
          then have "x = t" using asm by simp
          show "L' x \<in> cube N' (t + 1)"
          proof(unfold cube_def, intro PiE_I)
            fix j
            assume "j \<in> {..<N'}"
            have "j \<in> B 1 \<or> j \<in> B 0 \<or> j \<notin> (B 0 \<union> B 1)" by blast
            then show "L' x j \<in> {..<t + 1}"
            proof (elim disjE)
              assume "j \<in> B 1"
              then have "L' x j = L (t - 1) j" 
                by (simp add: \<open>x = t\<close> L'_def)
              have "L (t - 1) \<in> cube N' t" using aux2 L_def 
                by (meson assms(1) diff_less less_numeral_extra(1))
              then have "L (t - 1) j < t" using \<open>j \<in> {..<N'}\<close> unfolding cube_def by auto 
              then show "L' x j \<in> {..<t + 1}" using \<open>L' x j = L (t - 1) j\<close> by simp
            next
              assume "j \<in> B 0"
              then have "j \<notin> B 1" using Bf_defs unfolding disjoint_family_on_def by auto
              then have "L' x j = t"  by (simp add: \<open>j \<in> B 0\<close> \<open>x = t\<close> L'_def)
              then show "L' x j \<in> {..<t + 1}" by simp
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
            then show "L' x j = undefined" using \<open>x = t\<close> by (simp add: L'_def)
          qed
        qed
      next
        fix x
        assume asm: "x \<notin> {..<t+1}" 
        then have "x \<notin> {..<t} \<and> x \<noteq> t" by simp
        then show "L' x = undefined" unfolding L'_def by (metis (no_types, lifting) L_def PiE_E fun_upd_apply is_line_def)
      qed


      have A2: "(\<exists>j<N'. (\<forall>s < (t + 1). L' s j = s))"
      proof (cases "t = 1")
        case True
        obtain j where j_prop: "j \<in> B 0 \<and> j < N'" using Bf_defs by blast
        then have "\<forall>s < t. L' s j = L s j" by (auto simp: L'_def)
        moreover have "\<forall>s < t. L s j = 0" using True L_def unfolding is_line_def 
          by (metis L_def aux2_exp j_prop lessThan_iff less_one)
        ultimately have "\<forall>s < t. L' s j = s" using True by simp
        moreover have "L' t j = t" using j_prop B_props by (auto simp: L'_def)
        ultimately show ?thesis unfolding L'_def using j_prop by force
      next
        case False
        then show ?thesis
        proof-
          have "(\<exists>j<N'. (\<forall>s < t. L' s j = s))" using L_def unfolding is_line_def by (auto simp: L'_def)
          then obtain j where j_def: "j < N' \<and> (\<forall>s < t. L' s j = s)" by blast
              (* following not very clean, overreliance on sledgehammer *)
          have "j \<notin> B 1"
          proof 
            assume a:"j \<in> B 1"
            then have "(\<forall>y \<in> cube 1 t. (restrict (\<lambda>y. L (y 0)) (cube 1 t)) y j = f j)" using Bf_defs by simp
            then have "\<forall>y \<in> cube 1 t. L (y 0) j = f j" by simp
            moreover have "\<forall>y \<in> cube 1 t. (\<exists>!i. i < t \<and> y 0 = i)" using one_dim_cube_eq_nat_set[of "t"] unfolding bij_betw_def by blast
            moreover have "\<forall>i<t. (\<exists>!y. y \<in> cube 1 t \<and> y 0 = i)" using one_dim_cube_eq_nat_set[of "t"] unfolding bij_betw_def 
              by (smt (verit, best) image_iff inj_on_def lessThan_iff)
            moreover have "\<forall>i<t. L i j = f j" using calculation by blast
            moreover have "(\<exists>j<N'. (\<forall>s < t. L s j = s))" using \<open>(\<exists>j<N'. (\<forall>s < t. L' s j = s))\<close> by (auto simp: L'_def)
            ultimately show False using False
              by (metis (no_types, lifting) L'_def assms(1) fun_upd_apply j_def less_one nat_neq_iff)
          qed
          then have "j \<in> B 0" using \<open>j \<notin> B 1\<close> j_def B_props by auto

          then have "L' t j = t" using \<open>j \<notin> B 1\<close> by (auto simp: L'_def)
          then have "(\<forall>s < (t + 1). L' s j = s)" using j_def by (auto simp: L'_def)
          then show ?thesis using j_def by blast
        qed
      qed
      

      have A3: "(\<forall>j<N'. (\<forall>x<t+1. \<forall>y<t+1. L' x j =  L' y j) \<or> (\<forall>s<t+1. L' s j = s))"
      proof(intro allI impI)
        fix j
        assume "j < N'"
        show "(\<forall>x<t+1. \<forall>y<t+1. L' x j =  L' y j) \<or> (\<forall>s<t+1. L' s j = s)"
        proof (cases "j \<in> B 1")
          case True
          then have "(\<forall>y \<in> cube 1 t. (restrict (\<lambda>y. L (y 0)) (cube 1 t)) y j = f j)" using Bf_defs by simp
          moreover have "\<forall>y \<in> cube 1 t. (\<exists>!i. i < t \<and> y 0 = i)" using one_dim_cube_eq_nat_set[of "t"] unfolding bij_betw_def by blast
          moreover have "\<forall>i<t. (\<exists>!y. y \<in> cube 1 t \<and> y 0 = i)" using one_dim_cube_eq_nat_set[of "t"] unfolding bij_betw_def 
            by (smt (verit, best) image_iff inj_on_def lessThan_iff)
          moreover have "\<forall>i<t. L i j = f j" using calculation by auto
          ultimately have  "\<forall>x<t. \<forall>i<t. L i j = L x j" by simp
          then have *: "\<forall>x<t.\<forall>y<t. L' x j = L' y j" unfolding L'_def
            by (metis (no_types, lifting) fun_upd_apply nat_neq_iff)

          have "L' t j = L' (t - 1) j" using \<open>j \<in> B 1\<close> by (auto simp: L'_def)
          then have "\<forall>x<t. L' x j = L' t j" using *  
            by (metis (no_types, lifting) assms(1) diff_less zero_less_one)
          then have "\<forall>x<t+1. \<forall>y<t+1. L' x j = L' y j" using * 
            by (simp add: less_Suc_eq L'_def)
          then show ?thesis by blast
        next
          case False
          then have "j \<in> B 0" using B_props \<open>j <N'\<close> by auto
          then have "\<forall>y \<in> cube 1 t. ((restrict (\<lambda>y. L (y 0)) (cube 1 t)) y) j = y 0" using \<open>j \<in> B 0\<close> Bf_defs by auto
          then have "\<forall>y \<in> cube 1 t. L (y 0) j = y 0"  by auto
          moreover have "\<forall>i<t. (\<exists>!y. y \<in> cube 1 t \<and> y 0 = i)" using one_dim_cube_eq_nat_set[of "t"] unfolding bij_betw_def 
            by (smt (verit, best) image_iff inj_on_def lessThan_iff)
          ultimately have "\<forall>s<t. L s j = s" by auto
          then have "\<forall>s<t. L' s j = s" by (auto simp: L'_def)
          moreover have "L' t j = t" using False \<open>j \<in> B 0\<close> by (auto simp: L'_def)
          ultimately have "\<forall>s<t+1. L' s j = s" by (auto simp: L'_def)
          then show ?thesis by blast
        qed




      qed
      from A1 A2 A3 show ?thesis unfolding is_line_def by simp


    qed
    then have F1: "is_subspace (restrict (\<lambda>y. L' (y 0)) (cube 1 (t + 1))) 1 N' (t + 1)" using line_is_dim1_subspace[of "N'" "t+1"] N'_props assms(1) by force

    define S1 where "S1 \<equiv> (restrict (\<lambda>y. L' (y (0::nat))) (cube 1 (t+1)))"
      (* have F2: "\<exists>c < r. \<forall>x \<in> classes 1 t i. \<chi> (S1 x) = c" if i: "i \<in> {..1}" for i
proof - *)
    have F2: "(\<forall>i \<in> {..1}. \<exists>c < r. (\<forall>x \<in> classes 1 t i. \<chi> (S1 x) = c))"
    proof(safe)                    
      fix i
      assume "i \<le> (1::nat)"
      have "\<exists>c < r. (\<forall>y \<in> L' ` {..<t}. ?chi_t y = c)" unfolding L'_def using L_def by fastforce
      have "\<forall>x \<in> (L ` {..<t}). x \<in> cube N' t" using L_def 
        using aux2 by blast
      then have "\<forall>x \<in> (L' ` {..<t}). x \<in> cube N' t" by (auto simp: L'_def)
      then have *:"\<forall>x \<in> (L' ` {..<t}). \<chi> x = ?chi_t x" by simp
      then have "?chi_t ` (L' ` {..<t}) = \<chi> ` (L' ` {..<t})" by force
      then have "\<exists>c < r. (\<forall>y \<in> L' ` {..<t}. \<chi> y = c)" using \<open>\<exists>c < r. (\<forall>y \<in> L' ` {..<t}. ?chi_t y = c)\<close> *
        by (smt (z3))
      then obtain linecol where lc_def: "linecol < r \<and> (\<forall>y \<in> L' ` {..<t}. \<chi> y = linecol)" by blast
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
          then have "S1 x = L' (x 0)" unfolding S1_def by simp
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
  then show ?thesis using N_def unfolding layered_subspace_def lhj_def by auto
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
  assumes "t > 0" 
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

find_theorems "_ (THE _. _)"
thm the_inv_into_def
lemma invinto: "bij_betw f A B \<Longrightarrow> (\<forall>x \<in> B. \<exists>!y \<in> A. (the_inv_into A f) x = y)" 
  unfolding bij_betw_def inj_on_def 
  by (metis inj_on_def order_refl the_inv_into_into)

lemma invintoprops:
  assumes "s < t"
  shows "the_inv_into (cube 1 t) (\<lambda>f. f 0) s \<in> cube 1 t" 
    and "the_inv_into (cube 1 t) (\<lambda>f. f 0) s 0 = s"
  using assms invinto one_dim_cube_eq_nat_set apply auto
  using f_the_inv_into_f_bij_betw by fastforce




lemma "\<exists>!x. P x \<Longrightarrow> (SOME x. P x) = (THE x. P x)"
  by (metis someI_ex theI)
lemma some_inv_into: assumes "s < t" shows "(SOME p. p\<in>cube 1 t \<and> p 0 = s) = (the_inv_into (cube 1 t) (\<lambda>f. f 0) s)"
  using invintoprops[of s t] invinto[of "(\<lambda>f. f 0)" "cube 1 t" "{..<t}"] one_dim_cube_eq_nat_set[of t] assms someI_ex theI unfolding the_inv_into_def 
  by (smt (verit, best) bij_betw_iff_bijections cube_props(1) cube_props(2) cube_props(4) one_dim_cube_eq_nat_set)

lemma some_inv_into_2:  assumes "s < t" shows "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) = (the_inv_into (cube 1 t) (\<lambda>f. f 0) s)"
proof-
  have "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) \<in> cube 1 (t+1)" using cube_props assms by simp
  moreover have A:"(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) 0 = s" using cube_props assms by simp
  ultimately have "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) ` {..<1} = {s}" by auto
  then have "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) ` {..<1} \<subseteq> {..<t}" using assms by simp
  then have B: "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) \<in> cube 1 t" using \<open>(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) \<in> cube 1 (t+1)\<close> unfolding cube_def by blast

  show "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) = (the_inv_into (cube 1 t) (\<lambda>f. f 0) s)" using A B 
    by (smt (verit, best) assms bij_betw_iff_bijections invintoprops(1) invintoprops(2) one_dim_cube_eq_nat_set)

qed

lemma dim1_layered_subspace_as_line:
  assumes "t > 0"
    and "layered_subspace S 1 n t r \<chi>"
  shows "\<exists>c1 c2. c1<r \<and> c2<r \<and> (\<forall>s<t. \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) = c1) \<and> \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = t)) = c2"
proof -
  thm layered_subspace_def
  have "\<forall>x\<in>classes 1 t 0. t \<notin> x ` {..<1}" unfolding classes_def by simp
  have "\<forall>x \<in> classes 1 t 0. \<forall>u. u < 1 \<longrightarrow> x u < t"
  proof (intro allI ballI impI)
    fix x u assume "x \<in> classes 1 t 0" "(u::nat) < 1"
    then have "x \<in> cube 1 (t+1)" unfolding classes_def by blast
    then have "x u \<in> {..<t+1}" using \<open>u < 1\<close> unfolding cube_def by blast
    then have "x u \<in> {..<t}" using \<open>\<forall>x\<in>classes 1 t 0. t \<notin> x ` {..<1}\<close> 
      using \<open>u < 1\<close> \<open>x \<in> classes 1 t 0\<close> less_Suc_eq by fastforce
    then show "x u < t" by simp
  qed
  then have "classes 1 t 0 \<subseteq> cube 1 t" unfolding cube_def classes_def by auto
  moreover have "cube 1 t \<subseteq> classes 1 t 0" using AUX[of 1 t] unfolding cube_def classes_def by auto
  ultimately have X: "classes 1 t 0 = cube 1 t" by blast

  obtain c1 where c1_prop: "c1 < r \<and> (\<forall>x\<in>classes 1 t 0. \<chi> (S x) = c1)" using assms(2) unfolding layered_subspace_def by blast
  then have "(\<forall>x \<in> cube 1 t. \<chi> (S x) = c1)" using X by blast
  then have "\<forall>s<t. \<chi> (S (the_inv_into (cube 1 t) (\<lambda>f. f 0) s)) = c1" using one_dim_cube_eq_nat_set[of t] 
    by (meson bij_betwE bij_betw_the_inv_into lessThan_iff)
  then have K1: "\<forall>s<t. \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) = c1" using some_inv_into_2 by simp

  have *: "\<exists>c<r. \<forall>x \<in> classes 1 t 1. \<chi> (S x) = c" using assms(2) unfolding layered_subspace_def by blast

  have "\<forall>x \<in> classes 1 t 1. x 0 = t" unfolding classes_def by simp
  moreover have "\<exists>!x \<in> cube 1 (t+1). x 0 = t" using one_dim_cube_eq_nat_set[of "t+1"] unfolding bij_betw_def inj_on_def 
    using invintoprops(1) invintoprops(2) by force 
  moreover have **: "\<exists>!x. x  \<in> classes 1 t 1" unfolding classes_def using calculation(2) by simp
  ultimately have "the_inv_into (cube 1 (t+1)) (\<lambda>f. f 0) t \<in> classes 1 t 1" using invintoprops[of t "t+1"] unfolding classes_def by simp

  then have "\<exists>c2. c2 < r \<and> \<chi> (S (the_inv_into (cube 1 (t+1)) (\<lambda>f. f 0) t)) = c2" using * ** by blast
  then have K2: "\<exists>c2. c2 < r \<and> \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = t)) = c2" using some_inv_into by simp

  from K1 K2 show ?thesis 
    using c1_prop by blast
qed

lemma dim1_layered_subspace_mono_line: assumes "t > 0" and "layered_subspace S 1 n t r \<chi>"
  shows "\<forall>s<t. \<forall>l<t.  \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) =  \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = l)) \<and>  \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) < r"
  using dim1_layered_subspace_as_line[of t S n r \<chi>] assms by auto

find_theorems "_ \<subseteq> _ \<Longrightarrow> _ \<subseteq> _ \<Longrightarrow> _ = _"
lemma "{(\<lambda>x\<in>{..<1::nat}. t)} = classes 1 t 1"
apply (rule equalityI)
   apply (simp add: cube_def classes_def)
  unfolding classes_def cube_def apply simp 
  by (smt (verit, best) PiE_iff PiE_singleton insertCI lessThan_0 lessThan_Suc mem_Collect_eq restrict_apply' restrict_extensional singletonD subsetI)
  

definition join
  where
    "join f g n m \<equiv> (\<lambda>x. if x \<in> {..<n} then f x else (if x \<in> {n..<n+m} then g (x - n) else undefined))"

lemma NOTES1: assumes "j < k" shows "classes (k+1) t j = {join f g 1 k | f g . f \<in> classes 1 t j \<and> g \<in> classes k t j}"
proof
  show "classes (k + 1) t j \<subseteq> {join f g 1 k |f g. f \<in> classes 1 t j \<and> g \<in> classes k t j}"
  proof
    fix x
    assume "x \<in> classes (k + 1) t j"
    moreover have "(0::nat) \<in> {..<k + 1 - j}" using assms by auto
    ultimately have "x (0::nat) \<noteq> t" unfolding classes_def by blast
    then have "x (0::nat) \<in> {..<t+1}" using \<open>x \<in> classes (k + 1) t j\<close> unfolding classes_def cube_def by auto
    then have "x 0 < t" using \<open>x 0 \<noteq> t\<close> by simp
    define f where "f \<equiv> restrict x ({..<1::nat})"
    define g where "g \<equiv> restrict (\<lambda>i. x (i + 1)) {0..<k}"

    have "join f g 1 k = x" unfolding join_def 
    proof 
      fix xa
      consider "xa \<in> {..<1}" | "xa \<in> {1..<1+k}" | "xa \<notin> {..<1} \<and> xa \<notin> {1..<1+k}" by blast
      then show "(if xa \<in> {..<1} then f xa else if xa \<in> {1..<1 + k} then g (xa - 1) else undefined) = x xa"
      proof cases
        case 1
        then have "(if xa \<in> {..<1} then f xa else if xa \<in> {1..<1 + k} then g (xa - 1) else undefined) = f xa" by auto
        also have " ... = x xa" using 1 unfolding f_def by force
        finally show ?thesis .
      next
        case 2
        then have "(if xa \<in> {..<1} then f xa else if xa \<in> {1..<1 + k} then g (xa - 1) else undefined) = g (xa - 1)" by auto
        also have "... = x ((xa - 1) + 1)" using 2 unfolding g_def by force
        also have "... = x xa" using 2 by force
        finally show ?thesis .
      next
        case 3
        have "classes (k+1) t j \<subseteq> cube (k+1) (t+1)" unfolding classes_def by blast
        then have "x xa = undefined" using 3 \<open>x \<in> classes (k+1) t j\<close> unfolding cube_def by auto
        then show ?thesis using 3 by presburger
      qed
    qed
    moreover have "f \<in> classes 1 t j" sorry
    moreover have "g \<in> classes k t j" sorry
    ultimately show "x \<in> {join f g 1 k |f g. f \<in> classes 1 t j \<and> g \<in> classes k t j}" by auto
  qed
next
  show "{join f g 1 k |f g. f \<in> classes 1 t j \<and> g \<in> classes k t j} \<subseteq> classes (k + 1) t j" sorry
qed

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
  using assms unfolding cube_def is_subspace_def by blast



text \<open>The induction step of theorem 4. Heart of the proof\<close>
text \<open>
Proof sketch/idea:
  * we prove lhj r t (k+1) for all r at once. That means we assume hj r t for all r, and lhj r t k' for all r (and all dimensions k' less than k+1)
  * remember: hj -> statement about monochromatic lines, lhj -> statement about layered subspaces (k-dimensional)
  * core idea: to construct (k+1)-dimensional subspace, use (by induction) k-dimensional subspace and (by assumption) 1-dimensional subspace (line) in some natural way (ensuring the colorings satisfy the requisite conditions)

In detail:
  - let \<chi> be an r-coloring, for which we wish to show that there exists a layered (k+1)-dimensional subspace.
  - (SECTION 1) by our assumptions, we can obtain a layered k-dimensional subspace S (w.r.t. r-colorings) and a layered line L (w.r.t. to s-colorings, where s=f(r) is constructed from r to facilitate our main proof; details irrelevant)
  - let m be the dimension of the cube in which the layered k-dimensional subspace S exists
  - let n' be the dimension of the cube in which the layered line L exists
  - we claim that the layered (k+1)-dimensional subspace we are looking for exists in the (m+n')-dimensional cube
    # concretely, we construct these (m+n')-dimensional elements (i.e. tuples) by setting the first n' coordinates to points on the line, and the last m coordinates to points on the subspace.
    # (SECTION 2) this construction yields a subspace (i.e. satisfying the subspace properties). We call this T''. 
    # We prove it is a subspace in SECTION 3. In SECTION 4, we show it is layered.
\<close>

lemma thm4_step: 
  fixes   r k
  assumes "t > 0"
    and "k \<ge> 1"
    and "True" 
    and "(\<And>r k'. k' \<le> k \<Longrightarrow> lhj r t k')" 
    and "r > 0"
  shows   "lhj r t (k+1)"
proof-
  obtain m where m_props: "(m > 0 \<and> (\<forall>M' \<ge> m. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. layered_subspace S k M' t r \<chi>)))" using assms(4)[of "k" "r"] unfolding lhj_def  by blast
  define s where "s \<equiv> r^((t + 1)^m)"
  obtain n' where n'_props: "(n' > 0 \<and> (\<forall>N \<ge> n'. \<forall>\<chi>. \<chi> \<in> (cube N (t + 1)) \<rightarrow>\<^sub>E {..<s::nat} \<longrightarrow> (\<exists>S. layered_subspace S 1 N t s \<chi>)))" using assms(2) assms(4)[of "1" "s"] unfolding lhj_def by auto 

  have cr: "(\<exists>T. layered_subspace T (k + 1) (M') t r \<chi>)" if \<chi>_prop: "\<chi> \<in> cube M' (t + 1) \<rightarrow>\<^sub>E {..<r}" and M'_prop: "M' \<ge> n' + m" for \<chi> M'
  proof -
    define d where "d \<equiv> M' - (n' + m)"
    define n where "n \<equiv> n' + d"
    have "n \<ge> n'" unfolding n_def d_def by simp
    have "n + m = M'" unfolding n_def d_def using M'_prop by simp
    have "\<forall>\<chi>. \<chi> \<in> (cube n (t + 1)) \<rightarrow>\<^sub>E {..<s::nat} \<longrightarrow> (\<exists>S. layered_subspace S 1 n t s \<chi>)" using n'_props \<open>n \<ge> n'\<close> by blast
    have line_subspace_s: "\<forall>\<chi>. \<chi> \<in> (cube n (t + 1)) \<rightarrow>\<^sub>E {..<s::nat} \<longrightarrow> (\<exists>S. layered_subspace S 1 n t s \<chi> \<and> is_line (\<lambda>s\<in>{..<t+1}. S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) n (t+1))"
    proof(safe)
      fix \<chi>
      assume a: "\<chi> \<in> cube n (t + 1) \<rightarrow>\<^sub>E {..<s}"
      then have "(\<exists>S. layered_subspace S 1 n t s \<chi>)" 
        using \<open>\<forall>\<chi>. \<chi> \<in> cube n (t + 1) \<rightarrow>\<^sub>E {..<s} \<longrightarrow> (\<exists>S. layered_subspace S 1 n t s \<chi>)\<close> by presburger
      then obtain L where "layered_subspace L 1 n t s \<chi>" by blast
      then have "is_subspace L 1 n (t+1)" unfolding layered_subspace_def by simp
      then have "is_line (\<lambda>s\<in>{..<t+1}. L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) n (t + 1)" using dim1_subspace_is_line[of "t+1" "L" "n"] assms(1) by simp
      then show "\<exists>S. layered_subspace S 1 n t s \<chi> \<and> is_line (\<lambda>s\<in>{..<t + 1}. S (SOME p. p \<in> cube 1 (t+1) \<and> p 0 = s)) n (t + 1)" using \<open>layered_subspace L 1 n t s \<chi>\<close> by auto
    qed

(** SECTION 1: OBTAINING THE SUBSPACES, CONSTRUCTING THE COLORINGS, AND PROVING RELEVANT FACTS **)

(* \<chi>L is \<chi>* in the book, an s-coloring; see s_colored a couple of lines below *)
    define \<chi>L where "\<chi>L \<equiv> (\<lambda>x \<in> cube n (t+1). (\<lambda>y \<in> cube m (t + 1). \<chi> (join x y n m)))"
    have A: "\<forall>x \<in> cube n (t+1). \<forall>y \<in> cube m (t+1). \<chi> (join x y n m) \<in> {..<r}"
    proof(safe)
      fix x y
      assume "x \<in> cube n (t+1)" "y \<in> cube m (t+1)"
      then have "join x y n m \<in> cube (n+m) (t+1)" using join_cubes[of x n t y m] by simp
      then show "\<chi> (join x y n m) < r" using \<chi>_prop \<open>n + m = M'\<close> by blast 
    qed
    have \<chi>L_prop: "\<chi>L \<in> cube n (t+1) \<rightarrow>\<^sub>E cube m (t+1) \<rightarrow>\<^sub>E {..<r}" using A by (auto simp: \<chi>L_def)

    have "card (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) = (card {..<r}) ^ (card (cube m (t+1)))"  apply (subst card_PiE) unfolding cube_def apply (meson finite_PiE finite_lessThan)  
      using prod_constant by blast
    also have "... = r ^ (card (cube m (t+1)))" by simp
    also have "... = r ^ ((t+1)^m)" using cube_card unfolding cube_def by simp
    finally have "card (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) = r ^ ((t+1)^m)" .
    then have s_colored: "card (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) = s" unfolding s_def by simp
    have "s > 0" using assms(5) unfolding s_def by simp
    then obtain \<phi> where \<phi>_prop: "bij_betw \<phi> (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) {..<s}" using ex_bij_betw_nat_finite_2[of "cube m (t+1) \<rightarrow>\<^sub>E {..<r}" "s"] s_colored by blast
    define \<chi>L_s where "\<chi>L_s \<equiv> (\<lambda>x\<in>cube n (t+1). \<phi> (\<chi>L x))"
    have "\<chi>L_s \<in> cube n (t+1) \<rightarrow>\<^sub>E {..<s}"
    proof
      fix x assume a: "x \<in> cube n (t+1)"
      then have "\<chi>L_s x = \<phi> (\<chi>L x)" unfolding \<chi>L_s_def by simp
      moreover have "\<chi>L x \<in> (cube m (t+1) \<rightarrow>\<^sub>E {..<r})" using a \<chi>L_def \<chi>L_prop unfolding \<chi>L_def by blast
      moreover have "\<phi> (\<chi>L x) \<in> {..<s}" using \<phi>_prop calculation(2) unfolding bij_betw_def by blast
      ultimately show "\<chi>L_s x \<in> {..<s}" by auto
    qed (auto simp: \<chi>L_s_def)
      (* L is the layered line which we obtain from the monochromatic line guaranteed to exist in the assumption hj s t *)
    then obtain L where L_prop: "layered_subspace L 1 n t s \<chi>L_s" using line_subspace_s by blast
    define L_line where "L_line \<equiv> (\<lambda>s\<in>{..<t+1}. L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s))"
    have L_line_base_prop: "\<forall>s \<in> {..<t+1}. L_line s \<in> cube n (t+1)" using assms(1) dim1_subspace_is_line[of "t+1" "L" "n"] L_prop aux2[of L_line n "t+1"] unfolding layered_subspace_def L_line_def by auto

(* \<chi>S is \<chi>** in book, an r-coloring *)
    define \<chi>S where "\<chi>S \<equiv> (\<lambda>y\<in>cube m (t+1). \<chi> (join (L_line 0) y n m))"
    have "\<chi>S \<in> (cube m (t + 1)) \<rightarrow>\<^sub>E {..<r::nat}"
    proof
    	fix x assume a: "x \<in> cube m (t+1)"
    	then have "\<chi>S x = \<chi> (join (L_line 0) x n m)" unfolding \<chi>S_def by simp
    	moreover have "L_line 0 = L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = 0)" using L_prop assms(1) unfolding L_line_def by simp
    	moreover have "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = 0) \<in> cube 1 (t+1)" using cube_props(4)[of "t+1"] using assms(1) by auto 
    	moreover have "L \<in> cube 1 (t+1) \<rightarrow>\<^sub>E cube n (t+1)" using L_prop unfolding layered_subspace_def is_subspace_def by blast
    	moreover have "L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = 0) \<in> cube n (t+1)" using calculation (3,4) unfolding cube_def by auto
    	moreover have "join (L_line 0) x n m \<in> cube (n + m) (t+1)" using join_cubes a calculation(2, 5) by auto
    	ultimately show "\<chi>S x \<in> {..<r}" using A a by fastforce
    qed (auto simp: \<chi>S_def)
      (* S is the k-dimensional layered subspace as a consequence of the IH. Note the coloring is \<chi>S, an r-coloring *)
    then obtain S where S_prop: "layered_subspace S k m t r \<chi>S" using assms(4) m_props by blast
        (* L_line i returns the i-th point of the line *)


(* ------------------------------------------------------------------------------------------------------------------------------ *)


(** SECTION 2: CONSTRUCTING THE GOAL SUBSPACE T'' **)

(* T is the set as defined in the book; it represents the (k+1)-dim subspace as a set. In this construction, subspaces are functions whose image is a set such as T. See below \<rightarrow> im_T''_eq_T *)
    define imT where "imT \<equiv> {join (L_line i) s n m | i s . i \<in> {..<t+1} \<and> s \<in> S ` (cube k (t+1))}" (* x\<^sub>is *)
    define T' where "T' \<equiv> (\<lambda>x \<in> cube 1 (t+1). \<lambda>y \<in> cube k (t+1). join (L_line (x 0)) (S y) n m)"
    have T'_prop: "T' \<in> cube 1 (t+1) \<rightarrow>\<^sub>E cube k (t+1) \<rightarrow>\<^sub>E cube (n + m) (t+1)"
    proof
      fix x assume a: "x \<in> cube 1 (t+1)"
      show "T' x \<in> cube k (t + 1) \<rightarrow>\<^sub>E cube (n + m) (t + 1)"
      proof
        fix y assume b: "y \<in> cube k (t+1)"
        then have "T' x y = join (L_line (x 0)) (S y) n m" using a unfolding T'_def by simp
        moreover have "L_line (x 0) \<in> cube n (t+1)" using a L_line_base_prop unfolding cube_def by blast
        moreover have "S y \<in> cube m (t+1)" using subspace_elems_embed[of "S" "k" "m" "t+1"] S_prop b  unfolding layered_subspace_def by blast
        ultimately show "T' x y \<in> cube (n + m) (t + 1)" using join_cubes by presburger
      next
      qed (unfold T'_def; use a in simp)
   	qed (auto simp: T'_def)

   	define T''' where "T''' \<equiv> (\<lambda>x \<in> cube (k + 1) (t + 1). join (L_line (x 0)) (S (\<lambda>y \<in> {..<k}. x (y + 1))) n m)"
   	have "T''' \<in> cube (k+1) (t+1) \<rightarrow>\<^sub>E cube (n+m) (t+1)"
   	proof
   	  fix x
   	  assume a: "x \<in> cube (k+1) (t+1)"
   	  then have "L_line (x 0) \<in> cube n (t+1)" using L_line_base_prop unfolding cube_def 
   	    by (metis PiE_mem add_gr_0 lessThan_iff less_numeral_extra(1))
   	  moreover have "(\<lambda>y \<in> {..<k}. x (y + 1)) \<in> cube k (t+1)" 
   	    using \<open>x \<in> cube (k + 1) (t + 1)\<close> split_cube(2) by blast
   	  moreover have "S (\<lambda>y \<in> {..<k}. x (y + 1)) \<in> cube m (t+1)" 
   	    using S_prop calculation(2) layered_subspace_def subspace_elems_embed by fastforce
   	  ultimately show "T''' x \<in> cube (n+m) (t+1)" using join_cubes a unfolding T'''_def  by auto
   	qed (auto simp: T'''_def)

   	define T where "T \<equiv> (\<lambda>x \<in> cube (k + 1) (t+1). T' (\<lambda>y \<in> {..<1}. x y) (\<lambda>y \<in> {..<k}. x (y + 1)))"
   	have T_prop: "T \<in> cube (k+1) (t+1) \<rightarrow>\<^sub>E cube (n+m) (t+1)"
   	proof
   	  fix x assume a: "x \<in> cube (k+1) (t+1)"
   	  then have "T x = T' (\<lambda>y \<in> {..<1}. x y) (\<lambda>y \<in> {..<k}. x (y + 1))" unfolding T_def by auto
   	  moreover have "(\<lambda>y \<in> {..<1}. x y) \<in> cube 1 (t+1)" using a unfolding cube_def by auto
   	  moreover have "(\<lambda>y \<in> {..<k}. x (y + 1)) \<in> cube k (t+1)" using a unfolding cube_def by auto
   	  moreover have "T' (\<lambda>y \<in> {..<1}. x y) (\<lambda>y \<in> {..<k}. x (y + 1)) \<in> cube (n + m) (t+1)" using T'_prop calculation unfolding T'_def by blast
   	  ultimately show "T x \<in> cube (n + m) (t+1)" by argo
   	qed (auto simp: T_def)

   	have im_T_eq_imT: "T ` cube (k+1) (t+1) = imT"
   	proof
   	  show "T ` cube (k + 1) (t + 1) \<subseteq> imT"
   	  proof
   	    fix x assume "x \<in> T ` cube (k+1) (t+1)"
   	    then obtain y where y_prop: "y \<in> cube (k+1) (t+1) \<and> x = T y" by blast
   	    then have "T y = T' (\<lambda>i \<in> {..<1}. y i) (\<lambda>i \<in> {..<k}. y (i + 1))" unfolding T_def by simp
   	    moreover have "(\<lambda>i \<in> {..<1}. y i) \<in> cube 1 (t+1)" using y_prop unfolding cube_def by auto
   	    moreover have "(\<lambda>i \<in> {..<k}. y (i + 1)) \<in> cube k (t+1)" using y_prop unfolding cube_def by auto
   	    moreover have " T' (\<lambda>i \<in> {..<1}. y i) (\<lambda>i \<in> {..<k}. y (i + 1)) = join (L_line ((\<lambda>i \<in> {..<1}. y i) 0)) (S (\<lambda>i \<in> {..<k}. y (i + 1))) n m" using calculation unfolding T'_def by auto
   	    ultimately have *: "T y = join (L_line ((\<lambda>i \<in> {..<1}. y i) 0)) (S (\<lambda>i \<in> {..<k}. y (i + 1))) n m" by simp

   	    have "(\<lambda>i \<in> {..<1}. y i) 0 \<in> {..<t+1}" using y_prop unfolding cube_def by auto
   	    moreover have "S (\<lambda>i \<in> {..<k}. y (i + 1)) \<in> S ` (cube k (t+1))" 
   	      using \<open>(\<lambda>i\<in>{..<k}. y (i + 1)) \<in> cube k (t + 1)\<close> by blast
   	    ultimately have "T y \<in> imT" using * unfolding imT_def by blast
   	    then show "x \<in> imT" using y_prop by simp
   	  qed

   	  show "imT \<subseteq> T ` cube (k + 1) (t + 1)" 
   	  proof
   	    fix x assume "x \<in> imT"
   	    then obtain i sx sxinv where isx_prop: "x = join (L_line i) sx n m \<and> i \<in> {..<t+1} \<and> sx \<in> S ` (cube k (t+1)) \<and> sxinv \<in> cube k (t+1) \<and> S sxinv = sx" unfolding imT_def by blast
   	    let ?f1 = "(\<lambda>j \<in> {..<1::nat}. i)"
   	    let ?f2 = "sxinv"
   	    have "?f1 \<in> cube 1 (t+1)" using isx_prop unfolding cube_def by simp
   	    moreover have "?f2 \<in> cube k (t+1)" using isx_prop by blast
   	    moreover have "x = join (L_line (?f1 0)) (S ?f2) n m" by (simp add: isx_prop)
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
   	    ultimately have "T' ?f1 ?f2 = T f" using \<open>f \<in> cube (k+1) (t+1)\<close> unfolding T_def by simp
   	    then show "x \<in> T ` cube (k + 1) (t + 1)" using * 
   	      using \<open>f \<in> cube (k + 1) (t + 1)\<close> by blast
   	  qed


   	qed
   	have "imT \<subseteq> cube (n + m) (t+1)"
   	proof
   	  fix x assume a: "x\<in>imT"
   	  then obtain i sx where isx_props: "x = join (L_line i) sx n m \<and> i \<in> {..<t+1} \<and> sx \<in> S ` (cube k (t+1))" unfolding imT_def by blast
   	  then have "L_line i \<in> cube n (t+1)" using L_line_base_prop by blast
   	  moreover have "sx \<in> cube m (t+1)" using subspace_elems_embed[of "S" "k" "m" "t+1"] S_prop isx_props unfolding layered_subspace_def by blast
   	  ultimately show "x \<in> cube (n + m) (t+1)" using join_cubes[of "L_line i" "n" "t" sx m] isx_props by simp 
   	qed

   	




(* ------------------------------------------------------------------------------------------------------------------------------ *)

(** SECTION 3: PROVING THAT T IS A SUBSPACE **)

(* To prove entities are subspaces, we have to provide the B and f satisfying the subspace properties. We construct BT and fT from BS, fS and BL, fL, which correspond to the k-dim subspace S and the 1-dimensional subspace (~ line) L, respectively. *)
   	obtain BS fS where BfS_props: "disjoint_family_on BS {..k}" "\<Union>(BS ` {..k}) = {..<m}" "({} \<notin> BS ` {..<k})" " fS \<in> (BS k) \<rightarrow>\<^sub>E {..<t+1}" "S \<in> (cube k (t+1)) \<rightarrow>\<^sub>E (cube m (t+1)) " "(\<forall>y \<in> cube k (t+1). (\<forall>i \<in> BS k. S y i = fS i) \<and> (\<forall>j<k. \<forall>i \<in> BS j. (S y) i = y j))" using S_prop unfolding layered_subspace_def is_subspace_def by auto

   	obtain BL fL where BfL_props: "disjoint_family_on BL {..1}" "\<Union>(BL ` {..1}) = {..<n}"  "({} \<notin> BL ` {..<1})" "fL \<in> (BL 1) \<rightarrow>\<^sub>E {..<t+1}" "L \<in> (cube 1 (t+1)) \<rightarrow>\<^sub>E (cube n (t+1))" "(\<forall>y \<in> cube 1 (t+1). (\<forall>i \<in> BL 1. L y i = fL i) \<and> (\<forall>j<1. \<forall>i \<in> BL j. (L y) i = y j))" using L_prop unfolding layered_subspace_def is_subspace_def by auto

   	define Bstat where "Bstat \<equiv> shiftset n (BS k) \<union> BL 1"
   	define Bvar where "Bvar \<equiv> (\<lambda>i::nat. (if i = 0 then BL 0 else shiftset n (BS (i - 1))))"
   	define BT where "BT \<equiv> (\<lambda>i \<in> {..<k+1}. Bvar i)((k+1):=Bstat)"
   	define fT where "fT \<equiv> (\<lambda>x. (if x \<in> BL 1 then fL x else (if x \<in> shiftset n (BS k) then fS (x - n) else undefined)))"


(* useful facts *)
   	have fax1: "shiftset n (BS k) \<inter> BL 1 = {}"  using BfL_props BfS_props unfolding shiftset_def by auto
    have fax2: "BL 0 \<inter> (\<Union>i\<in>{..<k}. shiftset n (BS i)) = {}" using BfL_props BfS_props unfolding shiftset_def by auto
    have fax3: "\<forall>i \<in> {..<k}. BL 0 \<inter> shiftset n (BS i) = {}" using BfL_props BfS_props unfolding shiftset_def by auto
    have fax4: "\<forall>i \<in> {..<k+1}. \<forall>j \<in> {..<k+1}. i \<noteq> j \<longrightarrow> shiftset n (BS i) \<inter> shiftset n (BS j) = {}" using shiftset_disjoint_family[of BS k] BfS_props unfolding disjoint_family_on_def by simp 
    have fax5: "\<forall>i \<in> {..<k+1}. Bvar i \<inter> Bstat = {}"
  	proof
  	  fix i assume a: "i \<in> {..<k+1}"
  	  show "Bvar i \<inter> Bstat = {}"
  	  proof (cases i)
  	    case 0
  	    then have "Bvar i = BL 0" unfolding Bvar_def by simp
  	    moreover have "BL 0 \<inter> BL 1 = {}" using BfL_props unfolding disjoint_family_on_def by simp
  	    moreover have "shiftset n (BS k) \<inter> BL 0 = {}" using BfL_props BfS_props unfolding shiftset_def by auto
  	    ultimately show ?thesis unfolding Bstat_def by blast
  	  next
  	    case (Suc nat)
  	    then have "Bvar i = shiftset n (BS nat)" unfolding Bvar_def by simp
  	    moreover have "shiftset n (BS nat) \<inter> BL 1 = {}" using BfS_props BfL_props a Suc unfolding shiftset_def by auto
  	    moreover have "shiftset n (BS nat) \<inter> shiftset n (BS k) = {}" using a Suc fax4 by simp
  	    ultimately show ?thesis unfolding Bstat_def by blast
  	  qed
  	qed

  	have shiftsetnotempty: "\<forall>n i. BS i \<noteq> {} \<longrightarrow> shiftset n (BS i) \<noteq> {}" unfolding shiftset_def by blast

(* facts F1 ... F5 are the disjuncts in the subspace definition *)  
    have "Bvar ` {..<k+1} = BL ` {..<1} \<union> Bvar ` {1..<k+1}" unfolding Bvar_def by force
    also have " ... = BL ` {..<1} \<union> {shiftset n (BS i) | i . i \<in> {..<k}} " unfolding Bvar_def by fastforce  
    moreover have "{} \<notin> BL ` {..<1}" using BfL_props by auto
    moreover have "{} \<notin> {shiftset n (BS i) | i . i \<in> {..<k}}" using BfS_props shiftsetnotempty 
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


  	have F3: "\<Union>(BT ` {..k+1}) = {..<n + m}"
  	proof 
  	  show "\<Union> (BT ` {..k + 1}) \<subseteq> {..<n + m}"
  	  proof
  	    fix x assume "x \<in> \<Union> (BT ` {..k + 1})"
  	    then obtain i where i_prop: "i \<in> {..k+1} \<and> x \<in> BT i" by blast
  	    then consider "i = k +1" | "i \<in> {..<k+1}" by fastforce
  	    then show "x \<in> {..<n + m}"
  	    proof (cases)
  	      case 1
  	      then have "x \<in> Bstat" using i_prop unfolding BT_def by simp
  	      then have "x \<in> BL 1 \<or> x \<in> shiftset n (BS k)" unfolding Bstat_def by blast
  	      then have "x \<in> {..<n} \<or> x \<in> {n..<n+m}" using BfL_props shiftset_image[of BS k m n] 
  	        by (metis BfS_props(2) UN_iff atMost_iff order_refl) 
  	      then show ?thesis by auto
  	    next
  	      case 2
  	      then have "x \<in> Bvar i" using i_prop unfolding BT_def by simp
  	      then have "x \<in> BL 0 \<or> x \<in> shiftset n (BS (i - 1))" unfolding Bvar_def by metis
  	      then show ?thesis
  	      proof (elim disjE)
  	        assume "x \<in> BL 0"
  	        then have "x \<in> {..<n}" using BfL_props by auto
  	        then show "x \<in> {..<n + m}" by simp
  	      next
  	        assume a: "x \<in> shiftset n (BS (i - 1))"
  	        then have "i - 1 \<le> k" 
  	          by (meson atMost_iff i_prop le_diff_conv) 
  	        then have "shiftset n (BS (i - 1)) \<subseteq> {n..<n+m}" using shiftset_image[of BS k m n] BfS_props by auto
  	        then show "x \<in> {..<n+m}" using a by auto
  	      qed
  	    qed
  	  qed

  	  show "{..<n + m} \<subseteq> \<Union> (BT ` {..k + 1})"
  	  proof 
  	    fix x assume "x \<in> {..<n + m}"
  	    then consider "x \<in> {..<n}" | "x \<in> {n..<n+m}" by fastforce
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
  	      then have "x \<in> (\<Union>i\<le>k. shiftset n (BS i))" using shiftset_image[of BS k m n] BfS_props by simp
  	      then obtain i where i_prop: "i \<le> k \<and> x \<in> shiftset n (BS i)" by blast
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
  	  then have "x \<in> BL 1 \<or> x \<in> shiftset n (BS k)" unfolding Bstat_def by auto
  	  then show "fT x \<in> {..<t + 1}"
  	  proof (elim disjE)
  	    assume "x \<in> BL 1"
  	    then have "fT x = fL x" unfolding fT_def by simp
  	    then show "fT x \<in> {..<t+1}" using BfL_props \<open>x \<in> BL 1\<close> by auto
  	  next
  	    assume a: "x \<in> shiftset n (BS k)"
  	    then have "fT x = fS (x - n)" unfolding fT_def by (metis IntI emptyE fax1)
  	    moreover have "x - n \<in> BS k" using a unfolding shiftset_def by auto
  	    ultimately show "fT x \<in> {..<t+1}" using BfS_props by auto
  	  qed
  	qed(auto simp: BT_def Bstat_def fT_def)
  	find_theorems "\<forall>_\<in>_._"

  	have F5: "((\<forall>i \<in> BT (k + 1). T y i = fT i) \<and> (\<forall>j<k+1. \<forall>i \<in> BT j. (T y) i = y j))" if "y \<in> cube (k + 1) (t + 1)" for y
  	proof(intro conjI allI impI ballI)
  	  fix i assume "i \<in> BT (k + 1)"
  	  then have "i \<in> Bstat" unfolding BT_def by simp
  	  then consider "i \<in> shiftset n (BS k)" |  "i \<in> BL 1" unfolding Bstat_def by blast
  	  then show "T y i = fT i"
  	  proof (cases)
  	    case 1
  	    then have "\<exists>s<m. i = n + s" unfolding shiftset_def using BfS_props(2) by auto
  	    then obtain s where s_prop: "s < m \<and> i = n + s" by blast
  	    then have *: " i \<in> {n..<n+m}" by simp
  	    have "i \<notin> BL 1" using 1 fax1 by auto
  	    then have "fT i = fS (i - n)" using 1 unfolding fT_def by simp
  	    then have **: "fT i = fS s" using s_prop by simp

  	    have XX: "(\<lambda>z \<in> {..<k}. y (z + 1)) \<in> cube k (t+1)" using split_cube that by simp
  	    have XY: "s \<in> BS k" using  s_prop  1 unfolding shiftset_def by auto

  	    from that have "T y i = (T' (\<lambda>z \<in> {..<1}. y z) (\<lambda>z \<in> {..<k}. y (z + 1))) i" unfolding T_def by auto
  	    also have "... = (join (L_line ((\<lambda>z \<in> {..<1}. y z) 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) n m) i" using split_cube that unfolding T'_def by simp
  	    also have "... = (join (L_line (y 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) n m) i" by simp
  	    also have "... = (S (\<lambda>z \<in> {..<k}. y (z + 1))) s" using * s_prop unfolding join_def by simp
  	    also have "... = fS s" using XX XY BfS_props(6) by blast
  	    finally show ?thesis using ** by simp
  	  next
  	    case 2
  	    have XZ: "y 0 \<in> {..<t+1}" using that unfolding cube_def by auto
  	    have XY: "i \<in> {..<n}" using 2 BfL_props(2) by blast
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

  	    from that have "T y i = (T' (\<lambda>z \<in> {..<1}. y z) (\<lambda>z \<in> {..<k}. y (z + 1))) i" unfolding T_def by auto
  	    also have "... = (join (L_line ((\<lambda>z \<in> {..<1}. y z) 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) n m) i" using split_cube that unfolding T'_def by simp
  	    also have "... = (L_line ((\<lambda>z \<in> {..<1}. y z) 0)) i" using XY unfolding join_def by simp
  	    also have "... = L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = ((\<lambda>z \<in> {..<1}. y z) 0)) i" using XZ unfolding L_line_def by auto
  	    also have "... = L (\<lambda>z \<in> {..<1}. y z) i" using some_eq_restrict by simp
  	    also have "... = fL i" using BfL_props(6) XX 2 by blast
  	    also have "... = fT i" using 2 unfolding fT_def by simp
  	    finally show ?thesis .
  	  qed

  	next

(*  	define Bstat where "Bstat \<equiv> shiftset n' (BS k) \<union> BL 1"
   	define Bvar where "Bvar \<equiv> (\<lambda>i::nat. (if i = 0 then BL 0 else shiftset n' (BS (i - 1))))"
   	define BT where "BT \<equiv> (\<lambda>i \<in> {..<k+1}. Bvar i)((k+1):=Bstat)"
   	define fT where "fT \<equiv> (\<lambda>x. (if x \<in> BL 1 then fL x else (if x \<in> shiftset n' (BS k) then fS (x - n') else undefined)))"
    define T where "T \<equiv> (\<lambda>x \<in> cube (k + 1) (t+1). T' (\<lambda>y \<in> {..<1}. x y) (\<lambda>y \<in> {..<k}. x (y + 1)))"
    define T' where "T' \<equiv> (\<lambda>x \<in> cube 1 (t+1). \<lambda>y \<in> cube k (t+1). join (L_line (x 0)) (S y) n' m)"
        "join f g n m \<equiv> (\<lambda>x. if x \<in> {..<n} then f x else (if x \<in> {n..<n+m} then g (x - n) else undefined))"


  obtain BS fS where BfS_props: "disjoint_family_on BS {..k}" "\<Union>(BS ` {..k}) = {..<m}" "({} \<notin> BS ` {..<k})" " fS \<in> (BS k) \<rightarrow>\<^sub>E {..<t+1}" "S \<in> (cube k (t+1)) \<rightarrow>\<^sub>E (cube m (t+1)) " "(\<forall>y \<in> cube k (t+1). (\<forall>i \<in> BS k. S y i = fS i) \<and> (\<forall>j<k. \<forall>i \<in> BS j. (S y) i = y j))" using S_prop unfolding layered_subspace_def is_subspace_def by auto

   	obtain BL fL where BfL_props: "disjoint_family_on BL {..1}" "\<Union>(BL ` {..1}) = {..<n'}"  "({} \<notin> BL ` {..<1})" "fL \<in> (BL 1) \<rightarrow>\<^sub>E {..<t+1}" "L \<in> (cube 1 (t+1)) \<rightarrow>\<^sub>E (cube n' (t+1))" "(\<forall>y \<in> cube 1 (t+1). (\<forall>i \<in> BL 1. L y i = fL i) \<and> (\<forall>j<1. \<forall>i \<in> BL j. (L y) i = y j))" using L_prop unfolding layered_subspace_def is_subspace_def by auto


"(\<forall>y \<in> cube k (t+1). (\<forall>i \<in> BS k. S y i = fS i) \<and> (\<forall>j<k. \<forall>i \<in> BS j. (S y) i = y j))"
*)
  	  fix j i assume "j < k + 1" "i \<in> BT j"
  	  then have i_prop: "i \<in> Bvar j" unfolding BT_def by auto
      consider "j = 0" | "j > 0" by auto
  	  then show "T y i = y j"
  	  proof cases
  	    case 1
  	    then have "i \<in> BL 0" using i_prop unfolding Bvar_def by auto
  	    then have XY: "i \<in> {..<n}" using 1 BfL_props(2) by blast
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

  	    from that have "T y i = (T' (\<lambda>z \<in> {..<1}. y z) (\<lambda>z \<in> {..<k}. y (z + 1))) i" unfolding T_def by auto
  	    also have "... = (join (L_line ((\<lambda>z \<in> {..<1}. y z) 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) n m) i" using split_cube that unfolding T'_def by simp
  	    also have "... = (L_line ((\<lambda>z \<in> {..<1}. y z) 0)) i" using XY unfolding join_def by simp
  	    also have "... = L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = ((\<lambda>z \<in> {..<1}. y z) 0)) i" using XZ unfolding L_line_def by auto
  	    also have "... = L (\<lambda>z \<in> {..<1}. y z) i" using some_eq_restrict by simp
  	    also have "... =  (\<lambda>z \<in> {..<1}. y z) j" using BfL_props(6) XX 1  \<open>i \<in> BL 0\<close> by blast 
  	    also have "... = (\<lambda>z \<in> {..<1}. y z) 0" using 1 by blast
  	    also have "... = y 0" by simp
  	    also have "... = y j" using 1 by simp
  	    finally show ?thesis .
  	  next
  	    case 2
  	    then have "i \<in> shiftset n (BS (j - 1))" using i_prop unfolding Bvar_def by simp
  	    then have "\<exists>s<m. n + s = i" using BfS_props(2) \<open>j < k + 1\<close> unfolding shiftset_def by force 
  	    then obtain s where s_prop: "s < m" "i = s + n" by auto
         then have *: " i \<in> {n..<n+m}" by simp

  	    have XX: "(\<lambda>z \<in> {..<k}. y (z + 1)) \<in> cube k (t+1)" using split_cube that by simp
  	    have XY: "s \<in> BS (j - 1)" using s_prop 2 \<open>i \<in> shiftset n (BS (j - 1))\<close> unfolding shiftset_def by force

  	    from that have "T y i = (T' (\<lambda>z \<in> {..<1}. y z) (\<lambda>z \<in> {..<k}. y (z + 1))) i" unfolding T_def by auto
  	    also have "... = (join (L_line ((\<lambda>z \<in> {..<1}. y z) 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) n m) i" using split_cube that unfolding T'_def by simp
  	    also have "... = (join (L_line (y 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) n m) i" by simp
  	    also have "... = (S (\<lambda>z \<in> {..<k}. y (z + 1))) s" using * s_prop unfolding join_def by simp
  	    also have "... = (\<lambda>z \<in> {..<k}. y (z + 1)) (j-1)" using XX XY BfS_props(6) 2 \<open>j < k + 1\<close> by auto
  	    also have "... = y j" using 2 \<open>j < k + 1\<close> by force
  	    finally show ?thesis .
  	  qed
  	qed
  	


  	from F1 F2 F3 F4 F5 have subspace_T: "is_subspace T (k+1) (n+m) (t+1)" unfolding is_subspace_def using T_prop by metis


(* ------------------------------------------------------------------------------------------------------------------------------ *)


(** SECTION 4: PROVING T IS LAYERED **)

    (* This redefinition of the classes makes proving the layered property easier *)
    define T_class where "T_class \<equiv> (\<lambda>j\<in>{..k}. {join (L_line i) s n m | i s . i \<in> {..<t} \<and> s \<in> S ` (classes k t j)})(k+1:= {join (L_line t) (SOME s. s \<in> S ` (cube m (t+1))) n m})"
    (* Proving the equivalence *) 
    have classprop: "T_class j = T ` classes (k + 1) t j" if j_prop: "j \<le> k" for j
    proof
      show "T_class j \<subseteq> T ` classes (k + 1) t j"
      proof
        fix x assume "x \<in> T_class j"
        from that have "T_class j = {join (L_line i) s n m | i s . i \<in> {..<t} \<and> s \<in> S ` (classes k t j)}" unfolding T_class_def by simp
        then obtain i s where is_defs: "x = join (L_line i) s n m \<and> i < t \<and> s \<in> S ` (classes k t j)" using \<open>x \<in> T_class j\<close> unfolding T_class_def by auto
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

        moreover have "x = T p"
        proof-
          have loc_useful:"(\<lambda>y \<in> {..<k}. p (y + 1)) = (\<lambda>z \<in> {..<k}. y z)" using ** by auto
          have "T p = T' (\<lambda>y \<in> {..<1}. p y) (\<lambda>y \<in> {..<k}. p (y + 1))" using p_in_cube unfolding T_def by auto
     
          have "T' (\<lambda>y \<in> {..<1}. p y) (\<lambda>y \<in> {..<k}. p (y + 1)) = join (L_line ((\<lambda>y \<in> {..<1}. p y) 0)) (S (\<lambda>y \<in> {..<k}. p (y + 1))) n m" using split_cube p_in_cube unfolding T'_def by simp
          also have "... = join (L_line (p 0)) (S (\<lambda>y \<in> {..<k}. p (y + 1))) n m" by simp
          also have "... = join (L_line i) (S (\<lambda>y \<in> {..<k}. p (y + 1))) n m" by (simp add: **)
          also have "... = join (L_line i) (S (\<lambda>z \<in> {..<k}. y z)) n m" using loc_useful by simp
          also have "... = join (L_line i) (S y) n m" using y_prop * unfolding cube_def by auto
          also have "... = x" using is_defs y_prop by simp
          finally show "x = T p" 
            using \<open>T p = T' (restrict p {..<1}) (\<lambda>y\<in>{..<k}. p (y + 1))\<close> by presburger
        qed
        ultimately show "x \<in> T ` classes (k + 1) t j" by blast
      qed
    next
      show "T ` classes (k + 1) t j \<subseteq> T_class j"
      proof
        fix x assume "x \<in> T ` classes (k+1) t j"
        then obtain y where y_prop: "y \<in> classes (k+1) t j \<and> T y = x" by blast
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
        then have "T y = T' (\<lambda>g \<in> {..<1}. y g) z  " using y_prop classes_subset_cube[of "k+1" t j] unfolding T_def z_def by auto
        also have " ... = join (L_line ((\<lambda>g \<in> {..<1}. y g) 0)) (S z) n m" unfolding T'_def using \<open>(\<lambda>g \<in> {..<1}. y g) \<in> cube 1 (t+1)\<close> \<open>z \<in> cube k (t+1)\<close> by auto
        also have " ... = join (L_line (y 0)) (S z) n m" by simp
        also have " ... \<in> T_class j" using tr z_in_classes that unfolding T_class_def by force
        finally show "x \<in> T_class j" using y_prop by simp
      qed
    qed
    (* The core case i \<le> k. The case i = k+1 is trivial since k+1 has only one point. *)
    have "\<forall>x \<in> T ` classes (k+1) t i. \<forall>y \<in> T ` classes (k+1) t i.  \<chi> x = \<chi> y \<and> \<chi> x < r" if i_assm: "i \<le> k" for i
    proof (intro ballI)
      fix x y assume a: "x \<in> T ` classes (k + 1) t i" "y \<in> T ` classes (k + 1) t i"
      from that have *: "T ` classes (k+1) t i = T_class i" by (simp add: classprop)
      then have  "x \<in> T_class i " using a by simp
      moreover have **: "T_class i = {join (L_line l) s n m | l s . l \<in> {..<t} \<and> s \<in> S ` (classes k t i)}" using that unfolding T_class_def by simp
      ultimately obtain xs xi where xdefs:  "x = join (L_line xi) xs n m \<and> xi < t \<and> xs \<in> S ` (classes k t i)" by blast

      from * ** obtain ys yi where ydefs: "y = join (L_line yi) ys n m \<and> yi < t \<and> ys \<in> S ` (classes k t i)" using a by auto

      have "(L_line xi) \<in> cube n (t+1)" using L_line_base_prop xdefs by simp
      moreover have "xs \<in> cube m (t+1)" using xdefs S_prop subspace_elems_embed imageE image_subset_iff mem_Collect_eq unfolding layered_subspace_def classes_def  by blast
      ultimately have AA1: "\<chi> x = \<chi>L (L_line xi) xs" using xdefs unfolding \<chi>L_def by simp

      have "(L_line yi) \<in> cube n (t+1)" using L_line_base_prop ydefs by simp
      moreover have "ys \<in> cube m (t+1)" using ydefs S_prop subspace_elems_embed imageE image_subset_iff mem_Collect_eq unfolding layered_subspace_def classes_def  by blast
      ultimately have AA2: "\<chi> y = \<chi>L (L_line yi) ys" using ydefs unfolding \<chi>L_def by simp

      have "\<forall>s<t. \<forall>l < t. \<chi>L_s (L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) = \<chi>L_s (L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = l))" using dim1_layered_subspace_mono_line[of t L n s \<chi>L_s] L_prop assms(1) by blast
      then have mykey: "\<forall>s<t. \<forall>l<t. \<chi>L_s (L_line s) = \<chi>L_s (L_line l)" unfolding L_line_def 
        by (metis (no_types, lifting) add.commute lessThan_iff less_Suc_eq plus_1_eq_Suc restrict_apply)
      have BIGKEY: "\<forall>s<t. \<forall>l<t. \<chi>L (L_line s) = \<chi>L (L_line l)"
      proof (intro allI impI)
        fix s l assume "s < t" "l < t"
        have L1: "\<chi>L (L_line s) \<in> cube m (t + 1) \<rightarrow>\<^sub>E {..<r}" unfolding \<chi>L_def using A L_line_base_prop \<open>s < t\<close> by simp
        have L2: "\<chi>L (L_line l) \<in> cube m (t + 1) \<rightarrow>\<^sub>E {..<r}" unfolding \<chi>L_def using A L_line_base_prop \<open>l < t\<close> by simp
        have "\<phi> (\<chi>L (L_line s)) = \<chi>L_s (L_line s)" unfolding \<chi>L_s_def using \<open>s < t\<close> L_line_base_prop by simp
        also have " ... =  \<chi>L_s (L_line l)" using mykey \<open>s <t\<close> \<open>l < t\<close> by blast
        also have " ... = \<phi> (\<chi>L (L_line l))" unfolding \<chi>L_s_def using L_line_base_prop \<open>l<t\<close> by simp
        finally have "\<phi> (\<chi>L (L_line s)) = \<phi> (\<chi>L (L_line l))" by simp
        then show "\<chi>L (L_line s) = \<chi>L (L_line l)" using \<phi>_prop L_line_base_prop L1 L2 unfolding bij_betw_def inj_on_def by blast
      qed
      then have "\<chi>L (L_line xi) xs = \<chi>L (L_line 0) xs" using xdefs 
        by (metis assms(1))
      also have " ... =  \<chi>S xs" unfolding \<chi>S_def \<chi>L_def using xdefs L_line_base_prop by auto
      also have " ... = \<chi>S ys" using xdefs ydefs layered_eq_classes[of S k m t r \<chi>S] S_prop i_assm by blast
      also have " ... = \<chi>L (L_line 0) ys"  unfolding \<chi>S_def \<chi>L_def using xdefs L_line_base_prop by auto
      also have " ... = \<chi>L (L_line yi) ys" using ydefs 
        by (metis BIGKEY assms(1))
      finally have CORE: "\<chi>L (L_line xi) xs =  \<chi>L (L_line yi) ys" by simp


      then have "\<chi> x = \<chi> y" using AA1 AA2 by simp      
      then show " \<chi> x = \<chi> y \<and> \<chi> x < r" 
        by (metis AA1 BIGKEY PiE_mem \<open>\<chi>S \<in> cube m (t + 1) \<rightarrow>\<^sub>E {..<r}\<close> \<open>\<chi>S xs = \<chi>S ys\<close> \<open>\<chi>L (L_line 0) xs = \<chi>S xs\<close> \<open>ys \<in> cube m (t + 1)\<close> assms(1) lessThan_iff xdefs)

    qed
    then have "\<forall>i\<le>k. \<exists>c<r. \<forall>x \<in> T ` classes (k+1) t i. \<chi> x = c" 
      by (meson assms(5))

    have "\<exists>c<r. \<forall>x \<in> T ` classes (k+1) t (k+1). \<chi> x = c"
    proof -
      have "\<forall>x \<in> classes (k+1) t (k+1). \<forall>u < k + 1. x u = t" unfolding classes_def by auto
      have "(\<lambda>u. t) ` {..<k + 1} \<subseteq> {..<t + 1}" by auto
      then have "\<exists>!y \<in> cube (k+1) (t+1). (\<forall>u < k + 1. y u = t)" using PiE_uniqueness[of "(\<lambda>u. t)" "{..<k+1}" "{..<t+1}"] unfolding cube_def by auto
      then have "\<exists>!y \<in> classes (k+1) t (k+1). (\<forall>u < k + 1. y u = t)" unfolding classes_def using classes_subset_cube[of "k+1" t "k+1"] by auto
      then have "\<exists>!y. y \<in> classes (k+1) t (k+1)" using \<open>\<forall>x \<in> classes (k+1) t (k+1). \<forall>u < k + 1. x u = t\<close> by metis
      have "\<exists>c<r. \<forall>y \<in> classes (k+1) t (k+1). \<chi> (T y) = c" 
      proof -
        have "\<forall>y \<in> classes (k+1) t (k+1). T y \<in> cube (n+m) (t+1)" using T_prop classes_subset_cube by blast
        then have "\<forall>y \<in> classes (k+1) t (k+1). \<chi> (T y) < r" using \<chi>_prop 
          unfolding n_def d_def using M'_prop by auto 
        then show "\<exists>c<r. \<forall>y \<in> classes (k+1) t (k+1). \<chi> (T y) = c" using \<open>\<exists>!y. y \<in> classes (k+1) t (k+1)\<close> by blast
      qed
      then show "\<exists>c<r. \<forall>x \<in> T ` classes (k+1) t (k+1). \<chi> x = c" by blast
    qed
    then have " (\<forall>i \<in> {..k+1}. \<exists>c<r. \<forall>x \<in> T ` classes (k+1) t i. \<chi> x = c)" using \<open>\<forall>i\<le>k. \<exists>c<r. \<forall>x \<in> T ` classes (k+1) t i. \<chi> x = c\<close> 
      by (metis One_nat_def add.right_neutral add_Suc_right atMost_iff less_Suc_eq nat_less_le order_refl)
    then have "(\<forall>i \<in> {..k+1}. \<exists>c<r. \<forall>x \<in> classes (k+1) t i. \<chi> (T x) = c)" by simp
    then have "layered_subspace T (k+1) (n + m) t r \<chi>"  using subspace_T that(1) \<open>n + m = M'\<close> unfolding layered_subspace_def by blast
  	then show ?thesis using \<open>n + m = M'\<close> by blast 
  qed
  then show ?thesis unfolding lhj_def
    by (metis add.commute m_props trans_less_add1)
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
    proof (cases "t > 0")
      case True
      then show ?thesis using thm4_k_1[of "t"] assms 2 by blast
    next
      case False
      then show ?thesis using assms unfolding hj_def lhj_def cube_def by fastforce
    qed
  next
    case 3
    note less
    then show ?thesis
    proof (cases "t > 0 \<and> r > 0")
    	case True
    	then show ?thesis  using thm4_step[of t "k-1" r]
    	  using assms less.IH 3 One_nat_def Suc_pred by fastforce
    next
      case False
      then consider "t = 0" | "t > 0 \<and> r = 0" | "t = 0 \<and> r = 0" by fastforce
      then show ?thesis
      proof cases
        case 1
        then show ?thesis using assms unfolding hj_def lhj_def cube_def by fastforce
      next
        case 2
        then obtain N where N_prop: "N > 0 \<and> (\<forall>N'\<ge>N. \<forall>\<chi>. \<chi> \<in> cube N' t \<rightarrow>\<^sub>E {..<r} \<longrightarrow> (\<exists>L c. c < r \<and> is_line L N' t \<and> (\<forall>y \<in> L ` {..<t}. \<chi> y = c)))" using assms unfolding hj_def by metis
        then have "\<forall>N' \<ge> N. cube N' t \<noteq> {}" unfolding cube_def using 2 by auto
        then have "\<forall>N' \<ge> N. cube N' t \<rightarrow>\<^sub>E {..<r} = {}" using 2 by blast
        then show ?thesis using N_prop unfolding lhj_def 
          by (metis PiE_eq_empty_iff all_not_in_conv cube_def lessThan_iff trans_less_add1) 
      next
        case 3
        then have "\<forall>N' \<chi>. (\<exists>L c. c < r \<and> is_line L N' t \<and> (\<forall>y \<in> L ` {..<t}. \<chi> y = c)) \<Longrightarrow> False" by blast
        then have False using assms 3 unfolding hj_def cube_def by fastforce
        then show ?thesis by blast
      qed
      
    qed
  qed
qed


lemma thm5: assumes "layered_subspace S k n t k \<chi>" and "t > 0"  shows "(\<exists>L. \<exists>c<k. is_line L n (t+1) \<and> (\<forall>y \<in> L ` {..<t+1}. \<chi> y = c))"
proof-
  define x where "x \<equiv> (\<lambda>i\<in>{..k}. \<lambda>j\<in>{..<k}. (if j < k - i then 0 else t))"

  thm is_subspace_def
  thm layered_subspace_def
  have A: "x i \<in> cube k (t + 1)" if "i \<le> k" for i using that unfolding cube_def x_def by simp
  then have "S (x i) \<in> cube n (t+1)" if "i \<le> k" for i using that assms(1) unfolding layered_subspace_def is_subspace_def by fast

  have "\<chi> \<in> cube n (t + 1) \<rightarrow>\<^sub>E {..<k}" using assms unfolding layered_subspace_def by linarith
  then have "\<chi> ` (cube n (t+1)) \<subseteq> {..<k}" by blast
  then have "card (\<chi> ` (cube n (t+1))) \<le> card {..<k}" 
    by (meson card_mono finite_lessThan)
  then have *: "card (\<chi> ` (cube n (t+1))) \<le> k" by auto
  have "k > 0" 
    by (metis assms(1) atMost_iff gr0I layered_subspace_def less_nat_zero_code not_less)
  have "inj_on x {..k}"
  proof -
    have *:"x i1 (k - i2) \<noteq> x i2 (k - i2)" if "i1 \<le> k" "i2 \<le> k" "i1 \<noteq> i2" "i1 < i2" for i1 i2 using that assms(2) unfolding x_def by auto 
    have "\<exists>j<k. x i1 j \<noteq> x i2 j" if "i1 \<le> k" "i2 \<le> k" "i1 \<noteq> i2" for i1 i2
    proof (cases "i1 \<le> i2")
      case True
      then have "k - i2 < k" 
        using \<open>0 < k\<close> that(3) by linarith
      then show ?thesis using that * 
        by (meson True nat_less_le)
    next
      case False
      then have "i2 < i1" by simp
      then show ?thesis using that *[of i2 i1] 
        by (metis diff_less gr_implies_not0 le0 nat_less_le)
    qed
    then have "x i1 \<noteq> x i2" if "i1 \<le> k" "i2 \<le> k" "i1 \<noteq> i2" "i1 < i2" for i1 i2 using that by metis
    then show ?thesis 
      by (metis atMost_iff linear linorder_inj_onI nat_neq_iff)
  qed
  then have "card (x ` {..k}) = card {..k}" using card_image by blast
  then have B: "card (x ` {..k}) = k+1" by simp
  have "x ` {..k} \<subseteq> cube k (t+1)" using A by blast
  then have "S ` x ` {..k} \<subseteq> S ` cube k (t+1)" by fast
  also have "... \<subseteq> cube n (t+1)" 
    by (meson assms(1) layered_subspace_def subspace_elems_embed)
  finally have "S ` x ` {..k} \<subseteq> cube n (t+1)" by blast
  then have "\<chi> ` S ` x ` {..k} \<subseteq> \<chi> ` cube n (t+1)" by auto
  then have "card (\<chi> ` S ` x ` {..k}) \<le> card (\<chi> ` cube n (t+1))" 
    by (simp add: card_mono cube_def finite_PiE)
  also have " ... \<le> k" using * by blast
  also have " ... < k + 1" by auto
  also have " ... = card {..k}" by simp
  also have " ... = card (x ` {..k})" using B by auto
  also have " ... = card (S ` x ` {..k})" using subspace_inj_on_cube 
    by (metis \<open>x ` {..k} \<subseteq> cube k (t + 1)\<close> assms(1) card_image inj_on_subset layered_subspace_def)
  finally have "card (\<chi> ` S ` x ` {..k}) < card (S ` x ` {..k})" by blast
  then have "\<not>inj_on \<chi> (S ` x ` {..k})" using pigeonhole[of \<chi> "S ` x ` {..k}"] by blast
  then have "\<exists>a b. a \<in> S ` x ` {..k} \<and> b \<in> S ` x ` {..k} \<and> a \<noteq> b \<and> \<chi> a = \<chi> b" unfolding inj_on_def by auto
  then obtain ax bx where ab_props: "ax \<in> S ` x ` {..k} \<and> bx \<in> S ` x ` {..k} \<and> ax \<noteq> bx \<and> \<chi> ax = \<chi> bx" by blast
  then have "\<exists>u v. u \<in> {..k} \<and> v \<in> {..k} \<and> u \<noteq> v \<and> \<chi> (S (x u)) = \<chi> (S (x v))" by blast
  then obtain u v where uv_props: "u \<in> {..k} \<and> v \<in> {..k} \<and> u < v \<and> \<chi> (S (x u)) = \<chi> (S (x v))" 
    by (metis nat_neq_iff)

  thm is_subspace_def
  define y where "y \<equiv> (\<lambda>s \<in> {..t}. S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then s else t))))"

  have line1: "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then s else t))) \<in> cube k (t+1)" if "s\<le>t" for s
  proof (unfold cube_def; intro PiE_I)
    fix l assume "l\<in>{..<k}"
    then have "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then s else t))) l \<le> t" using that by auto
    then show "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then s else t))) l \<in> {..<t+1}" by simp
  qed (auto simp: cube_def)

  have HEHE:"(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then j else t))) \<in> cube k (t+1)" if "j < t+1" for j using line1 that by simp
  have HEHE_BETTER: "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then j else t))) \<in> classes k t u" if j_prop: "j < t" for j
(*   where "classes n t \<equiv> (\<lambda>i. {x . x \<in> (cube n (t + 1)) \<and> (\<forall>u \<in> {(n-i)..<n}. x u = t) \<and> t \<notin> x ` {..<(n - i)}})" *)
  proof -
    have "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then j else t))) z = t" if "z \<in> {k - u..<k}" for z using that uv_props by auto
    moreover have "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then j else t))) z \<noteq> t" if "z \<in> {..<k - u}" for z using that j_prop by auto
    moreover have "t \<notin> (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then j else t))) ` {..<k-u}" using calculation by force
    ultimately show ?thesis unfolding classes_def using HEHE j_prop by simp
  qed
   have HEHE_BETTER_v: "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then j else t))) \<in> classes k t v" if j_prop: "j = t" for j
(*   where "classes n t \<equiv> (\<lambda>i. {x . x \<in> (cube n (t + 1)) \<and> (\<forall>u \<in> {(n-i)..<n}. x u = t) \<and> t \<notin> x ` {..<(n - i)}})" *)
  proof -
    have "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then j else t))) z = t" if "z \<in> {k - v..<k}" for z using that uv_props j_prop by auto
    moreover have "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then j else t))) z \<noteq> t" if "z \<in> {..<k - v}" for z using that j_prop assms(2) by auto
    moreover have "t \<notin> (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then j else t))) ` {..<k-v}" using calculation by force
    ultimately show ?thesis unfolding classes_def using HEHE j_prop by simp
  qed

  obtain B f where Bf_props: "disjoint_family_on B {..k}" "\<Union>(B ` {..k}) = {..<n}" "({} \<notin> B ` {..<k})" "f \<in> (B k) \<rightarrow>\<^sub>E {..<t+1}" "S \<in> (cube k (t+1)) \<rightarrow>\<^sub>E (cube n (t+1))" "(\<forall>y \<in> cube k (t+1). (\<forall>i \<in> B k. S y i = f i) \<and> (\<forall>j<k. \<forall>i \<in> B j. (S y) i = y j))" using assms(1) unfolding layered_subspace_def is_subspace_def by auto

  have "y \<in> {..<t+1} \<rightarrow>\<^sub>E cube n (t+1)"
  proof
    fix j assume a: "j \<in> {..<t+1}"
    then have "y j = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then j else t)))" unfolding y_def by auto
    moreover have "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then j else t))) \<in> cube k (t+1)" using a line1 by simp
    moreover have "S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then j else t))) \<in> cube n (t+1)" using calculation(2)  \<open>S ` cube k (t + 1) \<subseteq> cube n (t + 1)\<close> by blast
    ultimately show "y j \<in> cube n (t+1)" by auto
  qed (auto simp: cube_def y_def)


  moreover have "(\<forall>u<t+1. \<forall>v<t+1. y u j = y v j) \<or> (\<forall>s<t+1. y s j = s)" if j_prop: "j<n" for j 
  proof-
    show "(\<forall>u<t+1. \<forall>v<t+1. y u j = y v j) \<or> (\<forall>s<t+1. y s j = s)"
    proof -
      consider "j \<in> B k" | "\<exists>ii<k. j \<in> B ii" using Bf_props(2) j_prop 
        by (metis UN_E atMost_iff le_neq_implies_less lessThan_iff)
      then have "y a j = y b j \<or> y s j = s" if "a < t + 1" "b < t +1" "s < t +1" for a b s
      proof cases
        case 1
        then have "y a j = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then a else t))) j" using that(1) unfolding y_def by auto
        also have " ... = f j" using Bf_props(6) HEHE 1 that(1) by auto
        also have " ... = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then b else t))) j" using Bf_props(6) HEHE 1 that(2) by auto
        also have " ... = y b j" using that(2) unfolding y_def by simp
        finally show ?thesis by simp
      next
        case 2
        then obtain ii where ii_prop:" ii < k \<and> j \<in> B ii" by blast
        then consider "ii < k - v" | "ii \<ge> k - v \<and> ii < k - u" | "ii \<ge> k - u \<and> ii < k" using not_less  by blast
        then show ?thesis
        proof cases
          case 1
          then have "y a j = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then a else t))) j" using that(1) unfolding y_def by auto
          also have " ... = (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then a else t))) ii" using Bf_props(6) HEHE that(1) ii_prop by auto
          also have " ... = 0" using 1 by (simp add: ii_prop)
          also have " ... = (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then b else t))) ii" using 1 by (simp add: ii_prop)
          also have " ... = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then b else t))) j" using Bf_props(6) HEHE that(2) ii_prop by auto
          also have " ... = y b j" using that(2) unfolding y_def by auto
          finally show ?thesis by simp
        next
          case 2
          then have "y s j = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then s else t))) j" using that(3) unfolding y_def by auto
          also have " ... = (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then s else t))) ii" using Bf_props(6) HEHE that(3) ii_prop by auto
          also have " ... = s" using 2 by (simp add: ii_prop)
          finally show ?thesis by simp
        next
          case 3
          then have "y a j = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then a else t))) j" using that(1) unfolding y_def by auto
          also have " ... = (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then a else t))) ii" using Bf_props(6) HEHE that(1) ii_prop by auto
          also have " ... = t" using 3 uv_props by auto
          also have " ... = (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then b else t))) ii" using 3 uv_props by auto
          also have " ... = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then b else t))) j" using Bf_props(6) HEHE that(2) ii_prop by auto
          also have " ... = y b j" using that(2) unfolding y_def by auto
          finally show ?thesis by simp
        qed
      qed

      then show ?thesis by blast
    qed
  qed
  moreover have "\<exists>j < n. \<forall>s<t+1. y s j = s"
  proof -
    have "k > 0" using uv_props by simp
    have "k - v < k" using uv_props by auto
    have "k - v < k - u" using uv_props by auto
    then have "B (k - v) \<noteq> {}" using Bf_props(3) uv_props by auto
    then obtain j where j_prop: "j \<in> B (k - v) \<and> j < n" using Bf_props(2) uv_props by force
    then have "y s j = s" if "s<t+1" for s
    proof
      have "y s j = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then s else t))) j" using that unfolding y_def by auto
      also have " ... = (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then s else t))) (k - v)" using Bf_props(6) HEHE that j_prop \<open>k - v < k\<close> by fast
      also have " ... = s" using that j_prop \<open>k - v < k - u\<close> by simp
      finally show ?thesis .
    qed
    then show "\<exists>j < n. \<forall>s<t+1. y s j = s" using j_prop by blast
  qed
  ultimately have Z1: "is_line y n (t+1)" unfolding is_line_def by blast

 (*   define y where "y \<equiv> (\<lambda>s \<in> {..t}. S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then s else t))))" *)
(*      y i1 j = S \<Delta> j, with j<k. Ofc, S will either map S \<Delta> j \<rightarrow> f j or S \<Delta> j \<rightarrow> \<Delta> i, with j \<in> B i 

to utilize classes; note that y i1 \<in> S ` classes k t SOMETHING ! ! ! \<longrightarrow> in fact y i1 \<in> S ` classes m t unto

*)
  have k_color: "\<chi> e < k" if "e \<in> y ` {..<t+1}" for e using \<open>y \<in> {..<t+1} \<rightarrow>\<^sub>E cube n (t + 1)\<close> \<open>\<chi> \<in> cube n (t + 1) \<rightarrow>\<^sub>E {..<k}\<close> that by auto
  have "\<chi> e1 = \<chi> e2 \<and> \<chi> e1 < k" if "e1 \<in> y ` {..<t+1}" "e2 \<in> y ` {..<t+1}" for e1 e2 
  proof  
    from that obtain i1 i2 where i_props: "i1 < t + 1" "i2 < t + 1" "e1 = y i1" "e2 = y i2" by blast 
    from i_props(1,2) have "\<chi> (y i1) = \<chi> (y i2)"
    proof (induction i1 i2 rule: linorder_wlog)
      case (le a b)
      then show ?case
      proof (cases "a = b")
        case True
        then show ?thesis by blast
      next
        case False
        then have "a < b" using le by linarith
        then consider "b = t" | "b < t" 
          by (metis Nat.add_0_right One_nat_def Suc_leI add_Suc_right le.prems(2) linorder_neqE_nat not_less)
        then show ?thesis
        proof cases
          case 1
          then have "y b \<in> S ` classes k t v" 
          proof -
            have "y b = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then b else t)))" unfolding y_def using \<open>b = t\<close> by auto
            moreover have "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then b else t))) \<in> classes k t v" using \<open>b = t\<close> HEHE_BETTER_v by blast
            ultimately show "y b \<in> S ` classes k t v" by blast
          qed
          moreover have "x u \<in> classes k t u"
          proof -
(*  define x where "x \<equiv> (\<lambda>i\<in>{..k}. \<lambda>j\<in>{..<k}. (if j < k - i then 0 else t))" *)
            have "x u cord = t" if "cord \<in> {k - u..<k}" for cord using uv_props that unfolding x_def by simp 
            moreover 
            {  
              have "x u cord \<noteq> t" if "cord \<in> {..<k-u}" for cord using uv_props that assms(2) unfolding x_def by auto
              then have "t \<notin> x u ` {..<k-u}" by blast
            }
            ultimately show "x u \<in> classes k t u" unfolding classes_def 
              using \<open>x ` {..k} \<subseteq> cube k (t + 1)\<close> uv_props by blast
          qed
          moreover have "x v \<in> classes k t v"
          proof -
(*  define x where "x \<equiv> (\<lambda>i\<in>{..k}. \<lambda>j\<in>{..<k}. (if j < k - i then 0 else t))" *)
            have "x v cord = t" if "cord \<in> {k - v..<k}" for cord using uv_props that unfolding x_def by simp 
            moreover 
            {  
              have "x v cord \<noteq> t" if "cord \<in> {..<k-v}" for cord using uv_props that assms(2) unfolding x_def by auto
              then have "t \<notin> x v ` {..<k-v}" by blast
            }
            ultimately show "x v \<in> classes k t v" unfolding classes_def 
              using \<open>x ` {..k} \<subseteq> cube k (t + 1)\<close> uv_props by blast
          qed
          moreover have "\<chi> (y b) = \<chi> (S (x v))" using assms(1) calculation(1, 3) unfolding layered_subspace_def 
            by (metis imageE uv_props)
          moreover have "y a \<in> S ` classes k t u" 
          proof -
            have "y a = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then a else t)))" unfolding y_def using \<open>a < b\<close> 1 by simp
            moreover have "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then a else t))) \<in> classes k t u" using \<open>a < b\<close> 1 HEHE_BETTER by blast
            ultimately show "y a \<in> S ` classes k t u" by blast
          qed
          moreover have "\<chi> (y a) = \<chi> (S (x u))" using assms(1) calculation(2, 5) unfolding layered_subspace_def 
            by (metis imageE uv_props)
          ultimately have "\<chi> (y a) = \<chi> (y b)" using uv_props by simp
          then show ?thesis by blast
        next
          case 2
          then have "a < t" using \<open>a < b\<close> less_trans by blast
          thm classes_def
          then have "y a \<in> S ` classes k t u"
          proof -
            have "y a = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then a else t)))" unfolding y_def using \<open>a < t\<close> by auto
            moreover have "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then a else t))) \<in> classes k t u" using \<open>a < t\<close> HEHE_BETTER by blast
            ultimately show "y a \<in> S ` classes k t u" by blast
          qed
          moreover have "y b \<in> S ` classes k t u"
          proof -
            have "y b = S (\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then b else t)))" unfolding y_def using \<open>b < t\<close> by auto
            moreover have "(\<lambda>i \<in> {..<k}. (if i < k - v then 0 else (if i < k - u then b else t))) \<in> classes k t u" using \<open>b < t\<close> HEHE_BETTER by blast
            ultimately show "y b \<in> S ` classes k t u" by blast
          qed
          ultimately have "\<chi> (y a) = \<chi> (y b)" using assms(1) uv_props unfolding layered_subspace_def by (metis imageE)
          then show ?thesis by blast
        qed
      qed
    next
      case (sym a b)
      then show ?case by presburger
    qed
    then show "\<chi> e1 = \<chi> e2" using i_props(3,4) by blast
  qed (use that(1) k_color in blast)
  then have Z2: "\<exists>c < k. \<forall>e \<in> y ` {..<t+1}. \<chi> e = c"
    by (meson image_eqI lessThan_iff less_add_one)

  from Z1 Z2 show " \<exists>L c. c < k \<and> is_line L n (t + 1) \<and> (\<forall>y\<in>L ` {..<t + 1}. \<chi> y = c)" by blast

qed



  text \<open>Gonna go to sleep. Proof in book is clever:
  
  let u = 3, v = 6; k = 8
  then x_u = (t, t, t, 0, 0, 0, 0, 0)
       x_v = (t, t, t, t, t, t, 0, 0)
  and the line (y0, ..., yt)
         y = (t, t, t, *, *, *, 0, 0)
  the points y0, ..., yt are in the class k t k, hence have same color as x_u.

  But my idea: since I define classes slightly differently (i.e. I force *all* rightmost positions to be t),
maybe I can define:
      x_u = (0, 0, 0, 0, 0, t, t, t)
      x_v = (0, 0, 0, t, t, t, t, t)
        y = (0, 0, 0, *, *, t, t, t)
then the points y0, ..., y(t-1) are in class k t u and have same color as x_u.
 and the point  yt is in class k t k and has the same color as x_v, which is the color of x_u.



classes 5 t 3 -> {(<t,<t,t,t,t)}
classes 5 t 5 -> {(t,t,t,t,t)}



\<close>

lemma cor6: assumes "(\<And>r k. lhj r t k)" "t>0"  shows "(hj r (t+1))"
  using assms(1)[of r r] assms(2) unfolding hj_def lhj_def using thm5
  by metis


lemma "\<not>hj 0 0"
  by (auto simp: hj_def cube_def)

lemma base: assumes "r > 0" shows "hj r 0"
proof-
  have "(\<exists>L c. c < r \<and> is_line L N' 0 \<and> (\<forall>y \<in> L ` {..<0::nat}. \<chi> y = c))" if "N' \<ge> 1" "\<chi> \<in> cube N' 0 \<rightarrow>\<^sub>E {..<r}" for N' \<chi>
    using assms is_line_def that(1) by fastforce
  then show ?thesis unfolding hj_def by auto
qed

lemma AUXBASE1: "\<forall>N > 0. is_line (\<lambda>s\<in>{..<1}. \<lambda>a\<in>{..<N}. 0) N 1"
  unfolding is_line_def cube_def by auto

lemma AUX2BASE1: assumes "\<chi> \<in> cube N 1 \<rightarrow>\<^sub>E {..<r}" "N > 0" shows "(\<exists>c < r. is_line (\<lambda>s\<in>{..<1}. \<lambda>a\<in>{..<N}. 0) N 1 \<and> (\<forall>i \<in>  (\<lambda>s\<in>{..<1}. \<lambda>a\<in>{..<N}. 0) ` {..<1}. \<chi> i = c))"
proof -
  have "is_line (\<lambda>s\<in>{..<1}. \<lambda>a\<in>{..<N}. 0) N 1" using assms(2) AUXBASE1 by blast
  moreover have "\<exists>c < r. \<chi> ((\<lambda>s\<in>{..<1}. \<lambda>a\<in>{..<N}. 0) j) = c" if "(j::nat) < 1" for j using assms unfolding cube_def 
    by (metis PiE_mem assms(1) aux2 calculation lessThan_iff that)
  ultimately show ?thesis by auto
qed

lemma base1: "hj r 1"
  unfolding hj_def using AUX2BASE1 le_zero_eq not_le  
  by (metis less_numeral_extra(1))

lemma hales_jewett: "\<not>(r = 0 \<and> t = 0) \<Longrightarrow> hj r t"
  apply (induction t arbitrary: r)
  using  base apply blast
 using base1 thm4 cor6 
  by (metis One_nat_def Suc_eq_plus1 neq0_conv)

unused_thms

end