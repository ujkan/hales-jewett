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
* finish the base case
* start on the induction step / outline

\<close>

lemma "f \<in> A \<rightarrow>\<^sub>E B \<longleftrightarrow> ((\<forall>a. (a \<in> A \<longrightarrow> f a \<in> B) \<and> (a \<notin> A \<longrightarrow> f a = undefined)))" 
  by auto

definition cube :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "cube n t \<equiv> {..<n} \<rightarrow>\<^sub>E {..<t}"

text \<open>Attempting to show (card {} ->E A) = 1\<close>
lemma aux: "\<exists>!f. f \<in> {} \<rightarrow>\<^sub>E A " 
  by simp

lemma "card ({} \<rightarrow>\<^sub>E A) = 1"
  using aux by auto

thm card_PiE
lemma cube_card: "card ({..<n::nat} \<rightarrow>\<^sub>E {..<t::nat}) = t ^ n"
  apply (subst card_PiE)
  by auto
  
definition isLine :: "(nat \<Rightarrow> (nat \<Rightarrow> nat)) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "isLine L n t \<equiv> (L \<in> {..<t} \<rightarrow>\<^sub>E (cube n t) \<and> ((\<forall>j<n. (\<forall>x<t. \<forall>y<t. L x j =  L y j) \<or> (\<forall>s<t. L s j = s)) \<and> (\<exists>j < n. (\<forall>s < t. L s j = s))))"

lemma "isLine L n t \<Longrightarrow> L ` {..<t} \<subseteq> cube n t"
  unfolding cube_def isLine_def
  by auto

lemma aux2: "isLine L n t \<Longrightarrow> (\<forall>s<t. L s \<in> cube n t)"
  unfolding cube_def isLine_def
  by auto

term disjoint_family_on
term partition_on
definition isSubspace
  where "isSubspace f' k n t \<equiv> (\<exists>B f. disjoint_family_on B {..k} \<and> \<Union>(B ` {..k}) = {..<n} \<and> ({} \<notin> B ` {..<k}) \<and> f \<in> (B k) \<rightarrow>\<^sub>E {..<t} \<and> f' \<in> (cube k t) \<rightarrow>\<^sub>E (cube n t) \<and> (\<forall>y \<in> cube k t. (\<forall>i \<in> B k. f' y i = f i) \<and> (\<forall>j<k. \<forall>i \<in> B j. (f' y) i = y j)))"

lemma AUX: "cube n t \<subseteq> cube n (t + 1)"
  unfolding cube_def
  by (meson PiE_mono le_add1 lessThan_subset_iff)

text \<open>Defining the equivalence classes of (cube n (t + 1)). {classes n t 0, ..., classes n t n}\<close>
definition classes
  where "classes n t \<equiv> (\<lambda>i. {x . x \<in> (cube n (t + 1)) \<and> {t} = x ` {(n - i)..<n} \<and> t \<notin> x ` {..<(n - i)}})"

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
lemma "\<forall>\<chi> r t k. \<exists>M'. \<forall>M \<ge> M'. \<chi> \<in> (cube M (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. isSubspace S k M (t + 1) \<and> (\<forall>i \<in> {..M}. \<exists>c < r. \<chi> ` (classes M t i) = {c}))"
  sorry

text \<open>Experiments to see how \<rightarrow> behaves.\<close>
lemma "A \<noteq> {} \<Longrightarrow> A \<rightarrow>\<^sub>E {} = {}"
  by auto

lemma "A = {} \<Longrightarrow> \<exists>!f. f \<in> A \<rightarrow>\<^sub>E B"
  by simp
  
lemma "B \<noteq> {} \<Longrightarrow> A \<rightarrow>\<^sub>E B \<noteq> {}"
  by (meson PiE_eq_empty_iff)



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


text \<open>Should follow since cube k t subset of cube k (t + 1). At least, S is a subset of cube n (t + 1).\<close>
lemma subspace_suc_t: "isSubspace S k n t \<Longrightarrow> isSubspace S k n (t+1)"
  unfolding isSubspace_def using AUX sorry

lemma props_over_bij: "bij_betw h X Y \<Longrightarrow> (\<forall>x \<in> X. P a x) \<Longrightarrow> (\<forall>x \<in> X. P a x = Q a (h x)) \<Longrightarrow> (\<forall>y \<in> Y. Q a y)"
  by (smt (verit, ccfv_SIG) bij_betwE bij_betw_the_inv_into f_the_inv_into_f_bij_betw)


text \<open>Relating lines and 1-dimensional subspaces.\<close>
(* use assumes and shows *)
lemma line_is_1dim_subspace: "n > 0 \<Longrightarrow> t > 1 \<Longrightarrow> isLine L n t \<Longrightarrow> isSubspace (restrict (\<lambda>y. L (y 0)) (cube 1 t)) 1 n t"
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
    
    have "\<forall>a \<in> {..<t}. \<forall>b \<in> {..<n}. L a b \<in> {..<t}" using assms(3) unfolding isLine_def cube_def by auto
    then have "L 0 i \<in> {..<t}" using g h by simp
    then show "?f i \<in> {..<t}" using \<open>?f i = L 0 i\<close> by simp
  next
    fix i
    assume asm: "i \<notin> (?K 1)"
    then show "?f i = undefined" by auto
  qed


  have L_prop: "L \<in> {..<t} \<rightarrow>\<^sub>E (cube n t)" using assms(3) by (simp add: isLine_def)
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
      moreover have "L (y 0) i = L 0 i" using assms(3) \<open>i \<in> ?K 1\<close> unfolding isLine_def 
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

  from A1 A2 A3 A4 A5 A6 show "isSubspace ?L 1 n t" unfolding isSubspace_def by blast
qed

text \<open>The base case of Theorem 4 in the book.\<close>
lemma thm4_k_1: assumes "t > 1" "(\<forall>r. \<exists>N' > 0. \<forall>\<chi>. \<chi> \<in> (cube N' t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. isLine L N' t \<and> \<chi> ` (L ` {..<t}) = {c}))" shows "(\<forall>r. \<exists>M' > 0. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. isSubspace S 1 M' (t + 1) \<and> (\<forall>i \<in> {..M'}. \<exists>c < r. \<chi> ` (classes M' t i) = {c})))"
proof(rule allI)
  fix r
  obtain N' where N'_def: "N' > 0 \<and> (\<forall>\<chi>. \<chi> \<in> (cube N' t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. isLine L N' t \<and> \<chi> ` (L ` {..<t}) = {c}))" using assms(2) by metis

  have "\<forall>\<chi>. \<chi> \<in> (cube N' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. isSubspace S 1 N' (t + 1) \<and> (\<forall>i \<in> {..N'}. \<exists>c < r. \<chi> ` (classes N' t i) = {c}))"
  proof(safe)
    fix \<chi>
    assume asm: "\<chi> \<in> cube N' (t + 1) \<rightarrow>\<^sub>E {..<r::nat}"
    let ?chi_t = "(\<lambda>x. if x \<in> cube N' t then \<chi> x else undefined)"
    have "?chi_t \<in> cube N' t \<rightarrow>\<^sub>E {..<r::nat}"
    proof 
      fix x
      assume xdef: "x \<in> cube N' t"
      then have "x \<in> cube N' (t + 1)" using AUX by auto
      then show "?chi_t x \<in> {..<r::nat}" using asm xdef by auto
    next
      fix x
      assume xdef: "x \<notin> cube N' t"
      then show "?chi_t x = undefined" by simp
    qed
    then obtain L where L_def: "\<exists>c<r. isLine L N' t \<and> ?chi_t ` (L ` {..<t}) = {c}" using N'_def by presburger

    have "isSubspace (restrict (\<lambda>y. L (y 0)) (cube 1 t)) 1 N' t" using line_is_1dim_subspace N'_def L_def 
      using assms(1) by auto 
    then obtain B f where Bf_defs: "disjoint_family_on B {..1} \<and> \<Union>(B ` {..1}) = {..<N'} \<and> ({} \<notin> B ` {..<1}) \<and> f \<in> (B 1) \<rightarrow>\<^sub>E {..<t} \<and> (restrict (\<lambda>y. L (y 0)) (cube 1 t)) \<in> (cube 1 t) \<rightarrow>\<^sub>E (cube N' t) \<and> (\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. (restrict (\<lambda>y. L (y 0)) (cube 1 t)) y i = f i) \<and> (\<forall>j<1. \<forall>i \<in> B j. ((restrict (\<lambda>y. L (y 0)) (cube 1 t)) y) i = y j))" unfolding isSubspace_def by auto 

    have "{..1::nat} = {0,1}" by auto
    then have B_props: "B 0 \<union> B 1 = {..<N'} \<and> (B 0 \<inter> B 1 = {})" using Bf_defs unfolding disjoint_family_on_def by auto
    let ?L' = "L(t:=(\<lambda>j. if j \<in> B 1 then L (t - 1) j else (if j \<in> B 0 then t else undefined)))" 
    have "isLine ?L' N' (t + 1)"
    proof-
      have A1:"?L' \<in> {..<t+1} \<rightarrow>\<^sub>E cube N' (t + 1)" 
      proof
        fix x
        assume asm: "x \<in> {..<t + 1}"
        then show "?L' x \<in> cube N' (t + 1)"
        proof (cases "x < t")
          case True
          then have "?L' x = L x" by simp
          then have "?L' x \<in> cube N' t" using L_def True unfolding isLine_def by auto
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
        then show "?L' x = undefined"  by (metis (no_types, lifting) L_def PiE_E fun_upd_apply isLine_def)
      qed


      have A2: "(\<exists>j<N'. (\<forall>s < (t + 1). ?L' s j = s))"
      proof-
        have "(\<exists>j<N'. (\<forall>s < t. ?L' s j = s))" using L_def unfolding isLine_def by auto
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
      from A1 A2 A3 show ?thesis unfolding isLine_def by simp


    qed
    then have "\<exists>S. isSubspace S 1 N' (t + 1)" using line_is_1dim_subspace 
      by (meson N'_def assms(1) less_add_same_cancel2 less_numeral_extra(1) less_trans)

    show "\<exists>S. isSubspace S 1 N' (t + 1) \<and> (\<forall>i\<in>{..N'}. \<exists>c<r. \<chi> ` (classes N' t i) = {c}) " sorry


  qed
  then show "\<exists>M'>0. \<forall>\<chi>. \<chi> \<in> (cube M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. isSubspace S 1 M' (t + 1) \<and> (\<forall>i \<in> {..M'}. \<exists>c < r. \<chi> ` (classes M' t i) = {c}))" using N'_def by blast
qed


text \<open>Claiming k-dimension subspaces of (cube n t) are isomorphic to (cube k t)\<close>
definition isSubspace_alt
  where "isSubspace_alt S k n t \<equiv> (\<exists>\<phi>. k \<le> n \<and> bij_betw \<phi> S (cube k t))"



lemma hales_jewett: "\<forall>\<chi> r t. \<exists>N'. \<forall>N \<ge> N'. \<chi> \<in> (cube N t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. isLine L N t \<and> \<chi> ` (L ` {..<t}) = {c})"
  sorry
  
  

  
  

end