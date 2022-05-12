theory tt
  imports Main
begin

definition nat_to_seq :: "nat \<Rightarrow> (nat \<Rightarrow> nat)"
  where
    "nat_to_seq k \<equiv> (\<lambda>i. if i < k then 1 else 0)"

definition extinf :: "nat \<Rightarrow> nat" where "extinf \<equiv> (\<lambda>i. 1)"

lemma "nat_to_seq 0 = (\<lambda>i. 0)"
  unfolding nat_to_seq_def by simp

definition "ext_nats \<equiv> {f | f k . f = nat_to_seq k} \<union> {extinf}"

datatype EXT = N nat | I

fun ext_to_seq :: "EXT \<Rightarrow> (nat \<Rightarrow> nat)"
  where
    "ext_to_seq (N k) = nat_to_seq k"
  | "ext_to_seq I = extinf"


lemma inj_nat_to_seq: "inj nat_to_seq" 
  by (metis One_nat_def less_irrefl linorder_injI nat.simps(3) nat_to_seq_def)

lemma extinf_not_nat: "extinf \<noteq> nat_to_seq k"
  by (metis dual_order.irrefl extinf_def nat_to_seq_def zero_neq_one)

lemma "bij_betw (ext_to_seq) UNIV (ext_nats)"
proof (unfold bij_betw_def; intro conjI)
  show "inj ext_to_seq" using extinf_not_nat inj_nat_to_seq 
    by (metis (no_types, lifting) ext_to_seq.elims inj_def)
next
  show "range ext_to_seq = ext_nats" 
  proof
    show "range ext_to_seq \<subseteq> ext_nats"
    proof
      fix x
      assume a: "x \<in> range ext_to_seq"
      consider "\<exists>k. x = nat_to_seq k" | "x = extinf"         
        by (metis a ext_to_seq.elims rangeE)
      then show "x \<in> ext_nats" by (auto simp add: ext_nats_def)
    qed
  next
    show "ext_nats \<subseteq> range ext_to_seq"
    proof
      fix x
      assume a: "x \<in> ext_nats"
      then consider "x = extinf" | "\<exists>k. x = nat_to_seq k" unfolding ext_nats_def by blast
      then show "x \<in> range ext_to_seq" by (metis ext_to_seq.simps(1) ext_to_seq.simps(2) rangeI)
    qed
  qed
qed

lemma codomain_aux: "nat_to_seq k i \<in> {0, 1}" unfolding nat_to_seq_def by simp
lemma codomain: "(nat_to_seq k) ` {i . i \<ge> 0} \<subseteq> {0, 1}"
  using codomain_aux by force

(*fun natfamily_to_extfamily :: "(nat \<Rightarrow> 'a set) \<Rightarrow> (EXT \<Rightarrow> 'a set)"*)



end