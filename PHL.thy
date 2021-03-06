(* Title: Propositional Hoare Logic
   Author: Peixin You
*)

section \<open>Propositional Hoare Logic\<close>

theory PHL
  imports KAT

begin

subsection \<open>Deriving the rules of PHL in KAT\<close>

context kat
begin

definition Ho :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "Ho p x q = (\<tau> p \<cdot> x \<le> x \<cdot> \<tau> q)"

definition while_inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ inv _ do _ od" [64,64,64] 63) where
  "while p inv i do x od = while p do x od"

lemma H_abort: "Ho p 0 q"
  unfolding Ho_def by simp

lemma H_skip: "Ho p 1 p"
  unfolding Ho_def by simp

lemma H_cons: 
  assumes "\<tau> p \<le> \<tau> p'"
  and "Ho p' x q'"
  and "\<tau> q' \<le> \<tau> q"
shows "Ho p x q"
proof-
  have  "\<tau> p' \<cdot> x \<le> x \<cdot> \<tau> q'"
    using Ho_def assms by blast
  hence "\<tau> p \<cdot> x \<le> x \<cdot> \<tau> q"
    by (meson assms dual_order.trans mult_isol mult_isor)
  thus "Ho p x q"
    unfolding Ho_def.
qed

lemma H_seq: 
  assumes "Ho r y q"
  and "Ho p x r"
  shows "Ho p (x \<cdot> y) q" 
proof-
  have a: "\<tau> p \<cdot> x \<le> x \<cdot> \<tau> r"
    using Ho_def assms pcorrect_if1 by simp
  have b: "\<tau> r \<cdot> y \<le> y \<cdot> \<tau> q"
    using Ho_def assms pcorrect_if1 by simp
  hence "\<tau> p \<cdot> (x \<cdot> y) \<le> x \<cdot> \<tau> r \<cdot> y"
    by (metis a local.mult_assoc local.mult_isor)
  also have "\<dots> \<le> (x \<cdot> y) \<cdot> \<tau> q"
    by (simp add: b local.mult_assoc local.mult_isol)
  finally show "Ho p (x \<cdot> y) q"
    unfolding Ho_def.
qed

lemma H_cond: 
  assumes "Ho (\<tau> p \<cdot> \<tau> r) x q"
  and "Ho (\<tau> p \<cdot> \<alpha> r) y q"
  shows "Ho p (if r then x else y fi) q"
proof-
  have a: "\<tau> p \<cdot> \<tau> r \<cdot> x \<le> x \<cdot> \<tau> q"
    by (metis Ho_def assms a_de_morgan2 t_a_var)
  have b: "\<tau> p \<cdot> \<alpha> r \<cdot> y \<le> y \<cdot> \<tau> q"
    using Ho_def assms t_mult_closed test_def by simp
  hence "\<tau> p \<cdot> (\<tau> r \<cdot> x + \<alpha> r \<cdot> y) = \<tau> p \<cdot> \<tau> r \<cdot> x + \<tau> p \<cdot> \<alpha> r \<cdot> y"
    by (simp add: distl mult_assoc)
  hence "\<tau> p \<cdot> (\<tau> r \<cdot> x + \<alpha> r \<cdot> y) = \<tau> r \<cdot> \<tau> p \<cdot> \<tau> r \<cdot> x + \<alpha> r \<cdot> \<tau> p \<cdot> \<alpha> r \<cdot> y"
    by (metis a_comm a_idem mult_assoc test_def)
  also have "\<dots> \<le> \<tau> r \<cdot> x \<cdot> \<tau> q + \<alpha> r \<cdot> y \<cdot> \<tau> q"
    using a b add_iso mult_assoc mult_isol by simp
  also have "\<dots> = (\<tau> r \<cdot> x + \<alpha> r \<cdot> y) \<cdot> \<tau> q"
    by (simp add: distr)
  finally show "Ho p (if r then x else y fi) q"
    unfolding Ho_def cond_def.
qed

lemma H_cond_iff: "Ho p (if r then x else y fi) q = (Ho (\<tau> p \<cdot> \<tau> r) x q \<and> Ho (\<tau> p \<cdot> \<alpha> r) y q)"
proof
  assume h: "Ho p (if r then x else y fi) q"
  hence "\<tau> p \<cdot> \<tau> r \<cdot> x  \<le> \<tau> r \<cdot> x \<cdot> \<tau> q + \<alpha> r \<cdot> y \<cdot> \<tau> q"
    by (simp add: Ho_def add_lub distl distr cond_def mult_assoc)
  hence "\<tau> p \<cdot> \<tau> r \<cdot> x  \<le> \<tau> r \<cdot> \<tau> r \<cdot> x \<cdot> \<tau> q + \<tau> r \<cdot> \<alpha> r \<cdot> y \<cdot> \<tau> q"
    by (smt distl mult_assoc order_def a_comm a_idem test_def)
  also have "\<dots> \<le> x \<cdot> \<tau> q"
    by (metis a_de_morgan2 add_0_right add_idem annil mult_assoc pcorrect_if3 t_at_compl2 test_def)
  finally have a: "Ho (\<tau> p \<cdot> \<tau> r) x q"
    using Ho_def t_mult_closed test_def by simp
  have "\<tau> p \<cdot> \<alpha> r \<cdot> y \<le> \<tau> r \<cdot> x \<cdot> \<tau> q + \<alpha> r \<cdot> y \<cdot> \<tau> q"
    using Ho_def h add_lub distl distr cond_def mult_assoc by auto 
  hence "\<tau> p \<cdot> \<alpha> r \<cdot> y \<le> \<alpha> r \<cdot> \<tau> r \<cdot> x \<cdot> \<tau> q + \<alpha> r \<cdot> \<alpha> r \<cdot> y \<cdot> \<tau> q"
    by (smt a_comm a_idem distl mult_assoc order_def test_def)
  also have "\<dots> \<le> y \<cdot> \<tau> q"
    by (metis add_commute a_absorb2 a_idem add_0_left annil distr mult_1_left order_def test_def test_mult_comp test_one)
  finally have "Ho (\<tau> p \<cdot> \<alpha> r) y q"
    using Ho_def t_mult_closed test_def by auto
  thus "Ho (\<tau> p \<cdot> \<tau> r) x q \<and> Ho (\<tau> p \<cdot> \<alpha> r) y q"
    using a by blast
next
  show  "Ho (\<tau> p \<cdot> \<tau> r) x q \<and> Ho (\<tau> p \<cdot> \<alpha> r) y q \<Longrightarrow> Ho p (if r then x else y fi) q"
    by (simp add: H_cond)
qed

lemma H_while: 
  assumes "Ho (\<tau> p \<cdot> \<tau> r) x p"
  shows "Ho p (while r do x od) (\<tau> p \<cdot> \<alpha> r)" 
proof - 
  have "\<tau> p \<cdot> \<tau> r \<cdot> x \<le> \<tau> r \<cdot> x \<cdot> \<tau> p"
    by (metis Ho_def assms mult_assoc pcorrect_iff1 t_mult_closed test_def)
  hence "\<tau> p \<cdot> (\<tau> r \<cdot> x)\<^sup>\<star> \<cdot> \<alpha> r \<le> (\<tau> r \<cdot> x)\<^sup>\<star> \<cdot> \<tau> p \<cdot> \<alpha> r"
    by (metis mult_isor star_sim1 mult_assoc)
  also have "\<dots> = (\<tau> r \<cdot> x)\<^sup>\<star> \<cdot> \<alpha> r \<cdot> \<tau> p \<cdot> \<alpha> r"
    by (metis a_comm a_idem mult_assoc test_def)
  finally show ?thesis
    using Ho_def mult_assoc t_mult_closed test_def while_def by simp
qed

lemma H_inv: 
  assumes "\<tau> p \<le> \<tau> i"
  and "Ho i x i" 
  and "\<tau> i \<le> \<tau> q" 
  shows "Ho p x q"
  using H_cons assms by blast

lemma H_inv_seq:
  assumes "Ho i x i"
  and "Ho j x j"
  shows "Ho (\<tau> i \<cdot> \<tau> j) x (\<tau> i \<cdot> \<tau> j)"
proof-
  have a: "\<tau> i \<cdot> x \<le> x \<cdot> \<tau> i"
    using Ho_def assms(1) by blast
  have "\<tau> j \<cdot> x \<le> x \<cdot> \<tau> j"
    using Ho_def assms(2) by presburger
  hence "\<tau> i \<cdot> \<tau> j \<cdot> x \<le> \<tau> i \<cdot> x \<cdot> \<tau> j"
    by (simp add: local.mult_assoc local.mult_isol)
  also have "\<dots> \<le> x \<cdot> \<tau> i \<cdot> \<tau> j"
    by (simp add: a local.mult_isor)
  finally show ?thesis
    by (metis Ho_def local.a_de_morgan2 local.mult_assoc local.t_a_var)
qed

lemma H_inv_add:
  assumes "Ho i x i"
  and "Ho j x j"
shows "Ho (\<tau> i + \<tau> j) x (\<tau> i + \<tau> j)"
  by (smt (z3) Ho_def assms(1) assms(2) local.a_de_morgan3 local.add_iso local.distl local.distr local.t_a_var)

lemma H_while_inv: 
  assumes "\<tau> p \<le> \<tau> i"
  and "\<tau> i \<cdot> \<alpha> r \<le> \<tau> q"
  and "Ho (\<tau> i \<cdot> \<tau> r) x i"
shows "Ho p (while r inv i do x od) q" 
  unfolding while_inv_def by (metis H_cons H_while assms t_mult_closed test_def)

end


subsection \<open>Hoare Triples in the Relational and State Transformer Model\<close>

text \<open>First we consider relations.\<close>

abbreviation rH :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a pred \<Rightarrow> bool" ("H\<^sub>r") where
  "H\<^sub>r P R Q \<equiv> rel_kat.Ho \<lceil>P\<rceil>\<^sub>r R \<lceil>Q\<rceil>\<^sub>r"

abbreviation rcond :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("rif _ then _ else _ fi" [64,64,64] 63) where
  "rif P then R else S fi \<equiv> rel_kat.cond \<lceil>P\<rceil>\<^sub>r R S"

abbreviation rwhile :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("rwhile _ do _ od" [64,64] 63) where
  "rwhile P do R od \<equiv> rel_kat.while \<lceil>P\<rceil>\<^sub>r R"

abbreviation rwhile_inv :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("rwhile _ inv _ do _ od" [64,64,64] 63) where
  "rwhile P inv I do R od \<equiv> rel_kat.while_inv \<lceil>P\<rceil>\<^sub>r \<lceil>I\<rceil>\<^sub>r R"

lemma rH_unfold: "H\<^sub>r P R Q = (\<forall>x y. P x \<longrightarrow> (x,y) \<in> R \<longrightarrow> Q y)"
  unfolding p2r_def rel_kat.Ho_def rel_kat.test_def rel_atest_def by force
 
lemma rH_skip: "H\<^sub>r P Id Q = (\<forall>x. P x \<longrightarrow> Q x)"
  unfolding rH_unfold by simp

lemma rH_cons1: 
  assumes  "H\<^sub>r P' R Q"
  and "\<forall>x. P x \<longrightarrow> P' x"
  shows "H\<^sub>r P R Q"
  unfolding rH_unfold by (meson assms rH_unfold) 

lemma rH_cons2: 
  assumes "H\<^sub>r P R Q'"
  and "\<forall>x. Q' x \<longrightarrow> Q x"
  shows "H\<^sub>r P R Q"
  unfolding rH_unfold by (meson assms rH_unfold) 

lemma rH_cons: 
  assumes "H\<^sub>r P' R Q'"
  and "\<forall>x. P x \<longrightarrow> P' x"
  and "\<forall>x. Q' x \<longrightarrow> Q x"
  shows "H\<^sub>r P R Q"
  unfolding rH_unfold by (meson assms rH_unfold) 

lemma rH_cond [simp]: "(H\<^sub>r P (rif T then R else S fi) Q) = (H\<^sub>r (\<lambda>s. P s \<and> T s) R Q \<and> H\<^sub>r (\<lambda> s. P s \<and> \<not> T s) S Q)"
  by (simp add: rel_kat.H_cond_iff)

lemma rH_while_inv: 
  assumes "H\<^sub>r (\<lambda>s. I s \<and> T s) R I"
  and "\<forall>x. P x \<longrightarrow> I x"
  and "\<forall>x. I x \<and> \<not> T x \<longrightarrow> Q x"
  shows "H\<^sub>r P (rwhile T inv I do R od) Q"
  by (rule rel_kat.H_while_inv, simp_all add: assms)

lemma rH_while: 
  assumes "H\<^sub>r (\<lambda>s. P s \<and> T s) R P"
  shows "H\<^sub>r P (rwhile T do R od) (\<lambda>s. P s \<and> \<not> T s)"
proof-
  have "H\<^sub>r P (rwhile T inv P do R od) (\<lambda>s. P s \<and> \<not> T s)"
    by (rule rH_while_inv, simp_all add: assms)
  thus ?thesis
    by (simp add: rel_kat.while_inv_def)
qed

text \<open>Next we repeat the development with state transformers.\<close>

abbreviation Hs :: "'a pred \<Rightarrow> 'a sta \<Rightarrow> 'a pred \<Rightarrow> bool" ("H\<^sub>s") where
  "H\<^sub>s P f Q \<equiv> sta_kat.Ho \<lceil>P\<rceil>\<^sub>s f \<lceil>Q\<rceil>\<^sub>s"

abbreviation scond :: "'a pred \<Rightarrow> 'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" ("sif _ then _ else _ fi" [64,64,64] 63) where
  "sif P then f else g fi \<equiv> sta_kat.cond \<lceil>P\<rceil>\<^sub>s f g"

abbreviation swhile :: "'a pred \<Rightarrow> 'a sta \<Rightarrow> 'a sta" ("swhile _ do _ od" [64,64] 63) where
  "swhile P do f od \<equiv> sta_kat.while \<lceil>P\<rceil>\<^sub>s f"

abbreviation swhile_inv :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a sta \<Rightarrow> 'a sta" ("swhile _ inv _ do _ od" [64,64,64] 63) where
  "swhile P inv I do f od \<equiv> sta_kat.while_inv \<lceil>P\<rceil>\<^sub>s \<lceil>I\<rceil>\<^sub>s f"

lemma sH_unfold: "H\<^sub>s P f Q = (\<forall>x y. P x \<longrightarrow> y \<in> f x \<longrightarrow> Q y)"

  unfolding sta_kat.Ho_def p2s_def sta_kat.test_def sta_atest_def kleq_iff kcomp_iff by force
 
lemma sH_skip: "H\<^sub>s P \<eta> Q = (\<forall>x. P x \<longrightarrow> Q x)"
  unfolding sH_unfold by simp

lemma sH_cons1: 
  assumes "H\<^sub>s P' f Q"
  and "\<forall>x. P x \<longrightarrow> P' x"
  shows "H\<^sub>s P f Q"
  unfolding sH_unfold by (meson assms sH_unfold)

lemma sH_cons2: 
  assumes "H\<^sub>s P f Q'"
  and "\<forall>x. Q' x \<longrightarrow> Q x" 
  shows "H\<^sub>s P f Q"
  unfolding sH_unfold by (meson assms sH_unfold)

lemma sH_cons: 
  assumes "H\<^sub>s P' f Q'"
  and "\<forall>x. P x \<longrightarrow> P' x"
  and "\<forall>x. Q' x \<longrightarrow> Q x"
  shows "H\<^sub>s P f Q"
  unfolding sH_unfold by (meson assms sH_unfold)

lemma sH_cond [simp]: "(H\<^sub>s P (sif T then f else g fi) Q) = (H\<^sub>s (\<lambda>s. P s \<and> T s) f Q \<and> H\<^sub>s (\<lambda> s. P s \<and> \<not>T s) g Q)"
    by (simp add: sta_kat.H_cond_iff)

lemma sH_while_inv: 
  assumes "H\<^sub>s (\<lambda>s. I s \<and> T s) f I"
  and "\<forall>s. P s \<longrightarrow> I s"
  and "\<forall>s. I s \<and> \<not> T s \<longrightarrow> Q s"
  shows "H\<^sub>s P (swhile T inv I do f od) Q"
  by (rule sta_kat.H_while_inv) (simp_all add: assms)

lemma sH_while: 
  assumes "H\<^sub>s (\<lambda>s. P s \<and> T s) f P"
  shows "H\<^sub>s P (swhile T do f od) (\<lambda>s. P s \<and> \<not> T s)"
proof-
  have "H\<^sub>s P (swhile T inv P do f od) (\<lambda>s. P s \<and> \<not> T s)"
    by (rule sH_while_inv, simp_all add: assms)
  thus ?thesis
    by (simp add: sta_kat.while_inv_def)
qed

text \<open>We have taken care that the verification condition generation for relations and state transformers is the same.\<close>

end







