(* Title: Kleene Algebra with Tests
   Author: Peixin You
*)

section \<open>Kleene Algebra with Tests\<close>

theory KAT
  imports KA

begin

subsection \<open>Definitions and Basic Properties\<close>

class kat = kleene_algebra +
  fixes atest :: "'a \<Rightarrow> 'a" ("\<alpha>")
  assumes test_one [simp]: "\<alpha> (\<alpha> 1) = 1"
  and test_mult [simp]: "\<alpha> (\<alpha> (\<alpha> (\<alpha> x) \<cdot> \<alpha> (\<alpha> y))) = \<alpha> (\<alpha> y) \<cdot> \<alpha> (\<alpha> x)" 
  and test_mult_comp [simp]: "\<alpha> x \<cdot> \<alpha> (\<alpha> x) = 0"
  and test_de_morgan: "\<alpha> (\<alpha> (\<alpha> x) \<cdot> \<alpha> (\<alpha> y)) = \<alpha> x + \<alpha> y"

begin

definition test :: "'a \<Rightarrow> 'a"  ("\<tau>") where
  "\<tau> x = \<alpha> (\<alpha> x)"

lemma a_a [simp]: "\<alpha> \<circ> \<alpha> = \<tau>"
  unfolding fun_eq_iff comp_def test_def by simp

lemma t_a [simp]: "\<tau> \<circ> \<alpha> = \<alpha>"
  unfolding fun_eq_iff comp_def test_def
  by (metis add_idem test_de_morgan test_mult)

lemma t_a_var [simp]: "\<tau> (\<alpha> x) = \<alpha> x"
  by (metis comp_def t_a)

lemma a_t [simp]: "\<alpha> \<circ> \<tau> = \<alpha>"
  by (metis a_a fun.map_comp t_a)

lemma a_t_var [simp]: "\<alpha> (\<tau> x) = \<alpha> x"
  using t_a_var test_def by force

lemma t_t [simp]: "\<tau> \<circ> \<tau> = \<tau>"
  by (metis a_a comp_assoc t_a)

lemma t_t_var [simp]: "\<tau> (\<tau> x) = \<tau> x"
  using a_t_var test_def by auto

lemma a_comm: "\<alpha> x \<cdot> \<alpha> y = \<alpha> y \<cdot> \<alpha> x"
  by (metis test_mult t_a_var test_def)
 
lemma a_idem [simp]: "\<alpha> x \<cdot> \<alpha> x = \<alpha> x"
  by (metis add_idem test_de_morgan test_mult)

lemma t_add_closed [simp]: "\<tau> (\<alpha> x + \<alpha> y) = \<alpha> x + \<alpha> y"
  by (metis test_de_morgan t_a_var)

lemma t_mult_closed [simp]: "\<tau> (\<alpha> x \<cdot> \<alpha> y) = \<alpha> x \<cdot> \<alpha> y"
  by (metis a_t comp_eq_dest_lhs test_mult test_def)

lemma t_at_compl1 [simp]: "\<tau> x + \<alpha> x = 1"
  by (metis mult_1_left test_de_morgan test_mult_comp test_one a_t_var test_def)

lemma t_at_compl2 [simp]: "\<tau> x \<cdot> \<alpha> x = 0"
  by (simp add: a_comm test_def)

lemma a_absorb1 [simp]: "\<alpha> x \<cdot> (\<alpha> x + \<alpha> y) = \<alpha> x"
  by (metis a_idem add_commute add_ubl distl mult_1_right order_def t_at_compl1)

lemma a_absorb2 [simp]: "\<alpha> x + \<alpha> x \<cdot> \<alpha> y = \<alpha> x"
  using a_absorb1 distl test_def by auto

lemma t_distl2: "\<alpha> x + \<alpha> y \<cdot> \<alpha> z = (\<alpha> x + \<alpha> y) \<cdot> (\<alpha> x + \<alpha> z)"
  by (smt a_absorb1 a_comm a_idem abel_semigroup.commute abel_semigroup.left_commute add.abel_semigroup_axioms distr test_de_morgan)

lemma a_de_morgan2: "\<alpha> (\<alpha> x + \<alpha> y) = \<tau> x \<cdot> \<tau> y"
  by (metis test_de_morgan t_mult_closed test_def)

lemma a_de_morgan3: "\<alpha> (\<alpha> x \<cdot> \<alpha> y) = \<tau> x + \<tau> y"
  by (metis a_t_var test_de_morgan test_def)

lemma a_lbl: "\<alpha> x \<cdot> \<alpha> y \<le> \<alpha> x"
  by (simp add: add_commute order_def)

lemma a_lbr: "\<alpha> x \<cdot> \<alpha> y \<le> \<alpha> y"
  using a_comm a_lbl by fastforce

lemma a_upper: "\<alpha> z \<le> \<alpha> x \<Longrightarrow> \<alpha> z \<le> \<alpha> y \<Longrightarrow> \<alpha> z \<le> \<alpha> x \<cdot> \<alpha> y"
  by (simp add: order_def t_distl2)

lemma a_glb: "(\<tau> z \<le> \<tau> x \<cdot> \<tau> y) = (\<tau> z \<le> \<tau> x \<and> \<tau> z \<le> \<tau> y)"
  by (smt a_lbl a_lbr a_upper dual_order.trans test_def)

lemma t_subid: "\<tau> x \<le> 1"
  using add_ubl t_at_compl1 by fastforce

lemma a_subid: "\<alpha> x \<le> 1"
  by (metis t_a_var t_subid)

lemma a_comp_ord_def: "(\<alpha> x \<le> \<alpha> y) = (\<alpha> x \<cdot> \<alpha> y = \<alpha> x)"
  by (metis a_absorb1 a_lbr order_def)

lemma t_le_antitone: "(\<tau> x \<le> \<tau> y) = (\<alpha> y \<le> \<alpha> x)"
  by (metis a_de_morgan2 a_lbl a_t_var order_def test_def)

lemma at_shunt: "(\<alpha> x \<cdot> \<alpha> y \<le> \<alpha> z) = (\<alpha> x \<le> \<tau> y + \<alpha> z)"
proof 
  assume h1: "\<alpha> x \<cdot> \<alpha> y \<le> \<alpha> z"
  have "\<alpha> x = \<alpha> x \<cdot> (\<tau> y + \<alpha> y)"
    using t_at_compl1 by auto
  also have "\<dots> = \<alpha> x \<cdot> \<tau> y + \<alpha> x \<cdot> \<alpha> y"
    using distl by blast
  also have "\<dots> \<le> \<tau> y + \<alpha> z"
    by (simp add: a_lbr h1 add_iso test_def)
  finally show "\<alpha> x \<le> \<tau> y + \<alpha> z".
next
  assume "\<alpha> x \<le> \<tau> y + \<alpha> z"
  hence "\<alpha> x \<cdot> \<alpha> y \<le> (\<tau> y + \<alpha> z) \<cdot> \<alpha> y"
    by (simp add: add_ubr mult_isor)
  also have "\<dots> = \<tau> y \<cdot> \<alpha> y + \<alpha> z \<cdot> \<alpha> y"
    by (simp add: distr)
  also have "\<dots> = \<alpha> z \<cdot> \<alpha> y"
    using t_at_compl2 by auto
  also have "\<dots> \<le> \<alpha> z"
    by (simp add: a_lbl)
  finally show "\<alpha> x \<cdot> \<alpha> y \<le> \<alpha> z".
qed

end

subsection \<open>Boolean Subalgebra of Tests\<close>

typedef (overloaded) 'a test_alg = "{x::'a::kat. \<tau> x = x}"
  by (meson CollectI t_a_var)

setup_lifting type_definition_test_alg

instantiation test_alg :: (kat) boolean_algebra
begin

lift_definition minus_test_alg :: "'a test_alg \<Rightarrow> 'a test_alg \<Rightarrow> 'a test_alg" is "\<lambda>x y. x \<cdot> \<alpha> y"
  by (metis t_mult_closed test_def)

lift_definition uminus_test_alg :: "'a test_alg \<Rightarrow> 'a test_alg" is "\<alpha>"
  by simp

lift_definition bot_test_alg :: "'a test_alg" is "0"
  by (metis t_mult_closed test_mult_comp)

lift_definition top_test_alg :: "'a test_alg" is "1"
  by (simp add: test_def)

lift_definition inf_test_alg :: "'a test_alg \<Rightarrow> 'a test_alg \<Rightarrow> 'a test_alg" is "(\<cdot>)"
  by (metis t_mult_closed test_def)

lift_definition sup_test_alg :: "'a test_alg \<Rightarrow> 'a test_alg \<Rightarrow> 'a test_alg" is "(+)"
  by (metis t_add_closed test_def)

lift_definition less_eq_test_alg :: "'a test_alg \<Rightarrow> 'a test_alg \<Rightarrow> bool" is "(\<le>)".

lift_definition less_test_alg :: "'a test_alg \<Rightarrow> 'a test_alg \<Rightarrow> bool" is "(<)".

instance
  apply (intro_classes; transfer)
                 apply (simp_all add: less_le_not_le add_ubl add_ubr add_lub zero_least test_def)
        apply (metis a_lbl)
       apply (metis a_lbr)
      apply (metis a_upper)
     apply (metis a_subid)
    apply (metis t_distl2)
   apply (metis test_mult_comp)
  by (metis t_a_var t_at_compl1)

end


text \<open>Unfortunately, this theorem must be given outside of the context of the Kleene algebra with tests class.
We can therefore not use its results within this context. This means in particular that theorems from
Isabelle's boolean algebra component are not within scope within this context.\<close>

subsection \<open>Properties Helpful for Propositional Hoare Logic\<close>

context kat
begin

lemma pcorrect_if1: "\<alpha> p \<cdot> x \<le> x \<cdot> \<alpha> q \<Longrightarrow> \<alpha> p \<cdot> x \<cdot> \<tau> q = 0"
proof-
  assume "\<alpha> p \<cdot> x \<le> x \<cdot> \<alpha> q"
  hence "\<alpha> p \<cdot> x \<cdot> \<tau> q \<le> x \<cdot> \<alpha> q \<cdot> \<tau> q"
    by (metis mult_isor)
  thus ?thesis
    by (simp add: antisym mult_assoc test_def zero_least)
qed

lemma pcorrect_if1_op: "x \<cdot> \<alpha> q \<le> \<alpha> p \<cdot> x \<Longrightarrow> \<tau> p \<cdot> x \<cdot> \<alpha> q = 0"
proof-
  assume "x \<cdot> \<alpha> q \<le> \<alpha> p \<cdot> x"
  hence "\<tau> p \<cdot> x \<cdot> \<alpha> q \<le> \<tau> p \<cdot> \<alpha> p \<cdot> x"
    using mult_assoc mult_isol by presburger
  thus ?thesis
    by (simp add: order_def)
qed

lemma pcorrect_if2: "\<alpha> p \<cdot> x \<cdot> \<tau> q = 0 \<Longrightarrow> \<alpha> p \<cdot> x \<cdot> \<alpha> q = \<alpha> p \<cdot> x" 
proof-
  assume "\<alpha> p \<cdot> x \<cdot> \<tau> q = 0"
  hence "\<alpha> p \<cdot> x \<cdot> \<alpha> q = \<alpha> p \<cdot> x \<cdot> \<alpha> q + \<alpha> p \<cdot> x \<cdot> \<tau> q"
    by simp
  also have "\<dots> = \<alpha> p \<cdot> x \<cdot> (\<tau> q + \<alpha> q)"
    by (simp add: add_commute distl)
  finally show ?thesis
    by simp
qed

lemma pcorrect_if2_op: "\<tau> p \<cdot> x \<cdot> \<alpha> q = 0 \<Longrightarrow> \<alpha> p \<cdot> x \<cdot> \<alpha> q = x \<cdot> \<alpha> q" 
proof-
  assume "\<tau> p \<cdot> x \<cdot> \<alpha> q = 0"
  hence "\<alpha> p \<cdot> x \<cdot> \<alpha> q = \<alpha> p \<cdot> x \<cdot> \<alpha> q + \<tau> p \<cdot> x \<cdot> \<alpha> q"
    by simp
  also have "\<dots> = (\<tau> p + \<alpha> p) \<cdot> x \<cdot> \<alpha> q"
    by (simp add: add_commute distr)
  finally show ?thesis
    by simp
qed

lemma pcorrect_if3: "\<alpha> p \<cdot> x = \<alpha> p \<cdot> x \<cdot> \<alpha> q \<Longrightarrow> \<alpha> p \<cdot> x \<le> x \<cdot> \<alpha> q"
  by (metis a_subid mult_1_left mult_isor)

lemma pcorrect_if3_op: "\<alpha> p \<cdot> x \<cdot> \<alpha> q = x \<cdot> \<alpha> q \<Longrightarrow> x \<cdot> \<alpha> q \<le> \<alpha> p \<cdot>  x"
  by (metis a_subid mult_1_right mult_isol)

lemma pcorrect_iff1: "(\<alpha> p \<cdot> x \<le> x \<cdot> \<alpha> q) = (\<alpha> p \<cdot> x \<cdot> \<tau> q = 0)"  
  by (metis pcorrect_if1 pcorrect_if2 pcorrect_if3)

lemma pcorrect_iff1_op: "(x \<cdot> \<alpha> q \<le> \<alpha> p \<cdot> x) = (\<tau> p \<cdot> x \<cdot> \<alpha> q = 0)"  
   by (metis pcorrect_if1_op pcorrect_if2_op pcorrect_if3_op)

lemma pcorrect_iff2: "(\<alpha> p \<cdot> x \<cdot> \<tau> q = 0) = (\<alpha> p \<cdot> x \<cdot> \<alpha> q = \<alpha> p \<cdot> x)" 
  by (metis pcorrect_if1 pcorrect_if2 pcorrect_if3) 

lemma pcorrect_iff2_op: "(\<tau> p \<cdot> x \<cdot> \<alpha> q = 0) = (\<alpha> p \<cdot> x \<cdot> \<alpha> q  = x \<cdot> \<alpha> q)" 
  by (metis pcorrect_if1_op pcorrect_if2_op pcorrect_if3_op) 

lemma pcorrect_op: "(\<alpha> p \<cdot> x \<le> x \<cdot> \<alpha> q) = (x \<cdot> \<tau> q \<le> \<tau> p \<cdot> x)"
proof-
  have "(\<alpha> p \<cdot> x \<le> x \<cdot> \<alpha> q) = (\<alpha> p \<cdot> x \<cdot> \<tau> q = 0)"
    by (simp add: pcorrect_iff1)
  also have "\<dots> = (\<tau> (\<alpha> p) \<cdot> x \<cdot> \<alpha> (\<alpha> q) = 0)"
    using local.t_a_var local.test_def by auto
  also have "\<dots> = (x \<cdot> (\<alpha> (\<alpha> q)) \<le> \<alpha> (\<alpha> p) \<cdot> x)"
    by (simp add: pcorrect_iff1_op)
  finally show ?thesis
    by (simp add: local.test_def)
qed

lemma pcorrect: "(\<tau> p \<cdot> x \<le> x \<cdot> \<tau> q) = (x \<cdot> \<alpha> q \<le> \<alpha> p \<cdot> x)"
  using local.t_a_var local.test_def pcorrect_op by auto


subsection  \<open>Conditionals and while-Loops.\<close>

definition cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _ fi" [64,64,64] 63) where
  "if p then x else y fi = \<tau> p \<cdot> x + \<alpha> p \<cdot> y"

definition while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _ od" [64,64] 63) where
  "while p do x od = (\<tau> p \<cdot> x)\<^sup>\<star> \<cdot> \<alpha> p"


subsection \<open>Program Equivalences and Transformations\<close>

lemma while_rec: "while p do x od = if p then x \<cdot> (while p do x od) else 1 fi"
proof-
  have "if p then x \<cdot> (while p do x od) else 1 fi = \<tau> p \<cdot> x \<cdot> (\<tau> p \<cdot> x)\<^sup>\<star> \<cdot> \<alpha> p + \<alpha> p \<cdot> 1"
    by (simp add: cond_def mult_assoc while_def)
  also have "\<dots> = (\<tau> p \<cdot> x \<cdot> (\<tau> p \<cdot> x)\<^sup>\<star> + 1) \<cdot> \<alpha> p"
    by (simp add: distr)
  also have "\<dots> = (\<tau> p \<cdot> x)\<^sup>\<star> \<cdot> \<alpha> p"
    by (simp add: add_commute)
  also have "\<dots> = while p do x od"
    by (simp add: while_def)
  finally show ?thesis..
qed

lemma while_rec_least: "if p then x \<cdot> y else 1 fi = y \<Longrightarrow> while p do x od \<le> y"
  by (simp add: add_commute cond_def local.mult.semigroup_axioms local.star_inductl semigroup.assoc while_def)

lemma cond_merge_aux: "(\<tau> p \<cdot> x = x \<cdot> \<tau> p) = (\<alpha> p \<cdot> x = x \<cdot> \<alpha> p)"
proof-
  have "(\<tau> p \<cdot> x = x \<cdot> \<tau> p) = (\<tau> p \<cdot> x \<le> x \<cdot> \<tau> p \<and> x \<cdot> \<tau> p \<le> \<tau> p \<cdot> x)"
    by force
  also have "\<dots> = (\<tau> p \<cdot> x \<cdot> \<alpha> p = 0 \<and> \<alpha> p \<cdot> x \<cdot> \<tau> p = 0)"
    using local.t_a_var local.test_def pcorrect pcorrect_iff1_op by auto
  also have "\<dots> = (\<alpha> p \<cdot> x  \<le> x \<cdot> \<alpha> p \<and> x \<cdot> \<alpha> p \<le> \<alpha> p \<cdot> x)"
    using pcorrect_iff1 pcorrect_iff1_op by auto
  finally show ?thesis
    by fastforce
qed

lemma cond_merge:
  assumes "\<tau> p \<cdot> x = x \<cdot> \<tau> p"
  shows "if p then (x \<cdot> y) else (x \<cdot> z) fi = x \<cdot> (if p then y else z fi)"
proof-
  have "if p then (x \<cdot> y) else (x \<cdot> z) fi = \<tau> p \<cdot> x \<cdot> y + \<alpha> p \<cdot> x \<cdot> z"
    by (simp add: cond_def mult_assoc)
  also have "\<dots> = x \<cdot> \<tau> p \<cdot> y + x \<cdot> \<alpha> p \<cdot> z"
    using assms cond_merge_aux by force
 also have "\<dots> = x \<cdot> (\<tau> p \<cdot> y + \<alpha> p \<cdot> z)"
   by (simp add: distl mult_assoc)
  also have "\<dots> = x \<cdot> (if p then y else z fi)"
    by (simp add: cond_def)
  finally show ?thesis.
qed

lemma loop_denest: "while p do (x \<cdot> (while q do y od)) od = if p then (x \<cdot> (while (\<tau> p + \<tau> q) do (if q then y else x fi) od)) else 1 fi"
proof-
  have "while (\<tau> p + \<tau> q) do (if q then y else x fi) od = ((\<tau> p + \<tau> q) \<cdot> (\<tau> q \<cdot> y + \<alpha> q \<cdot> x))\<^sup>\<star> \<cdot> \<alpha> q \<cdot> \<alpha> p"
    unfolding while_def cond_def
    using a_comm a_de_morgan3 mult_assoc t_mult_closed test_def by simp
  also have "\<dots> = (\<alpha> q \<cdot> \<tau> p \<cdot> x + \<tau> q \<cdot> y)\<^sup>\<star> \<cdot> \<alpha> q \<cdot> \<alpha> p"
    by (smt add_commute cond_merge_aux a_absorb2 a_comm a_idem distl distr mult_assoc test_def pcorrect_iff2)
  also have "\<dots> = (\<tau> q \<cdot> y)\<^sup>\<star> \<cdot> (\<alpha> q \<cdot> \<tau> p \<cdot> x \<cdot> (\<tau> q \<cdot> y)\<^sup>\<star>)\<^sup>\<star> \<cdot> \<alpha> q \<cdot> \<alpha> p"
    by (simp add: add_commute star_denest)
  also have "\<dots> = (\<tau> q \<cdot> y)\<^sup>\<star> \<cdot> \<alpha> q \<cdot> (\<tau> p \<cdot> x \<cdot> (\<tau> q \<cdot> y)\<^sup>\<star> \<cdot> \<alpha> q)\<^sup>\<star> \<cdot> \<alpha> p"
    by (simp add: mult_assoc star_slide)
  finally have "while (\<tau> p + \<tau> q) do (if q then y else x fi) od = (\<tau> q \<cdot> y)\<^sup>\<star> \<cdot> \<alpha> q \<cdot> (\<tau> p \<cdot> x \<cdot> (\<tau> q \<cdot> y)\<^sup>\<star> \<cdot> \<alpha> q)\<^sup>\<star> \<cdot> \<alpha> p".
  hence "if p then (x \<cdot> (while (\<tau> p + \<tau> q) do (if q then y else x fi) od)) else 1 fi = \<tau> p \<cdot> x \<cdot> (\<tau> q \<cdot> y)\<^sup>\<star> \<cdot> \<alpha> q \<cdot> (\<tau> p \<cdot> x \<cdot> (\<tau> q \<cdot> y)\<^sup>\<star> \<cdot> \<alpha> q)\<^sup>\<star> \<cdot> \<alpha> p  + \<alpha> p"
    by (simp add: cond_def mult_assoc)
  also have "\<dots> = (1 + \<tau> p \<cdot> x \<cdot> (\<tau> q \<cdot> y)\<^sup>\<star> \<cdot> \<alpha> q \<cdot> (\<tau> p \<cdot> x \<cdot> (\<tau> q \<cdot> y)\<^sup>\<star> \<cdot> \<alpha> q)\<^sup>\<star>) \<cdot> \<alpha> p"
    using add_commute distr mult_1_left by presburger
  also have "\<dots> = (\<tau> p \<cdot> x \<cdot> (\<tau> q \<cdot> y)\<^sup>\<star> \<cdot> \<alpha> q)\<^sup>\<star> \<cdot> \<alpha> p"
    by simp
  also have "\<dots> = while p do x \<cdot> (while q do y od) od"
    by (simp add: mult_assoc while_def)
  finally show ?thesis..
qed

end

subsection \<open>A Locale for KAT\<close>

locale katloc =
  fixes test :: "'a::boolean_algebra \<Rightarrow> 'b::kleene_algebra" ("\<iota>")
  and not :: "'b::kleene_algebra \<Rightarrow> 'b::kleene_algebra" ("!")
  assumes test_sup: "\<iota> (sup p q) = \<iota> p + \<iota> q"
  and test_inf: "\<iota> (inf p q) = \<iota> p \<cdot> \<iota> q"
  and test_top: "\<iota> top = 1"
  and test_bot: "\<iota> bot = 0"
  and test_not: "\<iota> (- p) = ! (\<iota> p)" 
  and test_iso_eq: "p \<le> q \<longleftrightarrow> \<iota> p \<le> \<iota> q"

begin

lemma test_eq: "p = q \<longleftrightarrow> \<iota> p = \<iota> q"
  by (metis eq_iff test_iso_eq)

lemma test_iso: "p \<le> q \<Longrightarrow> \<iota> p \<le> \<iota> q"
  by (simp add: test_iso_eq)

lemma test_meet_comm: "\<iota> p \<cdot> \<iota> q = \<iota> q \<cdot> \<iota> p"
  by (metis inf.commute test_inf)

lemma [simp]: "! (\<iota> (p)) + \<iota> p = 1"
  by (metis compl_sup_top test_not test_sup test_top)

lemma [simp]: "\<iota> p + \<iota> (-p) = 1"
  by (metis sup_compl_top test_sup test_top)

lemma [simp]: "\<iota> (-p) \<cdot> \<iota> p = 0"
  by (metis compl_inf_bot test_bot test_inf)

lemma [simp]: "\<iota> p \<cdot> ! (\<iota> p) = 0"
  by (metis inf_compl_bot test_bot test_inf test_not)

end

subsection \<open>Relational and State Transformer Model\<close>

definition rel_atest :: "'a rel \<Rightarrow> 'a rel" ("\<alpha>\<^sub>r") where 
  "\<alpha>\<^sub>r R = Id \<inter> -R"  

interpretation rel_kat: kat "(\<union>)" "{}" Id "(;)" "(\<subseteq>)" "(\<subset>)" rtrancl "\<alpha>\<^sub>r" 
  by unfold_locales (auto simp: rel_atest_def)

definition sta_atest :: "'a sta \<Rightarrow> 'a sta" ("\<alpha>\<^sub>s") where
  "\<alpha>\<^sub>s f x = \<eta> x - f x"

lemma katest_iff: "y \<in> \<alpha>\<^sub>s f x \<longleftrightarrow> y \<in> \<eta> x \<and> \<not> y \<in> f x"
  unfolding sta_atest_def by simp

declare katest_iff [sta_unfolds]

interpretation sta_kat: kat "(+\<^sub>K)" "\<nu>" "\<eta>" "(\<circ>\<^sub>K)" "(\<sqsubseteq>)" "(\<sqsubset>)" kstar "\<alpha>\<^sub>s"
  by unfold_locales (auto simp: sta_unfolds)

lemma r2s_atest: "\<S> (\<alpha>\<^sub>r R) = \<alpha>\<^sub>s (\<S> R)"
  unfolding sta_unfolds s2r_def rel_atest_def 

  by (metis ComplD ComplI IntE IntI r2s_iff  s2r_id) 

lemma s2r_atest: "\<R> (\<alpha>\<^sub>s f) = \<alpha>\<^sub>r (\<R> f)"
  by (metis r2s2r_galois r2s_atest)

lemma p2r_atest [simp]: "\<alpha>\<^sub>r \<lceil>P\<rceil>\<^sub>r = \<lceil>\<lambda>x. \<not> P x\<rceil>\<^sub>r"
  unfolding p2r_def rel_atest_def by force

lemma p2r_test [simp]: "rel_kat.test \<lceil>P\<rceil>\<^sub>r = \<lceil>P\<rceil>\<^sub>r"
  unfolding rel_kat.test_def by force

lemma p2s_atest [simp]: "\<alpha>\<^sub>s \<lceil>P\<rceil>\<^sub>s = \<lceil>\<lambda>x. \<not> P x\<rceil>\<^sub>s"
  unfolding  p2s_def s2p_def sta_atest_def fun_eq_iff by force

lemma p2s_test [simp]: "sta_kat.test \<lceil>P\<rceil>\<^sub>s = \<lceil>P\<rceil>\<^sub>s"
  unfolding sta_kat.test_def by force

end





