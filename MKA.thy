(* Title: Program Correctness Component Based on Modal Kleene Algebra
   Author: Peixin You
*)

section \<open>Verification Component Based on Modal Kleene Algebra\<close>

theory MKA
  imports KA Store

begin

subsection \<open>Definitions\<close>

class antidomain_kleene_algebra = kleene_algebra + 
  fixes ad :: "'a \<Rightarrow> 'a" 
  assumes ad_annil [simp]: "ad x \<cdot> x = 0"
  and ad_local_sub [simp]: "ad (x \<cdot> y) \<le> ad (x \<cdot> ad (ad y))"
  and ad_compl1 [simp]: "ad (ad x) + ad x = 1"

begin

definition dom_op :: "'a \<Rightarrow> 'a" ("do") where
  "do x = ad (ad x)"

definition fdia :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "fdia x y = do (x \<cdot> y)"

definition fbox :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "fbox x y = ad (x \<cdot> ad y)"

end

class antirange_kleene_algebra = kleene_algebra +
  fixes ar :: "'a \<Rightarrow> 'a" 
  assumes ar_annil [simp]: "x \<cdot> ar x  = 0"
  and ar_local_sub [simp]: "ar (x \<cdot> y) \<le> ar (ar (ar x) \<cdot> y)"
  and ar_compl1 [simp]: "ar (ar x) + ar x = 1"

begin

definition range_op :: "'a \<Rightarrow> 'a" ("ra") where
  "ra x = ar (ar x)"

definition bdia :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "bdia x y = ra (y \<cdot> x)"

definition bbox :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  where
  "bbox x y = ar (ar y \<cdot> x)"

end

class modal_kleene_algebra = antidomain_kleene_algebra + antirange_kleene_algebra 

subsection \<open>Formalisation of Opposition Duality\<close>

sublocale antirange_kleene_algebra \<subseteq> op_arka: antidomain_kleene_algebra "(+)" "0" "1" "\<lambda>x y. y \<cdot> x" "(\<le>)" "(<)" _ ar
  rewrites "op_arka.dom_op x = ra x"
  and "op_arka.fdia x y = bdia x y"
  and "op_arka.fbox x y = bbox x y"
proof -
  show "class.antidomain_kleene_algebra (+) 0 1 (\<lambda>x y. y \<cdot> x) (\<le>) (<) star ar"
    by unfold_locales (simp_all add: mult_assoc distr distl star_inductl star_inductr)
  then interpret op_arka: antidomain_kleene_algebra "(+)" "0" "1" "(\<lambda>x y. y \<cdot> x)" "(\<le>)" "(<)" star ar.
  show "op_arka.dom_op x = ra x"
    by (simp add: range_op_def op_arka.dom_op_def)
  show "op_arka.fdia x y = bdia x y"
    by (simp add: bdia_def range_op_def op_arka.dom_op_def op_arka.fdia_def)
  show "op_arka.fbox x y = bbox x y"
    by (simp add: bbox_def op_arka.fbox_def)
qed

sublocale antidomain_kleene_algebra \<subseteq> arka_op: antirange_kleene_algebra "(+)" "0" "1" "(\<lambda>x y. y \<cdot> x)" "(\<le>)" "(<)" star ad
  rewrites "arka_op.range_op x = do x"
  and "arka_op.bdia x y = fdia x y"
  and "arka_op.bbox x y = fbox x y"
proof -
  show "class.antirange_kleene_algebra (+) 0 1 (\<lambda>x y. y \<cdot> x) (\<le>) (<) star ad"
    by unfold_locales (simp_all add: mult_assoc distl distr star_inductl star_inductr)
  then interpret arka_op: antirange_kleene_algebra "(+)" "0" "1" "(\<lambda>x y. y \<cdot> x)" "(\<le>)" "(<)" star ad.
  show "arka_op.range_op x = do x"
    by (simp add: arka_op.range_op_def dom_op_def)
  show "arka_op.bdia x y = fdia x y"
    by (simp add: arka_op.bdia_def arka_op.range_op_def dom_op_def fdia_def)
  show "arka_op.bbox x y = fbox x y"
    by (simp add: arka_op.bbox_def fbox_def)
qed

subsection \<open>Basic Properties\<close>

context antidomain_kleene_algebra
begin

lemma a_subid_aux: "ad x \<cdot> y \<le> y"
  by (metis ad_compl1 add.commute add_ubl mult.left_neutral mult_isor)

lemma d1_a [simp]: "do x \<cdot> x = x"
  unfolding dom_op_def by (metis add_0_right ad_annil ad_compl1 distr mult_1_left)
                                  
lemma ad_one [simp]: "ad 1 = 0"
  by (metis ad_annil mult_1_right)

lemma ad_zero [simp]: "ad 0 = 1"
  by (metis ad_one ad_compl1 add_0_right)

lemma ad_compl2 [simp]: "ad x \<cdot> do x = 0"
  by (metis antisym arka_op.ar_annil arka_op.ar_local_sub dom_op_def mult_1_left mult_isor zero_least)

lemma ad_d: "(ad x \<cdot> y = 0) = (do x \<cdot> y = y)"
  by (metis ad_compl2 add_commute dom_op_def ad_compl1 add_0_left annil distr mult_1_left mult_assoc)

lemma d_a_closed [simp]: "ad (do x) = ad x"
  by (metis ad_one ad_zero ad_zero d1_a dom_op_def ad_annil ad_compl1 annir distl mult_1_right)

lemma a_idem [simp]: "ad x \<cdot> ad x = ad x"
  by (metis d1_a d_a_closed dom_op_def)

lemma meet_ord: "(ad x \<le> ad y) = (ad x \<cdot> ad y = ad x)"
  by (metis a_subid_aux d1_a d_a_closed dom_op_def antisym mult_1_right mult_isol)

lemma d_wloc: "(x \<cdot> y = 0) = (x \<cdot> do y = 0)"
  by (metis a_subid_aux d1_a dom_op_def ad_annil ad_local_sub antisym mult_1_right mult_assoc)

lemma gla: "(ad x \<cdot> y = 0) = (ad x \<le> ad y)"
  apply standard
   apply (smt a_subid_aux add_commute d_wloc dom_op_def ad_compl1 add_0_right distl mult_1_right)
  by (metis ad_annil annir mult_assoc meet_ord)

lemma a_local [simp]: "ad (x \<cdot> do y) = ad (x \<cdot> y)"
  by (smt d_wloc gla ad_annil antisym mult_assoc)                                              

lemma a_supdist: "ad (x + y) \<le> ad x"
  by (metis gla ad_annil add_0_right add_ubl distl order_def)

lemma a_antitone: "x \<le> y \<Longrightarrow> ad y \<le> ad x"
  by (metis a_supdist order_def)

lemma d_iso: "x \<le> y \<Longrightarrow> do x \<le> do y"
  by (simp add: a_antitone dom_op_def)

lemma d_a_ord: "(do x \<le> do y) = (ad y \<le> ad x)"
  using a_antitone dom_op_def by fastforce

lemma llp: "(do y \<cdot> x = x) = (do x \<le> do y)"
  by (metis a_antitone ad_d d_a_closed dom_op_def gla)

lemma a_comm: "ad x \<cdot> ad y = ad y \<cdot> ad x"
  by (rule antisym) (metis a_local a_subid_aux d1_a d_a_closed d_iso dom_op_def eq_refl mult_1_right mult_iso)+

lemma a_closed [simp]: "do (ad x \<cdot> ad y) = ad x \<cdot> ad y"
  by (smt a_comm a_idem a_subid_aux ad_zero d1_a d_a_closed d_iso dom_op_def mult_1_right mult_assoc meet_ord)

lemma a_exp [simp]: "ad (ad x \<cdot> y) = do x + ad y"
proof (rule antisym)
  have a: "ad (ad x \<cdot> y) \<cdot> do y \<le> do x"
    by (smt a_closed a_comm a_local ad_compl2 gla dom_op_def mult_assoc)
  have "ad (ad x \<cdot> y) = ad (ad x \<cdot> y) \<cdot> do y + ad (ad x \<cdot> y) \<cdot> ad y"
    by (metis dom_op_def ad_compl1 distl mult_1_right)
  thus "ad (ad x \<cdot> y) \<le> do x + ad y"
    by (metis a a_subid_aux add_iso)
next
  show "do x + ad y \<le> ad (ad x \<cdot> y)"
    by (metis a_antitone a_comm a_local a_subid_aux add_lub dom_op_def)
qed  

lemma a_de_morgan: "ad (ad x \<cdot> ad y) = do x + do y"
  by (simp add: dom_op_def)

lemma d1_sum_var: "x + y \<le> (do x + do y) \<cdot> (x + y)"
  by (simp add: add_commute add_iso add_ubl distl distr)

lemma a_dual_add: "ad (x + y) = ad x \<cdot> ad y"
  apply (rule antisym)
  apply (metis a_supdist add_commute  mult_isor meet_ord)
  by (metis a_closed a_de_morgan a_exp a_subid_aux d1_sum_var antisym  order_def)

lemma d_add: "do (x + y) = do x + do y"
  by (simp add: a_dual_add dom_op_def)

lemma a_absorb1 [simp]: "ad x \<cdot> (ad x + ad y) = ad x"
  using a_dual_add a_supdist add_commute distl order_def by auto

lemma a_absorb2 [simp]: "ad x + ad x \<cdot> ad y = ad x"
  using a_dual_add a_supdist add_commute order_def by auto

lemma a_dist: "ad x + ad y \<cdot> ad z = (ad x + ad y) \<cdot> (ad x + ad z)"
  by (smt a_absorb1 a_subid_aux abel_semigroup.commute abel_semigroup.left_commute add.abel_semigroup_axioms distl distr order_def)

lemma a_lbl: "ad x \<cdot> ad y \<le> ad x"
  using a_dual_add a_supdist by simp

lemma a_lower: "ad x \<le> ad y \<Longrightarrow> ad x \<le> ad z \<Longrightarrow> ad x \<le> ad y \<cdot> ad z"
  by (simp add: a_dist order_def)

lemma a_glb: "(ad x \<le> ad y \<and> ad x \<le> ad z) = (ad x \<le> ad y \<cdot> ad z)"
  using a_lbl a_lower a_subid_aux dual_order.trans by blast

lemma at_shunt: "(ad x \<cdot> ad y \<le> ad z) = (ad x \<le> do y + ad z)"
  by (metis a_dual_add a_exp gla mult_assoc)

lemma a_comp_dist [simp]: "(ad p + ad q) \<cdot> (do p + ad t) = ad p \<cdot> ad t + do p \<cdot> ad q"
proof-
  have "(ad p + ad q) \<cdot> (do p + ad t) = ad p \<cdot> ad t + do p \<cdot> ad q + (ad p + do p) \<cdot> ad q \<cdot> ad t"
    using a_comm ad_compl2 add_commute add_assoc arka_op.ar_compl1 distl distr dom_op_def by simp
  also have "\<dots> = ad p \<cdot> ad t + do p \<cdot> ad q + ad p \<cdot> ad q \<cdot> ad t + do p \<cdot> ad q \<cdot> ad t"
    by (simp add: add_assoc distr)
  also have "\<dots> = (1 + ad q) \<cdot> ad p \<cdot> ad t + (1 + ad t) \<cdot> do p \<cdot> ad q"
    by (smt a_comm add_commute add.left_commute arka_op.distl arka_op.range_op_def mult.semigroup_axioms mult_1_left semigroup.assoc)
  finally show ?thesis
    by (metis a_absorb2 ad_zero mult_1_left)
qed

lemma pcorrect_if1: "ad p \<cdot> x \<le> x \<cdot> ad q \<Longrightarrow> ad p \<cdot> x \<cdot> do q = 0"
  by (smt d_wloc ad_annil add_0_right annir arka_op.mult_assoc distr order_def)

lemma pcorrect_if2: "ad p \<cdot> x \<cdot> do q = 0 \<Longrightarrow> ad p \<cdot> x \<cdot> ad q = ad p \<cdot> x"
  by (metis a_absorb2 d_a_closed local.arka_op.annil arka_op.ar_annil arka_op.ar_compl1 arka_op.distr arka_op.range_op_def mult_1_right) 

lemma pcorrect_if3: "ad p \<cdot> x = ad p \<cdot> x \<cdot> ad q \<Longrightarrow> ad p \<cdot> x \<le> x \<cdot> ad q"
  by (metis a_subid_aux mult_isor)

lemma pcorrect_iff1: "(ad p \<cdot> x \<le> x \<cdot> ad q) = (ad p \<cdot> x \<cdot> do q = 0)"  
   by (metis pcorrect_if1 pcorrect_if2 pcorrect_if3)

lemma pcorrect_iff2: "(ad p \<cdot> x \<cdot> do q = 0) = (ad p \<cdot> x \<cdot> ad q = ad p \<cdot> x)" 
  by (metis pcorrect_if1 pcorrect_if2 pcorrect_if3) 

lemma pcorrect_iff2_op: "(do p \<cdot> x \<cdot> ad q = 0) = (x \<cdot> ad q = ad p \<cdot> x \<cdot> ad q)"
  by (metis ad_d d_a_closed arka_op.mult_assoc dom_op_def)

lemma pcorrect_iff3_op: "(x \<cdot> ad q = ad p \<cdot> x \<cdot> ad q) = (x \<cdot> ad q \<le> ad p \<cdot> x)"
  apply standard
  apply (metis a_subid_aux mult_1_right mult_isol)
  by (metis a_antitone a_exp d_a_closed llp add_lub arka_op.mult_assoc dom_op_def)

lemma pcorrect_iff1_op: "(x \<cdot> ad q \<le> ad p \<cdot> x) = (do p \<cdot> x \<cdot> ad q = 0)"
  by (simp add: pcorrect_iff2_op pcorrect_iff3_op)

lemma pcorrect_var: "(ad p \<cdot> x \<le> x \<cdot> ad q) = (x \<cdot> do q \<le> do p \<cdot> x)"
  using d_a_closed  dom_op_def pcorrect_iff1 pcorrect_iff1_op by auto

lemma pcorrect_var2: "(do p \<cdot> x \<le> x \<cdot> do q) = (x \<cdot> ad q \<le> ad p \<cdot> x)"
  by (metis d_a_closed local.dom_op_def pcorrect_iff1 pcorrect_iff1_op)

lemma ad_star [simp]: "ad (x\<^sup>\<star>) = 0"
  by (metis a_dual_add ad_one annil star_unfoldl_eq)

end

context antidomain_kleene_algebra
begin

subsection \<open>Forward Diamond and Box Operators\<close>

lemma fbox_fdia: "fbox x p = ad (fdia x (ad p))"
  by (simp add: fbox_def fdia_def)

lemma fdia_fbox: "fdia x p = ad (fbox x (ad p))"
  using a_local dom_op_def fbox_def fdia_def by simp

lemma fdia_demod: "(fdia x y \<le> do z) = (x \<cdot> do y \<le> do z \<cdot> x)"
  by (unfold fdia_def, metis a_local arka_op.mult_assoc dom_op_def llp pcorrect_iff3_op)

lemma fbox_demod: "(do y \<le> fbox x z) = (do y \<cdot> x  \<le> x \<cdot> do z)"
  by (unfold fbox_def, metis arka_op.mult_assoc d_a_closed dom_op_def gla pcorrect_iff1)

lemma fdia_dom [simp]: "fdia x 1 = do x"
  by (simp add: fdia_def)

lemma fbox_dom [simp]: "fbox x 0 = ad x"
  by (simp add: fbox_def)

lemma fdia_one [simp]: "fdia 1 x = do x"
  by (simp add: fdia_def)

lemma fbox_zero [simp]: "fbox 0 x = 1"
  by (simp add: fbox_def)

lemma fdia_zero_var [simp]: "fdia 0 x = 0"
  by (simp add: dom_op_def fdia_def)

lemma fbox_zero_var [simp]: "fbox 1 x = do x"
  by (simp add: dom_op_def fbox_def) 

lemma fdia_zero [simp]: "fdia x 0 = 0"
  by (simp add: dom_op_def fdia_def)

lemma fbox_one_1 [simp]: "fbox x 1 = 1"
  by (simp add: fbox_def)

lemma fdia_add1: "fdia x (y + z) = fdia x y + fdia x z"
  by (simp add: a_dual_add distl dom_op_def fdia_def)

lemma fbox_add1: "fbox x (do y \<cdot> do z) = fbox x y \<cdot> fbox x z"
  by (metis a_dual_add a_local arka_op.distr dom_op_def fbox_def)

lemma fdia_add2: "fdia (x + y) z = fdia x z + fdia y z"
  by (simp add: a_dual_add distr dom_op_def fdia_def)

lemma fbox_add2: "fbox (x + y) z = fbox x z \<cdot> fbox y z"
  by (simp add: a_dual_add fbox_def distr)

lemma fdia_comp: "fdia (x \<cdot> y) z = fdia x (fdia y z)"
  using a_local arka_op.mult_assoc arka_op.range_op_def fdia_def by auto

lemma fbox_comp: "fbox (x \<cdot> y) z = fbox x (fbox y z)"
  using a_local dom_op_def fbox_def mult_assoc by auto

lemma fdia_iso1: "do x \<le> do y \<Longrightarrow> fdia z x \<le> fdia z y"
  by (metis a_dual_add a_exp a_local arka_op.distr dom_op_def fdia_def order_def)

lemma fbox_iso: "do x \<le> do y \<Longrightarrow> fbox z x \<le> fbox z y"
  by (metis a_antitone d_a_closed fbox_def mult_isol)

lemma fdia_iso2: "x \<le> y \<Longrightarrow> fdia x z \<le> fdia y z"
  by (simp add: d_iso fdia_def mult_isor)

lemma fbox_anti: "x \<le> y \<Longrightarrow> fbox y z \<le> fbox x z"
  by (simp add: a_antitone fbox_fdia fdia_iso2)

lemma fdia_export: "ad y \<cdot> fdia x z = fdia (ad y \<cdot> x) z"
  using a_closed dom_op_def fdia_def fdia_comp by simp

lemma fbox_export: "ad y + fbox x y = fbox (do y \<cdot> x) y"
  by (metis fbox_fdia fdia_export a_exp d_a_closed  dom_op_def)

lemma fdia_diff: "fdia x (do y \<cdot> ad z) \<le> fdia x y + ad (fdia x z)"
  by (metis fdia_iso1 a_closed a_lbl add_ubl dom_op_def dual_order.trans)

lemma fbox_diff: "fbox x (do y + ad z) \<le> fbox x y + ad (fbox x z)"
proof-
  have "fbox x (do y + ad z) \<cdot> fbox x z \<le> fbox x y"
    by (metis add_commute fbox_add1 fbox_iso a_closed a_idem arka_op.range_op_def at_shunt d1_sum_var d_add)
  thus ?thesis
    by (simp add: add_commute at_shunt dom_op_def fbox_def)
qed

lemma fdia_star_unfoldl [simp]: "fdia 1 y + fdia x (fdia (x\<^sup>\<star>) y) = fdia (x\<^sup>\<star>) y"
  by (metis fdia_add2 fdia_comp star_unfoldl_eq)

lemma fbox_star_unfoldl [simp]: "fbox 1 y \<cdot> fbox x (fbox (x\<^sup>\<star>) y) = fbox (x\<^sup>\<star>) y"
  by (metis fbox_add2 fbox_comp star_unfoldl_eq)

lemma fdia_star_unfoldr [simp]: "fdia 1 y + fdia (x\<^sup>\<star>) (fdia x y) = fdia (x\<^sup>\<star>) y"
  by (metis fdia_add2 fdia_comp star_unfoldr_eq)

lemma fbox_star_unfoldr [simp]: "fbox 1 y \<cdot> fbox (x\<^sup>\<star>) (fbox x y) = fbox (x\<^sup>\<star>) y"
  by (metis fbox_add2 fbox_comp star_unfoldr_eq)

lemma fdia_star_inductl_var: "fdia x y \<le> do y \<Longrightarrow> fdia (x\<^sup>\<star>) y \<le> do y"
  by (simp add: fdia_demod star_sim2)

lemma fbox_star_inductl_var: "do y \<le> fbox x y \<Longrightarrow> do y \<le> fbox (x\<^sup>\<star>) y"
  using d_a_ord fdia_star_inductl_var dom_op_def fbox_def fdia_def by auto

lemma fdia_star_inductl: "do z + fdia x y \<le> do y \<Longrightarrow> fdia (x\<^sup>\<star>) z \<le> do y"
  using fdia_iso1 fdia_star_inductl_var add_lub dual_order.trans by blast

lemma fbox_star_inductl: "do y \<le> do z \<cdot> fbox x y \<Longrightarrow> do y \<le> fbox (x\<^sup>\<star>) z"
  by (metis a_comm a_subid_aux fbox_fdia fbox_iso fbox_star_inductl_var dom_op_def dual_order.trans)

end

subsection \<open>Coherence, Galois Connections and Conjugations\<close>

context modal_kleene_algebra
begin

lemma dr_coh_aux1 [simp]: "ar x \<cdot> do (ra x) = 0"
proof-
  have "ar x \<cdot> ra x = 0"
    by (simp add: range_op_def)
  thus "ar x \<cdot> do (ra x) = 0"
    using d_wloc by simp
qed

lemma dr_coh_aux2 [simp]: "ra x \<cdot> do (ra x) \<cdot> ar x = 0"
proof-
  have "ra x \<cdot> do (ra x) \<cdot> ar x \<le> ra x \<cdot> ar x"
    by (metis a_subid_aux arka_op.mult_assoc dom_op_def mult_isol)
  also have "\<dots> = 0"
    by simp
  finally show ?thesis
    using order_def by simp
qed

lemma dr_coh [simp]: "do (ra x) = ra x"
proof -
  have "do (ra x) = (ar x + ra x) \<cdot> do (ra x)"
    using add_commute op_arka.ad_compl1 range_op_def by auto
  also have "\<dots> = ar x \<cdot> do (ra x) + ra x \<cdot> do (ra x) \<cdot> (ar x + ra x)"
    by (metis (mono_tags, lifting) add_commute arka_op.distl mult_1_right op_arka.ad_compl1 range_op_def)
  also have "\<dots> =  0 + ra x \<cdot> do (ra x) \<cdot> ar x + ra x \<cdot> do (ra x) \<cdot> ra x"
    using distl by simp
  also have "\<dots> = 0 + ra x \<cdot> ra x"
    by (simp add: mult.semigroup_axioms semigroup.assoc)
  also have "\<dots> = ra x"
    by (simp add: local.range_op_def)
  finally show ?thesis.
qed

lemma rd_coh [simp]: "ra (do x) = do x"
  by (smt dr_coh a_comm ad_compl2 ad_d dom_op_def op_arka.d_wloc)

lemma do_ra: "(do x = x) = (ra x = x)"
  by (metis dr_coh rd_coh)

lemma do_ra_alg: "{x. do x = x} = {x. ra x = x}"
  by (simp add: do_ra)

lemma dr_zero: "(x \<cdot> y = 0) = (ra x \<cdot> do y = 0)"
  by (metis d_wloc op_arka.d_wloc)

lemma bdia_fbox_galois: 
  assumes "do p = p" and "do q = q"
  shows "(bdia x p \<le> q) = (p \<le> fbox x q)"
proof-
  have "(bdia x p \<le> q) = (p \<cdot> x \<le> x \<cdot> q)"
    by (metis assms op_arka.fdia_demod rd_coh)
  also have "\<dots> = (p \<le> fbox x q)"
    by (metis assms fbox_demod)
  finally show ?thesis.
qed

lemma fdia_bbox_galois: 
  assumes "do p = p" and "do q = q"
  shows "(fdia x p \<le> q) = (p \<le> bbox x q)"
  by (metis assms fdia_demod op_arka.fbox_demod rd_coh)

lemma dia_conjugation: 
  assumes "do p = p" and "do q = q"
  shows "(p \<cdot> fdia x q = 0) = (bdia x p \<cdot> q = 0)"
proof-
  have "(p \<cdot> fdia x q = 0) = (fdia x q \<le> ad p)"
    by (metis assms ad_d dom_op_def fdia_fbox gla llp)
  also have "\<dots> = (q \<le> bbox x (ar p))"
    by (metis assms do_ra fdia_bbox_galois ad_d local.dom_op_def op_arka.a_idem op_arka.ad_d range_op_def)
  also have "\<dots> = (q \<le> ar (bdia x p))"
    by (metis assms op_arka.fbox_fdia range_op_def rd_coh)
  also have "\<dots> = (bdia x p \<cdot> q = 0)"
    by (metis assms op_arka.gla range_op_def rd_coh)
  finally show ?thesis.
qed

lemma box_conjugation: 
  assumes "do p = p" and "do q = q"
  shows "(p + fbox x q = 1) = (bbox x p + q = 1)"
proof-
  have "(p + fbox x q = 1) = (ad p \<cdot> ad (fbox x q) = 0)"
    by (metis assms a_dual_add a_exp a_local ad_one ad_zero dom_op_def fbox_def)
  also have "\<dots> = (ad p \<cdot> fdia x (ad q) = 0)"
    by (simp add: dom_op_def fbox_def fdia_def)
  also have "\<dots> = (bdia x (ar p) \<cdot> ar q = 0)"
    by (smt assms dia_conjugation do_ra ad_d dom_op_def op_arka.a_idem op_arka.ad_d range_op_def)
  also have "\<dots> = (ar (bbox x p) \<cdot> ar q = 0)"
    by (simp add: op_arka.fbox_def op_arka.fdia_def range_op_def)
  also have "\<dots> = (bbox x p + q = 1)"
    by (metis \<open>(bdia x (ar p) \<cdot> ar q = 0) = (ar (bbox x p) \<cdot> ar q = 0)\<close> add_commute assms op_arka.a_dual_add op_arka.a_exp op_arka.ad_one op_arka.ad_zero op_arka.fbox_fdia rd_coh)
  finally show ?thesis.
qed

end

subsection \<open>Algebraic Laws for VCG\<close>

context antidomain_kleene_algebra
begin

definition cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _ fi" [64,64,64] 63) where
  "if p then x else y fi = do p \<cdot> x + ad p \<cdot> y"

definition while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _ od" [64,64] 63) where
  "while p do x od = (do p \<cdot> x)\<^sup>\<star> \<cdot> ad p"

definition while_inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ inv _ do _ od" [64,64,64] 63) where
  "while p inv i do x od = while p do x od"

lemma while_if: "while p do x od = if p then x \<cdot> (while p do x od) else 1 fi"
  by (smt abel_semigroup.commute cond_def a_comm ad_zero add.abel_semigroup_axioms distr mult.semigroup_axioms star_unfoldl_eq semigroup.assoc while_def)

lemma fbox_cond: "fbox (if p then x else y fi) q = (ad p + fbox x q) \<cdot> (do p + fbox y q)"
proof- 
  have "fbox (if p then x else y fi) q = fbox (do p \<cdot> x + ad p \<cdot> y) q"
    by (simp add: cond_def)
  also have "\<dots> = fbox (do p \<cdot> x) q \<cdot> fbox (ad p \<cdot> y) q"
    by (simp add: fbox_add2)
  also have "\<dots> = (ad p + fbox x q) \<cdot> (do p + fbox y q)"
    by (metis a_exp arka_op.mult_assoc d_a_closed dom_op_def fbox_def)
  finally show ?thesis.
qed

lemma fbox_condl: "do p \<cdot> fbox (if p then x else y fi) q = do p \<cdot> fbox x q"
proof-
  have "do p \<cdot> fbox (if p then x else y fi) q = do p \<cdot> (ad p + fbox x q) \<cdot> (do p + fbox y q)"
    by (simp add: fbox_cond arka_op.mult_assoc)
  also have "\<dots> = do p \<cdot> fbox x q \<cdot> (do p + fbox y q)"
    by (simp add: distl dom_op_def)
  also have "\<dots> = do p \<cdot> fbox x q"
    by (metis a_absorb1 a_comm arka_op.mult_assoc dom_op_def fbox_fdia)
  finally show ?thesis.
qed

lemma fbox_condr: "ad p \<cdot> fbox (if p then x else y fi) q = ad p \<cdot> fbox y q"
proof-
  have "ad p \<cdot> fbox (if p then x else y fi) q = ad p \<cdot> (ad p + fbox x q) \<cdot> (do p + fbox y q)"
    by (simp add: fbox_cond arka_op.mult_assoc)
  also have "\<dots> = ad p \<cdot> (do p + fbox y q)"
    by (simp add: fbox_def)
  also have "\<dots> = ad p \<cdot> fbox y q"
    by (simp add: arka_op.distr)
  finally show ?thesis.
qed

lemma fbox_cond_var: "fbox (if p then x else y fi) q = (do p \<cdot> fbox x q) + (ad p \<cdot> fbox y q)"
  using add_commute fbox_cond fbox_def by simp

lemma fbox_while: 
  assumes "do p \<cdot> do t \<le> fbox x p"
  shows "do p \<le> fbox (while t do x od) (do p \<cdot> ad t)"
proof -
  have  "do p \<cdot> do t \<cdot> x \<le> do t \<cdot> x \<cdot> do p"
    by (metis assms a_exp arka_op.mult_assoc at_shunt dom_op_def fbox_def fbox_demod)
  hence "do p \<cdot> (do t \<cdot> x)\<^sup>\<star> \<cdot> ad t \<le> (do t \<cdot> x)\<^sup>\<star> \<cdot> do p \<cdot> ad t"
    by (metis arka_op.mult_assoc mult_isor star_sim1)
  also have "\<dots> = (do t \<cdot> x)\<^sup>\<star> \<cdot> ad t \<cdot> do p \<cdot> ad t"
    by (metis add_commute a_dual_add add_ubl arka_op.mult_assoc dom_op_def order_def)
  finally show ?thesis
    using a_closed arka_op.range_op_def fbox_demod mult.semigroup_axioms semigroup.assoc while_def by fastforce
qed

lemma fbox_whilet: "do p \<cdot> fbox (while p do x od) q = do p \<cdot> fbox x (fbox (while p do x od) q)"
  by (metis fbox_condl fbox_comp while_if)

lemma fbox_whilef: "ad p \<cdot> fbox (while p do x od) q = ad p \<cdot> do q"
  by (metis fbox_condr fbox_zero_var while_if)

lemma fbox_while_inv: 
  assumes "do p \<le> do i"
  and "do i \<cdot> ad t \<le> do q"
  and "do i \<cdot> do t \<le> fbox x i"
shows "do p \<le> fbox (while t inv i do x od) q"
  by (unfold while_inv_def, smt assms fbox_while a_closed distl dom_op_def dual_order.trans fbox_demod order_def)

end


subsection \<open>Relation and State Transformer KAD\<close>

definition rel_ad :: "'a rel \<Rightarrow> 'a rel" ("ad\<^sub>r") where
  "rel_ad R = {(x,x) | x. \<not>(\<exists>y. (x,y) \<in> R)}" 

interpretation rel_aka: antidomain_kleene_algebra "(\<union>)" "{}" Id "(;)" "(\<subseteq>)" "(\<subset>)" rtrancl "ad\<^sub>r"
  by unfold_locales (auto simp: rel_ad_def)

definition sta_ad :: "'a sta \<Rightarrow> 'a sta" ("ad\<^sub>s")where
  "sta_ad f x = (if f x = {} then {x} else {})"

interpretation sta_aka: antidomain_kleene_algebra "(+\<^sub>K)" "\<nu>" "\<eta>" "(\<circ>\<^sub>K)" "(\<sqsubseteq>)" "(\<sqsubset>)" kstar "ad\<^sub>s"
  apply (unfold_locales, unfold sta_iff sta_ad_def kcomp_iff kleq_iff kadd_iff)
  by clarsimp+ (auto simp: kcomp_def)

lemma rel_d_fix_subid: "(rel_aka.dom_op R = R) = (R \<subseteq> Id)" 
  unfolding rel_aka.dom_op_def rel_ad_def Id_def by force

lemma sta_d_fix_subid: "(sta_aka.dom_op f = f) = (f \<sqsubseteq> \<eta>)"
  unfolding sta_iff sta_aka.dom_op_def sta_ad_def kleq_iff by force


subsection \<open>Optimised Laws for VCG\<close>

abbreviation rcond :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("rif _ then _ else _ fi" [64,64,64] 63) where
  "rif P then R else S fi \<equiv> rel_aka.cond \<lceil>P\<rceil>\<^sub>r R S"

abbreviation rwhile :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("rwhile _ do _ od" [64,64] 63) where
  "rwhile P do R od \<equiv> rel_aka.while \<lceil>P\<rceil>\<^sub>r R"

abbreviation rwhile_inv :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("rwhile _ inv _ do _ od" [64,64,64] 63) where
  "rwhile P inv I do R od \<equiv> rel_aka.while_inv \<lceil>P\<rceil>\<^sub>r \<lceil>I\<rceil>\<^sub>r R"

abbreviation scond :: "'a pred \<Rightarrow> 'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" ("sif _ then _ else _ fi" [64,64,64] 63) where
  "sif P then f else g fi \<equiv> sta_aka.cond \<lceil>P\<rceil>\<^sub>s f g"

abbreviation swhile :: "'a pred \<Rightarrow> 'a sta \<Rightarrow> 'a sta" ("swhile _ do _ od" [64,64] 63) where
  "swhile P do f od \<equiv> sta_aka.while \<lceil>P\<rceil>\<^sub>s f"

abbreviation swhile_inv :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a sta \<Rightarrow> 'a sta" ("swhile _ inv _ do _ od" [64,64,64] 63) where
  "swhile P inv I do f od \<equiv> sta_aka.while_inv \<lceil>P\<rceil>\<^sub>s \<lceil>I\<rceil>\<^sub>s f"

lemma rel_fbox_subid: "rel_aka.fbox R P \<subseteq> Id"
  using rel_aka.fbox_anti by force

lemma sta_fbox_subid: "sta_aka.fbox f P \<sqsubseteq> \<eta>"
  by (simp add: kleq_iff sta_ad_def sta_aka.fbox_fdia)

lemma rel_dom_pred [simp]: "rel_aka.dom_op \<lceil>P\<rceil>\<^sub>r = \<lceil>P\<rceil>\<^sub>r"
  unfolding p2r_def rel_aka.dom_op_def rel_ad_def by simp

lemma rel_ad_pred [simp]: "ad\<^sub>r \<lceil>P\<rceil>\<^sub>r = \<lceil>\<lambda>s. \<not> P s\<rceil>\<^sub>r"
  unfolding p2r_def rel_ad_def by simp

lemma sta_dom_pred [simp]: "sta_aka.dom_op \<lceil>P\<rceil>\<^sub>s = \<lceil>P\<rceil>\<^sub>s"
  unfolding p2s_def sta_aka.dom_op_def sta_ad_def sta_iff by simp

lemma sta_ad_pred [simp]: "ad\<^sub>s \<lceil>P\<rceil>\<^sub>s = \<lceil>\<lambda>s. \<not> P s\<rceil>\<^sub>s"
  unfolding p2s_def sta_ad_def sta_iff by simp

abbreviation "rfbox R Q \<equiv> \<lfloor>rel_aka.fbox R \<lceil>Q\<rceil>\<^sub>r\<rfloor>\<^sub>r"

abbreviation "sfbox R Q \<equiv> \<lfloor>sta_aka.fbox R \<lceil>Q\<rceil>\<^sub>s\<rfloor>\<^sub>s"

lemma rfbox_p2r2p: "rel_aka.fbox R \<lceil>P\<rceil>\<^sub>r = \<lceil>rfbox R P\<rceil>\<^sub>r"
  by (simp add: p2r2p rel_fbox_subid)

lemma sfbox_p2s2p: "sta_aka.fbox R \<lceil>P\<rceil>\<^sub>s = \<lceil>sfbox R P\<rceil>\<^sub>s"
  by (simp add: p2s2p sta_fbox_subid)

lemma rfbox_unfold: "rfbox R P s = (\<forall>s'. (s,s') \<in> R \<longrightarrow> P s')"
  unfolding p2r_def r2p_def rel_aka.fbox_def rel_ad_def by force

lemma sfbox_unfold: "sfbox f P s = (\<forall>s'. s' \<in> f s \<longrightarrow> P s')"
  unfolding p2s_def s2p_def sta_aka.fbox_def sta_ad_def kcomp_def by force

lemma rfbox_seq [simp]: "rfbox (R ; S) P s = rfbox R (rfbox S P) s"
  by (metis rel_aka.fbox_comp rfbox_p2r2p)

lemma rfbox_seq_var: 
  assumes "\<forall>s. w s \<longrightarrow> rfbox y z s"
   and "\<forall>s. v s \<longrightarrow> rfbox x w s"
  shows "\<forall>s. v s \<longrightarrow> rfbox (x ; y) z s"
  by (metis assms rfbox_seq rfbox_unfold)

lemma sfbox_seq [simp]: "sfbox (f \<circ>\<^sub>K g) P s = sfbox f (sfbox g P) s"
  by (metis sfbox_p2s2p sta_aka.fbox_comp)

lemma sfbox_seq_var: 
  assumes "\<forall>s. w s \<longrightarrow> sfbox y z s" 
  and "\<forall>s. v s \<longrightarrow> sfbox x w s" 
  shows "\<forall>s. v s \<longrightarrow> sfbox (x \<circ>\<^sub>K y) z s"
  by (metis assms sfbox_seq sfbox_unfold)

lemma rfbox_cond [simp]: "rfbox (rif P then R else S fi) Q s = ((P s \<longrightarrow> rfbox R Q s) \<and> (\<not> P s \<longrightarrow> rfbox S Q s))"
  by (unfold rfbox_unfold rel_aka.cond_def relcomp_unfold, simp, unfold p2r_def, force)

lemma rfbox_cond_var: "rfbox (rif P then R else S fi) Q s = ((P s \<and> rfbox R Q s) \<or>  (\<not> P s \<and> rfbox S Q s))"
  by (metis (no_types, hide_lams) rfbox_cond)

lemma sfbox_cond [simp]: "sfbox (sif P then f else g fi) Q s = ((P s \<longrightarrow> sfbox f Q s) \<and> (\<not> P s \<longrightarrow> sfbox g Q s))"
  by (unfold sfbox_unfold sta_aka.cond_def sta_iff kadd_def kcomp_iff, simp, unfold p2s_def kcomp_iff, force)

lemma sfbox_cond_var: "sfbox (sif P then f else g fi) Q s = ((P s \<and> sfbox f Q s) \<or>  (\<not> P s \<and> sfbox g Q s))"
  unfolding sfbox_cond fun_eq_iff by force

lemma rfbox_while_inv: 
  assumes "\<forall>s. P s \<longrightarrow> I s"
  and "\<forall>s. I s \<longrightarrow> \<not> T s \<longrightarrow> Q s"
  and "\<forall>s. I s \<longrightarrow> T s \<longrightarrow> rfbox R I s"
  shows "\<forall>s. P s \<longrightarrow> rfbox (rwhile T inv I do R od) Q s" 
proof-
  have a: "\<lceil>P\<rceil>\<^sub>r \<subseteq> \<lceil>I\<rceil>\<^sub>r"
    using assms by simp
  have b: "\<lceil>I\<rceil>\<^sub>r ; ad\<^sub>r \<lceil>T\<rceil>\<^sub>r \<subseteq> \<lceil>Q\<rceil>\<^sub>r"
    by (simp add: assms(2))
  have c: "\<lceil>I\<rceil>\<^sub>r ; \<lceil>T\<rceil>\<^sub>r \<subseteq> rel_aka.fbox R \<lceil>I\<rceil>\<^sub>r"
    by (smt assms(3) p2r_comp p2r_imp rfbox_p2r2p)
  hence "rel_aka.dom_op \<lceil>P\<rceil>\<^sub>r \<subseteq> rel_aka.fbox (rel_aka.while_inv \<lceil>T\<rceil>\<^sub>r \<lceil>I\<rceil>\<^sub>r R) \<lceil>Q\<rceil>\<^sub>r"
    apply (intro rel_aka.fbox_while_inv)
    using a b by simp_all
  thus ?thesis
    by (smt p2r_imp rel_dom_pred rfbox_p2r2p)
qed

lemma sfbox_while_inv: 
  assumes "\<forall>s. P s \<longrightarrow> I s"
  and "\<forall>s. I s \<longrightarrow> \<not> T s \<longrightarrow> Q s"
  and "\<forall>s. I s \<longrightarrow> T s \<longrightarrow> sfbox f I s"
  shows "\<forall>s. P s \<longrightarrow> sfbox (swhile T inv I do f od) Q s" 
proof-
  have a: "\<lceil>P\<rceil>\<^sub>s \<sqsubseteq> \<lceil>I\<rceil>\<^sub>s"
    using assms by simp
  have b: "\<lceil>I\<rceil>\<^sub>s \<circ>\<^sub>K ad\<^sub>s \<lceil>T\<rceil>\<^sub>s \<sqsubseteq> \<lceil>Q\<rceil>\<^sub>s"
    by (simp add: assms(2))
  have c: "\<lceil>I\<rceil>\<^sub>s \<circ>\<^sub>K \<lceil>T\<rceil>\<^sub>s \<sqsubseteq> sta_aka.fbox f \<lceil>I\<rceil>\<^sub>s"
    by (smt assms(3) p2s_comp p2s_imp sfbox_p2s2p)
  hence "sta_aka.dom_op \<lceil>P\<rceil>\<^sub>s \<sqsubseteq> sta_aka.fbox (sta_aka.while_inv \<lceil>T\<rceil>\<^sub>s \<lceil>I\<rceil>\<^sub>s f) \<lceil>Q\<rceil>\<^sub>s"
    apply (intro sta_aka.fbox_while_inv)
    using a b by simp_all
  thus ?thesis
     by (smt p2s_imp sta_dom_pred sfbox_p2s2p)
 qed

lemma rfbox_while_inv_break: 
  assumes "\<forall>s. P s \<longrightarrow> rfbox S I s"
  and "\<forall>s. I s \<longrightarrow> \<not> T s \<longrightarrow> Q s"
  and "\<forall>s. I s \<longrightarrow>  T s \<longrightarrow> rfbox R I s"
  shows "\<forall>s. P s \<longrightarrow> rfbox (S ; (rwhile T inv I do R od)) Q s"
  apply (intro rfbox_seq_var rfbox_while_inv) 
  using assms by simp_all

lemma sfbox_while_inv_break: 
  assumes "\<forall>s. P s \<longrightarrow> sfbox g I s"
  and "\<forall>s. I s \<longrightarrow> \<not> T s \<longrightarrow> Q s"
  and "\<forall>s. I s \<longrightarrow>  T s \<longrightarrow> sfbox f I s"
  shows "\<forall>s. P s \<longrightarrow> sfbox (g \<circ>\<^sub>K (swhile T inv I do f od)) Q s"
  apply (intro sfbox_seq_var sfbox_while_inv)
  using assms by simp_all


subsection \<open>Store and Assignment Semantics\<close>

text \<open>We reuse the store from KAT\<close>

lemma mka_rel_assign [simp]: "rel_aka.fbox (v :=\<^sub>r e) \<lceil>Q\<rceil>\<^sub>r = \<lceil>\<lambda>s. Q (set v e s)\<rceil>\<^sub>r"
  by (auto simp: rel_aka.fbox_def rel_assign_def rel_ad_def p2r_def)

lemma mka_sta_assign [simp]: "sta_aka.fbox (v :=\<^sub>s e) \<lceil>Q\<rceil>\<^sub>s = \<lceil>\<lambda>s. Q (set v e s)\<rceil>\<^sub>s"
  by (auto simp: sta_iff sta_aka.fbox_def sta_assign_def kcomp_def sta_ad_def p2s_def)

lemma rfbox_assign [simp]: "rfbox (v :=\<^sub>r e) Q s = Q (set v e s)"
  by simp

lemma sfbox_assign [simp]: "sfbox (v :=\<^sub>s e) Q s = Q (set v e s)"
  by simp


subsection \<open>Examples\<close>

lemma svar_swap:
  "s ''x'' = m \<and> s ''y'' = n \<Longrightarrow>  
    sfbox ((''z'' :=\<^sub>s (\<lambda>s. s ''x''))\<circ>\<^sub>K
    (''x'' :=\<^sub>s (\<lambda>s. s ''y''))\<circ>\<^sub>K
    (''y'' :=\<^sub>s (\<lambda>s. s ''z'')))
   (\<lambda>s. s ''x'' = n \<and> s ''y'' = m) s"
  by simp

lemma rvar_swap: 
  "s ''x'' = m \<and> s ''y'' = n \<Longrightarrow> 
    rfbox ((''z'' :=\<^sub>r (\<lambda>s. s ''x''));
    (''x'' :=\<^sub>r (\<lambda>s. s ''y''));
    (''y'' :=\<^sub>r (\<lambda>s. s ''z'')))
   (\<lambda>s. s ''x'' = n \<and> s ''y'' = m) s"
  by simp

lemma rmaximum:  
  "\<forall>s::int store. 
   rfbox (rif (\<lambda>s. s ''x'' \<ge> s ''y'') 
    then (''z'' :=\<^sub>r (\<lambda>s. s ''x''))
    else (''z'' :=\<^sub>r (\<lambda>s. s ''y''))
    fi)
   (\<lambda>s. s ''z'' = max (s ''x'') (s ''y'')) s"
  by force

lemma smaximum:  
  "\<forall>s::int store. 
   sfbox (sif (\<lambda>s. s ''x'' \<ge> s ''y'') 
    then (''z'' :=\<^sub>s (\<lambda>s. s ''x''))
    else (''z'' :=\<^sub>s (\<lambda>s. s ''y''))
    fi)
   (\<lambda>s. s ''z'' = max (s ''x'') (s ''y'')) s"
  by force

lemma rinteger_division: 
"\<forall>s::nat store. 0 < y \<longrightarrow>
    rfbox ((''q'' :=\<^sub>r (\<lambda>s. 0)); 
    (''r'' :=\<^sub>r (\<lambda>s. x));
    (rwhile (\<lambda>s. y \<le> s ''r'') inv (\<lambda>s. x = s ''q'' * y + s ''r'')
     do
      (''q'' :=\<^sub>r (\<lambda>s. s ''q'' + 1)) ;
      (''r'' :=\<^sub>r (\<lambda>s. s ''r'' - y))
     od))
  (\<lambda>s. x = s ''q'' * y + s ''r'' \<and> s ''r'' < y) s"
  by (intro rfbox_seq_var rfbox_while_inv, auto simp: imp_refl)
(*  by (rule rfbox_while_inv_break) simp_all*)

lemma sinteger_division: 
"\<forall>s::nat store. 0 < y \<longrightarrow>
    sfbox ((''q'' :=\<^sub>s (\<lambda>s. 0)) \<circ>\<^sub>K
    (''r'' :=\<^sub>s (\<lambda>s. x))  \<circ>\<^sub>K
    (swhile (\<lambda>s. y \<le> s ''r'') inv (\<lambda>s. x = s ''q'' * y + s ''r'')
     do
      (''q'' :=\<^sub>s (\<lambda>s. s ''q'' + 1)) \<circ>\<^sub>K
      (''r'' :=\<^sub>s (\<lambda>s. s ''r'' - y))
     od))
  (\<lambda>s. x = s ''q'' * y + s ''r'' \<and> s ''r'' < y) s"
  by (rule sfbox_while_inv_break) simp_all

end




