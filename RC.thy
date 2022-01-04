(* Title: Refinement KAT
   Author: Peixin You
*)

section \<open>Refinement KAT\<close>

theory RC
  imports HL

begin

subsection \<open>Order Preservation of Conditionals and Loops\<close>

context kat
begin

lemma cond_iso: 
  assumes "x \<le> x'"
  and "y \<le> y'"
shows "if p then x else y fi \<le> if p then x' else y' fi"
  by (simp add: assms add_iso cond_def mult_isol)
                                     
lemma while_iso: 
  assumes "x \<le> y"
  shows "while p do x od \<le> while p do y od"
  by (simp add: assms mult_isol mult_isor star_iso while_def)

end

subsection \<open>Definition of refinement KAT\<close>

text \<open>A refinement KAT is a KAT expanded by Morgan's specification statement.\<close>

class rkat = kat +
  fixes Re :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes spec_def:  "(x \<le> Re p q) = Ho p x q"

begin

lemma R1: "Ho p (Re p q) q"
  using spec_def by blast

lemma R2: "Ho p x q \<Longrightarrow> x \<le> Re p q"
  by (simp add: spec_def)

lemma R_demmod: "(x \<le> Re p q) = (\<tau> p \<cdot> x \<le> x \<cdot> \<tau> q)"
  by (simp add: Ho_def spec_def) 


subsection \<open>Propositional Refinement Calculus\<close>

lemma R_skip: "1 \<le> Re p p"
proof -
  have "Ho p 1 p"
    by (simp add: H_skip)
  thus ?thesis
    by (rule R2)
qed

lemma R_cons: 
  assumes "\<tau> p \<le> \<tau> p'"
  and "\<tau> q' \<le> \<tau> q"
  shows "Re p' q' \<le> Re p q"
proof -
  have "Ho p' (Re p' q') q'"
    by (simp add: R1)
  hence "Ho p (Re p' q') q"
    using assms H_cons by simp
  thus ?thesis
    by (rule R2)
qed

lemma R_seq: "Re p r \<cdot> Re r q \<le> Re p q"
proof -
  have "Ho p (Re p r) r" and "Ho r (Re r q) q"
    by (simp add: R1)+
  hence "Ho p ((Re p r) \<cdot> (Re r q)) q"
    using H_seq by auto
  thus ?thesis
    by (rule R2)
qed

lemma R_cond: "if v then Re (\<tau> p \<cdot> \<tau> v) q else Re (\<tau> p \<cdot> \<alpha> v) q fi \<le> Re p q"
proof - 
  have "Ho (\<tau> p \<cdot> \<tau> v) (Re (\<tau> p \<cdot> \<tau> v) q) q" and "Ho (\<tau> p \<cdot> \<alpha> v) (Re (\<tau> p \<cdot> \<alpha> v) q) q"
    by (simp add: R1)+
  hence "Ho p (if v then (Re (\<tau> p \<cdot> \<tau> v) q) else (Re (\<tau> p \<cdot> \<alpha> v) q) fi) q"
    by (simp add: H_cond_iff)
 thus ?thesis
    by (rule R2)
qed

lemma R_while: "while q do Re (\<tau> p \<cdot> \<tau> q) p od \<le> Re p (\<tau> p \<cdot> \<alpha> q)"  
proof -
  have "Ho (\<tau> p \<cdot> \<tau> q) (Re (\<tau> p \<cdot> \<tau> q) p)  p" 
    by (simp_all add: R1)
  hence "Ho p (while q do (Re (\<tau> p \<cdot> \<tau> q) p) od) (\<tau> p \<cdot> \<alpha> q)"
    by (simp add: H_while)
  thus ?thesis
    by (rule R2)
  qed

lemma R_zero_one: "x \<le> Re 0 1"
proof -
  have "Ho 0 x 1"
    by (metis Ho_def annil mult_1_right test_def test_mult_comp test_one zero_least)
  thus ?thesis
    by (rule R2)
qed

lemma R_one_zero: "Re 1 0 = 0"
proof -
  have "Ho 1 (Re 1 0) 0"
    by (simp add: R1)
  thus ?thesis
    by (metis Ho_def mult_1_left mult_1_right pcorrect_if1 t_a_var test_mult_comp test_one)
qed

lemma R_while_inv: "\<tau> p \<le> \<tau> i \<Longrightarrow>  \<alpha> t \<cdot> \<tau> i \<le> \<tau> q \<Longrightarrow> while t do Re (\<tau> t \<cdot> \<tau> i) i od \<le> Re p q"
  using R1 H_while_inv a_comm spec_def test_def while_inv_def by simp

end


subsection \<open>Models of Refinement KAT\<close>

definition rel_Re :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where 
  "rel_Re P Q = \<Union>{R. rel_kat.Ho P R Q}"

interpretation rel_rkat: rkat "(\<union>)" "{}" Id "(;)" "(\<subseteq>)" "(\<subset>)" rtrancl "\<alpha>\<^sub>r" rel_Re
  by (standard, auto simp: rel_Re_def rel_kat.Ho_def rel_atest_def rel_kat.test_def)

definition sta_Re :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" where 
  "(sta_Re P Q) x = \<Union>{f x|f. sta_kat.Ho P f Q}"

interpretation sta_rkat: rkat "(+\<^sub>K)" "\<nu>" "\<eta>" "(\<circ>\<^sub>K)" "(\<sqsubseteq>)" "(\<sqsubset>)" kstar "\<alpha>\<^sub>s" sta_Re
  by (standard, unfold sta_Re_def sta_kat.Ho_def sta_kat.test_def sta_atest_def kcomp_iff kleq_iff) auto


subsection \<open>Specialised Refinement Laws\<close>

text \<open>First we consider the relational model.\<close>

abbreviation rR :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("R\<^sub>r") where
   "R\<^sub>r P Q \<equiv> rel_Re \<lceil>P\<rceil>\<^sub>r \<lceil>Q\<rceil>\<^sub>r"

lemma rR_unfold: "R\<^sub>r P Q = \<Union>{R. \<forall>x y. P x \<longrightarrow> (x,y) \<in> R \<longrightarrow> Q y}"
  unfolding rel_Re_def rH_unfold by simp

lemma rR_cons1: 
  assumes "\<forall>s. P s \<longrightarrow> P' s"
  shows "R\<^sub>r P' Q \<subseteq> R\<^sub>r P Q"
  unfolding rR_unfold 
  apply (intro Sup_subset_mono)
  using assms by force

lemma rR_cons2: 
  assumes "\<forall>s. Q' s \<longrightarrow> Q s" 
  shows "R\<^sub>r P Q' \<subseteq> R\<^sub>r P Q"
  unfolding rR_unfold 
  apply (intro Sup_subset_mono)
  using assms by force

lemma rR_cons: 
  assumes "\<forall>s. P s \<longrightarrow> P' s"
  and "\<forall>s. Q' s \<longrightarrow> Q s" 
  shows "R\<^sub>r P' Q' \<subseteq> R\<^sub>r P Q"
  unfolding rR_unfold 
  apply (intro Sup_subset_mono)
  using assms by force

lemma rR_skip [simp]: "(Id \<subseteq> R\<^sub>r P Q) = (\<forall>s. P s \<longrightarrow> Q s)"
  apply (simp add: rR_unfold) by force

lemma rR_cond: "rif T then R\<^sub>r (\<lambda>s. P s \<and> T s) Q else R\<^sub>r (\<lambda>s. P s \<and> \<not>T s) Q fi \<subseteq> R\<^sub>r P Q"
  by (simp add: rel_rkat.R1 rel_rkat.R2)

lemma rR_cond_var: 
  assumes "R \<subseteq> R\<^sub>r (\<lambda>s. P s \<and> T s) Q"
  and "S \<subseteq> R\<^sub>r (\<lambda>s. P s \<and> \<not>T s) Q"
  shows "rif T then R else S fi \<subseteq> R\<^sub>r P Q"
  using assms rH_cond rel_rkat.spec_def by blast

lemma rR_while: "rwhile Q do R\<^sub>r (\<lambda>s. P s \<and> Q s) P od \<subseteq> R\<^sub>r P (\<lambda>s. P s \<and> \<not> Q s)"
  by (simp add: rH_while rel_rkat.R1 rel_rkat.R2)

lemma rR_while_var: 
  assumes "R \<subseteq> R\<^sub>r (\<lambda>s. P s \<and> Q s) P"
  shows "rwhile Q do R od \<subseteq> R\<^sub>r P (\<lambda>s. P s \<and> \<not> Q s)"
  using assms rH_while rel_rkat.spec_def by blast

text \<open>Next we consider the state transformer model.\<close>

abbreviation sR :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a sta" ("R\<^sub>s") where
   "R\<^sub>s P Q \<equiv> sta_Re \<lceil>P\<rceil>\<^sub>s \<lceil>Q\<rceil>\<^sub>s"

lemma sR_unfold: "(R\<^sub>s P Q) x = \<Union>{f x |f.  \<forall>y z. P y \<longrightarrow> z \<in> f y \<longrightarrow> Q z}"
  unfolding sta_Re_def sH_unfold by simp

lemma sR_cons1: 
  assumes "\<forall>s. P s \<longrightarrow> P' s"
  shows "R\<^sub>s P' Q \<sqsubseteq> R\<^sub>s P Q"
  unfolding sR_unfold kleq_def
  apply clarsimp
  using assms by auto

lemma sR_cons2: 
  assumes "\<forall>s. Q' s \<longrightarrow> Q s" 
  shows "R\<^sub>s P Q' \<sqsubseteq> R\<^sub>s P Q"
  unfolding sR_unfold kleq_def
  apply clarsimp
  using assms by blast 

lemma sR_cons: 
  assumes "\<forall>s. P s \<longrightarrow> P' s"
  and "\<forall>s. Q' s \<longrightarrow> Q s" 
  shows "R\<^sub>s P' Q' \<sqsubseteq> R\<^sub>s P Q"
  unfolding sR_unfold kleq_def
  apply clarsimp
  using assms by blast 

lemma scond_iso: 
  assumes "f \<sqsubseteq> f'"
  and "g \<sqsubseteq> g'" 
  shows "sif P then f else g fi \<sqsubseteq> sif P then f' else g' fi"
  by (simp add: assms sta_kat.cond_iso)
                                   
lemma swhile_iso: 
  assumes "f \<sqsubseteq> f'"
  shows "swhile P do f od \<sqsubseteq> swhile P do f' od"
  by (simp add: assms sta_kat.while_iso)

lemma sR_skip: "\<eta> \<sqsubseteq> R\<^sub>s P Q = (\<forall>s. P s \<longrightarrow> Q s)"
  by (simp add: sH_skip sta_rkat.spec_def)

lemma sR_cond: "sif T then R\<^sub>s (\<lambda>s. P s \<and> T s) Q else R\<^sub>s (\<lambda>s. P s \<and> \<not>T s) Q fi \<sqsubseteq> R\<^sub>s P Q"
  by (simp add: sta_rkat.R1 sta_rkat.R2)

lemma sR_cond_var: 
  assumes "f \<sqsubseteq> R\<^sub>s (\<lambda>s. P s \<and> T s) Q"
  and "g \<sqsubseteq> R\<^sub>s (\<lambda>s. P s \<and> \<not>T s) Q"
shows "sif T then f else g fi \<sqsubseteq> R\<^sub>s P Q"
  using assms sH_cond sta_rkat.spec_def by blast

lemma sR_while: "swhile Q do R\<^sub>s (\<lambda>s. P s \<and> Q s) P od \<sqsubseteq> R\<^sub>s P (\<lambda>s. P s \<and> \<not> Q s)"
  by (simp add: sH_while sta_rkat.R1 sta_rkat.spec_def)

lemma sR_while_var: 
  assumes "f \<sqsubseteq> R\<^sub>s (\<lambda>s. P s \<and> Q s) P"
  shows "swhile Q do f od \<sqsubseteq> R\<^sub>s P (\<lambda>s. P s \<and> \<not> Q s)"
  using assms sR_while sta_di.dual_order.trans swhile_iso by blast


subsection \<open>Assignment Laws\<close>

text \<open>The store model is from KAT\<close>

lemma rR_assign [simp]: "((v :=\<^sub>r e) \<subseteq> R\<^sub>r P Q) = (\<forall>s. P s \<longrightarrow> Q (set v e s))"
  by (simp add: rel_rkat.spec_def)

lemma rR_assignl: 
  assumes "\<forall>s. P s \<longrightarrow> P' (set v e s)"
  shows "(v :=\<^sub>r e) ; (R\<^sub>r P' Q) \<subseteq> R\<^sub>r P Q"
proof -
    have "v :=\<^sub>r e \<subseteq> R\<^sub>r P P'"
    using assms by simp
  then show ?thesis
    by (meson order.trans rel_d.mult_isor rel_rkat.R_seq)
qed

lemma rR_assignr: 
  assumes "\<forall>s. Q' s \<longrightarrow> Q (set v e s)"
  shows "(R\<^sub>r P Q') ; (v :=\<^sub>r e) \<subseteq> R\<^sub>r P Q"
proof -
 have "v :=\<^sub>r e \<subseteq> R\<^sub>r Q' Q"
    using assms by simp
  then show ?thesis
    by (meson rel_d.mult_isol rel_rkat.R_seq subset_trans)
qed

lemma sR_assign [simp]: "(\<forall>s. P s \<longrightarrow> Q (set v e s)) = ((v :=\<^sub>s e) \<sqsubseteq> R\<^sub>s P Q)"
  by (simp add: sta_rkat.spec_def)

lemma sR_assignr: 
  assumes "\<forall>s. Q' s \<longrightarrow> Q (set v e s)"
  shows "(R\<^sub>s P Q') \<circ>\<^sub>K (v :=\<^sub>s e) \<sqsubseteq> R\<^sub>s P Q"
proof -
   have "v :=\<^sub>s e \<sqsubseteq> R\<^sub>s Q' Q"
    using assms by simp
  then show ?thesis
    using sta_kat.H_seq sta_rkat.spec_def by blast
qed

lemma sR_assignl: 
  assumes "\<forall>s. P s \<longrightarrow> P' (set v e s)"
  shows "(v :=\<^sub>s e) \<circ>\<^sub>K (R\<^sub>s P' Q) \<sqsubseteq> R\<^sub>s P Q"
proof -
   have "v :=\<^sub>s e \<sqsubseteq> R\<^sub>s P P'"
    using assms by simp
  then show ?thesis
    using sta_kat.H_seq sta_rkat.spec_def by blast
qed


subsection \<open>Refinement Examples\<close>

text \<open>Variable Swap\<close>

lemma var_swap_ref1: 
  "R\<^sub>r (\<lambda>s. s ''x'' = a \<and> s ''y'' = b) (\<lambda>s. s ''x'' = b \<and> s ''y'' = a)
   \<supseteq> (''z'' :=\<^sub>r (\<lambda>s. s ''x'')); R\<^sub>r (\<lambda>s. s ''z'' = a \<and> s ''y'' = b) (\<lambda>s. s ''x'' = b \<and> s ''y'' = a)"
  by (rule rR_assignl) simp 

lemma var_swap_ref2: 
  "R\<^sub>r (\<lambda>s. s ''z'' = a \<and> s ''y'' = b) (\<lambda>s. s ''x'' = b \<and> s ''y'' = a)
   \<supseteq> (''x'' :=\<^sub>r (\<lambda>s. s ''y'')); R\<^sub>r (\<lambda>s. s ''z'' = a \<and> s ''x'' = b) (\<lambda>s. s ''x'' = b \<and> s ''y'' = a)"
  by (rule rR_assignl) simp

lemma var_swap_ref3:  
  "R\<^sub>r (\<lambda>s. s ''z'' = a \<and> s ''x'' = b) (\<lambda>s. s ''x'' = b \<and> s ''y'' = a)
   \<supseteq> (''y'' :=\<^sub>r (\<lambda>s. s ''z'')); R\<^sub>r (\<lambda>s. s ''x'' = b \<and> s ''y'' = a) (\<lambda>s. s ''x'' = b \<and> s ''y'' = a)" 
  by (rule rR_assignl) simp

lemma var_swap_ref: 
  "R\<^sub>r (\<lambda>s. s ''x'' = a \<and> s ''y'' = b) (\<lambda>s. s ''x'' = b \<and> s ''y'' = a)
   \<supseteq> (''z'' :=\<^sub>r (\<lambda>s. s ''x'')) ; (''x'' :=\<^sub>r (\<lambda>s. s ''y'')) ; (''y'' :=\<^sub>r (\<lambda>s. s ''z''))"
  by (simp add: rel_rkat.R2 rvarible_swap)


text \<open>Maximum\<close>

lemma max1: 
  "R\<^sub>r (\<lambda>s::int store. s ''x'' \<ge> s ''y'') (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))
   \<supseteq> R\<^sub>r (\<lambda>s. s ''x'' \<ge> s ''y'') (\<lambda>s. s ''y'' \<le> s ''x'') ; (''z'' :=\<^sub>r (\<lambda>s. s ''x''))"
  by (smt fun_update_simp1 fun_update_simp2 rR_assignr) 

lemma max11: 
  "R\<^sub>r (\<lambda>s. s ''x'' \<ge> s ''y'') (\<lambda>s. s ''y'' \<le> s ''x'') ; (''z'' :=\<^sub>r (\<lambda>s. s ''x''))
  \<supseteq> ''z'' :=\<^sub>r (\<lambda>s. s ''x'')"
  using rel_rkat.R_skip by fastforce

lemma max2: 
  "R\<^sub>r (\<lambda>s::int store. s ''x'' < s ''y'') (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))
   \<supseteq> R\<^sub>r (\<lambda>s. s ''x'' < s ''y'') (\<lambda>s. s ''x'' < s ''y'') ; (''z'' :=\<^sub>r (\<lambda>s. s ''y''))"
  by (smt fun_update_simp1 fun_update_simp2 rR_assignr)

lemma max21: 
  "R\<^sub>r (\<lambda>s. s ''x'' < s ''y'') (\<lambda>s. s ''x'' < s ''y'') ; (''z'' :=\<^sub>r (\<lambda>s. s ''y''))
  \<supseteq> ''z'' :=\<^sub>r (\<lambda>s. s ''y'')"
  using rel_rkat.R_skip by fastforce

lemma max_cond: 
"R\<^sub>r (\<lambda>s::int store. True) (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))
\<supseteq> rif (\<lambda>s. s ''x'' \<ge> s ''y'')
     then (R\<^sub>r (\<lambda>s. s ''x'' \<ge> s ''y'') (\<lambda>s. s ''z'' = max (s ''x'') (s ''y'')))
     else (R\<^sub>r (\<lambda>s. s ''x'' < s ''y'') (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))) 
   fi"
  by (simp add: rR_cond_var rR_cons)

lemma maximum:
   "R\<^sub>r (\<lambda>s::int store. True) (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))
   \<supseteq> (rif (\<lambda>s. s ''x'' \<ge> s ''y'') 
         then (''z'' :=\<^sub>r (\<lambda>s. s ''x''))
         else (''z'' :=\<^sub>r (\<lambda>s. s ''y''))
       fi)"
  using rel_rkat.R2 rmaximum by blast


text \<open>Integer Division\<close>

abbreviation "Idiv s \<equiv> s ''x'' = s ''q'' * s ''y'' + s ''r''"

abbreviation "Tdiv s \<equiv> s ''y'' \<le> s ''r''"

lemma div_init1: "R\<^sub>r (\<lambda>s::nat store. 0 < s ''y'') (\<lambda>s. Idiv s  \<and> \<not>Tdiv s) \<supseteq> 
  (''r'' :=\<^sub>r (\<lambda>s. s ''x'')); 
  R\<^sub>r (\<lambda>s. s ''r'' = s ''x'' \<and> s ''x'' \<ge> 0) (\<lambda>s. Idiv s \<and> \<not>Tdiv s)"
  by (rule rR_assignl) simp

lemma div_init2: "R\<^sub>r (\<lambda>s::nat store. s ''r'' = s ''x'') (\<lambda>s. Idiv s \<and> \<not> Tdiv s) \<supseteq> 
  (''q'' :=\<^sub>r (\<lambda>s. 0)); 
  R\<^sub>r (\<lambda>s. s ''r'' = s ''x'' \<and> s ''q'' = 0) (\<lambda>s. Idiv s \<and> \<not> Tdiv s)"
  by (rule rR_assignl) simp

lemma div_init3: 
  "R\<^sub>r (\<lambda>s::nat store. s ''r'' = s ''x'' \<and> s ''q'' = 0) (\<lambda>s. Idiv s \<and> \<not> Tdiv s) \<supseteq> 
  R\<^sub>r Idiv (\<lambda>s. Idiv s \<and> \<not> Tdiv s)" 
  by (simp_all add: rR_cons)

lemma div_loop: "R\<^sub>r Idiv (\<lambda>s. Idiv s \<and> \<not> Tdiv s) \<supseteq> 
  rwhile Tdiv do (R\<^sub>r (\<lambda>s. Idiv s \<and> Tdiv s) Idiv) od"
  by (simp add: rR_while)

lemma div_body1: "R\<^sub>r (\<lambda>s. Idiv s \<and> Tdiv s) Idiv \<supseteq> 
  R\<^sub>r (\<lambda>s. Idiv s \<and> Tdiv s) (\<lambda>s::nat store. s ''x'' = s ''q'' * s ''y'' + (s ''r'' - s ''y'')) ; 
  (''r'' :=\<^sub>r (\<lambda>s. s ''r'' - s ''y''))"
  by (simp add: rR_assignr) 

lemma div_body2: 
  "R\<^sub>r (\<lambda>s. Idiv s \<and> Tdiv s) (\<lambda>s::nat store. s ''x'' = s ''q'' * s ''y'' + (s ''r'' - s ''y'')) \<supseteq> 
  R\<^sub>r (\<lambda>s. Idiv s \<and> Tdiv s) (\<lambda>s. Idiv s \<and>  Tdiv s) ; (''q'' :=\<^sub>r (\<lambda>s. s ''q'' + 1))"
  by  (simp add: rR_assignr)

lemma div_while: "rwhile Tdiv do R\<^sub>r (\<lambda>s. Idiv s \<and> Tdiv s) Idiv od \<supseteq> 
  rwhile Tdiv do
    (''q'' :=\<^sub>r (\<lambda>f. f ''q'' + (1::nat))); 
    (''r'' :=\<^sub>r (\<lambda>f. f ''r'' - f ''y'')) 
  od"
  apply (rule rel_kat.while_iso)
  using div_body1 div_body2 rel_rkat.R_skip by blast

lemma integer_division: "R\<^sub>r (\<lambda>s::nat store. 0 < s ''y'') (\<lambda>s. Idiv s \<and> \<not> Tdiv s) \<supseteq>  
  (''r'' :=\<^sub>r (\<lambda>s. s ''x'')); 
  (''q'' :=\<^sub>r (\<lambda>s. 0));
  (rwhile Tdiv do
      (''q'' :=\<^sub>r (\<lambda>s::nat store. s ''q'' + 1)); 
      (''r'' :=\<^sub>r (\<lambda>s. s ''r'' - s ''y''))
  od)"
  using div_init1 div_init2 div_init3 div_loop div_while by force

end

