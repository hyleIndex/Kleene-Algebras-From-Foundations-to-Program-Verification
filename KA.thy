(* Title: Kleene Algebra
   Author: Peixin You
*)

section \<open>Kleene Algebra\<close>

theory KA
  imports Main

begin

subsection \<open>Monoids\<close>

notation times (infixl "\<cdot>" 70)

class mult_monoid = times + one +
  assumes mult_assoc: "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z"
  and mult_unitl: "1 \<cdot> x = x"
  and mult_unitr: "x \<cdot> 1 = x"

class add_monoid = plus + zero +
  assumes add_assoc: "x + (y + z) = (x + y) + z"
  and add_unitl: "0 + x = x"
  and add_unitr: "x + 0 = x"

class abelian_add_monoid = add_monoid +
  assumes add_comm: "x + y = y + x"


subsection \<open>Semilattices\<close>

class sup_semilattice = comm_monoid_add + ord +
  assumes add_idem: "x + x = x"
  and order_def: "x \<le> y \<longleftrightarrow> x + y = y"
  and strict_order_def: "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

begin

subclass order 
proof unfold_locales
  fix x y z
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    using add_commute order_def strict_order_def by auto
  show "x \<le> x"
    by (simp add: add_idem order_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (metis add_assoc order_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: add_commute order_def)
qed

lemma zero_least: "0 \<le> x"
proof-
  have "0 + x = x"
    by simp
  thus "0 \<le> x"
    by (simp add: order_def)
qed

lemma add_isor: "x \<le> y \<Longrightarrow> x + z \<le> y + z" 
proof-
  assume "x \<le> y"
  hence a: "x + y = y"
    by (simp add: order_def)
  have "x + z + y + z = x + y + z"
    by (metis add_commute local.add_assoc local.add_idem)
  also have "\<dots> = y + z"
    by (simp add: a)
  finally have "x + z + y + z = y + z".
  thus "x + z \<le> y + z"
    by (simp add: add_assoc order_def)
qed

text \<open>This proof shows three things: First you can use the label a: to use a hypothesis/intermediate result 
later in a proof (not just in the next step writing hence. In this case in the third step of the proof. 
Second you can do textbook style equational reasoning using also have and finally have. Third, you can type  dot after the finally 
have to chain the proof steps together.\<close>

lemma add_iso: "x \<le> y \<Longrightarrow> x' \<le> y' \<Longrightarrow> x + x' \<le> y + y'"
proof-
  assume a: "x \<le> y"
  assume b: "x'\<le> y'"
  have c: "x + y = y"
    using a local.order_def by force
  have d: "x' + y' = y'"
    using b local.order_def by force
  have "x + x' + y + y' = y + x' + y'"
    by (metis add_commute c local.add_assoc)
  also have "\<dots> = y + y'"
    by (simp add: d local.add_assoc)
  finally show "x + x' \<le> y + y'"
    by (simp add: local.add_assoc local.order_def)
qed

lemma add_ubl: "x \<le> x + y" 
proof-
  have "x + y = x + x + y"
    by (simp add: add_idem)
  thus ?thesis
    by (metis add_assoc order_def)
qed

lemma add_ubr: "y \<le> x + y"
  using add_commute add_ubl by fastforce

lemma add_least: "x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> x + y \<le> z" 
proof-
  assume "x \<le> z" and "y \<le> z"
  hence "x + z = z" and "y + z = z"
    by (simp add: order_def)+
  hence "x + y + z = z"
    by (simp add: add_assoc)
  thus "x + y \<le> z"
    by (simp add: order_def)
qed

lemma add_lub: "(x + y \<le> z) = (x \<le> z \<and> y \<le> z)"
  using add_least add_ubl add_ubr dual_order.trans by blast

end


subsection \<open>Semirings and Dioids\<close>

class semiring = comm_monoid_add + monoid_mult +
  assumes distl: "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
  and distr: "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
  and annil [simp]: "0 \<cdot> x = 0"
  and annir [simp]: "x \<cdot> 0 = 0"

class dioid = semiring + sup_semilattice

begin

lemma mult_isol: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"
proof-
  assume "x \<le> y"
  hence "x + y = y"
    by (simp add: order_def)
  hence "z \<cdot> (x + y) = z \<cdot> y"
    by simp
  hence "z \<cdot> x + z \<cdot> y = z \<cdot> y"
    by (simp add: distl)
  thus "z \<cdot> x \<le> z \<cdot> y"
    by (simp add: order_def)
qed

lemma mult_isor: "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"
  by (metis distr order_def)

lemma mult_iso: "x \<le> y \<Longrightarrow> x' \<le> y' \<Longrightarrow> x \<cdot> x' \<le> y \<cdot> y'"
  using order_trans mult_isol mult_isor by blast

end

subsection \<open>Kleene Algebras\<close>

class kleene_algebra = dioid + 
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100)
  assumes star_unfoldl: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"  
  and star_unfoldr: "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  and star_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and star_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"

begin

lemma one_le_star: "1 \<le> x\<^sup>\<star>" 
proof-
  have "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (simp add: star_unfoldl) 
  thus "1 \<le> x\<^sup>\<star>"
    by (simp add: add_lub)
qed

lemma star_unfoldlr: "x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  using add_lub star_unfoldl by simp

lemma star_unfoldrr: "x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  using add_lub star_unfoldr by simp

lemma star_infl: "x \<le> x\<^sup>\<star>" 
proof-
  have "x = x \<cdot> 1"
    by simp
  also have "\<dots> \<le> x \<cdot> x\<^sup>\<star>"
    using mult_isol one_le_star by force
  also have "\<dots> \<le> x\<^sup>\<star>"
    by (simp add: star_unfoldlr)
  finally show "x \<le> x\<^sup>\<star>".
qed

lemma star_power: "x ^ i \<le> x\<^sup>\<star>"
proof (induct i)
case 0
  show "x ^ 0 \<le> x\<^sup>\<star>"
    by (simp add: one_le_star)
next
  case (Suc i)
  assume "x ^ i \<le> x\<^sup>\<star>"
  have "x ^ Suc i = x \<cdot> x ^ i"
    by simp
  also have "\<dots> \<le> x \<cdot> x\<^sup>\<star>"
    by (simp add: Suc.hyps mult_isol)
  also have "\<dots>  \<le> x\<^sup>\<star>"
    by (simp add: star_unfoldlr)
  finally show "x ^ Suc i \<le> x\<^sup>\<star>".
qed

lemma star_trans [simp]: "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>" 
proof (rule antisym)
  have "x\<^sup>\<star> + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (simp add: add_least star_unfoldlr)
  thus "x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (simp add: star_inductl)
  have "x\<^sup>\<star> = 1 \<cdot> x\<^sup>\<star>"
    by simp
  also have "\<dots> \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    using mult_isor one_le_star by force
  finally show "x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<star>".
qed

lemma star_idem [simp]: "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>" 
proof (rule antisym)
  have "1 + x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (simp add: add_least one_le_star)
  thus  "(x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star>"
    using star_inductl by fastforce
  show "x\<^sup>\<star> \<le> (x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: star_infl)
qed

lemma star_unfoldl_eq [simp]: "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"  
proof (rule antisym)
  show le: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>" 
    by (simp add: star_unfoldl) 
  have "1 + x \<cdot> (1 + x \<cdot> x\<^sup>\<star>) = 1 + x + x \<cdot> x \<cdot> x\<^sup>\<star>"
    by (simp add: add_assoc distl mult_assoc)
  also have "\<dots> \<le> 1 + x \<cdot> x\<^sup>\<star>"
    by (smt calculation le add_assoc distl add_idem order_def)
  finally have "1 + x \<cdot> (1 + x \<cdot> x\<^sup>\<star>) \<le> 1 + x \<cdot> x\<^sup>\<star>".
  thus "x\<^sup>\<star> \<le> 1 + x \<cdot> x\<^sup>\<star>"
    using star_inductl by fastforce
qed

lemma star_unfoldr_eq [simp]: "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
   apply (rule antisym)
   apply (simp add: star_unfoldr)
  by (smt distl distr mult.semigroup_axioms mult_1_left mult_1_right order_refl star_inductl semigroup.assoc star_unfoldl_eq)

lemma star_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>" 
proof-
  assume "x \<le> y"
  hence "1 + x \<cdot> y\<^sup>\<star> \<le> 1 + y \<cdot> y\<^sup>\<star>"
    using add_iso mult_iso by blast
  also have "\<dots> \<le> y\<^sup>\<star>"
    by (simp add: star_unfoldl)
  finally show " x\<^sup>\<star> \<le> y\<^sup>\<star>"
    using star_inductl by fastforce
qed

lemma star_slide: "(x \<cdot> y)\<^sup>\<star> \<cdot> x = x \<cdot> (y \<cdot> x)\<^sup>\<star>" 
proof (rule antisym)
  have "1 + y \<cdot> x \<cdot> (y \<cdot> x)\<^sup>\<star> \<le> (y \<cdot> x)\<^sup>\<star>"
    by (simp add: star_unfoldl)
  hence "x + x \<cdot> y \<cdot> x \<cdot> (y \<cdot> x)\<^sup>\<star> \<le> x \<cdot> (y \<cdot> x)\<^sup>\<star>"
    by (metis distl eq_iff mult_1_right mult_assoc star_unfoldl_eq)
  thus "(x \<cdot> y)\<^sup>\<star> \<cdot> x \<le> x \<cdot> (y \<cdot> x)\<^sup>\<star>"
    by (simp add: star_inductl mult_assoc)
  have "1 + (x \<cdot> y)\<^sup>\<star> \<cdot> x \<cdot> y \<le> (x \<cdot> y)\<^sup>\<star>"
    by (simp add: mult_assoc)
  hence "x + (x \<cdot> y)\<^sup>\<star> \<cdot> x \<cdot> y \<cdot> x \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> x"
    by (metis distr eq_refl mult_1_left mult_assoc star_unfoldr_eq)
  thus "x \<cdot> (y \<cdot> x)\<^sup>\<star> \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> x"
    by (simp add: star_inductr mult_assoc)
qed

lemma star_denest: "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>" 
proof (rule antisym)
  have a: "1 \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (metis mult_1_right mult_isol order_trans one_le_star)
  have b: "x \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: mult_isor star_unfoldlr)
  have "y \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: star_unfoldlr)
  also have  "\<dots> = 1 \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by simp
  also have "\<dots> \<le>  x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    using mult_isor one_le_star by blast
  finally have "y \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>".
  hence "1 + (x + y) \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: a b add_lub distr)
  thus  "(x + y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    using mult_assoc star_inductl by fastforce
  have a: "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (simp add: add_ubl star_iso)
  have "y \<le> (x + y)\<^sup>\<star>"
    using add_lub star_infl by blast
  hence "(y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> ((x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<star>)\<^sup>\<star>"
    using a mult_iso star_iso by blast
  also have "\<dots> = (x + y)\<^sup>\<star>"
    by simp
  finally have "(y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star>".
  hence "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<star>"
    using a mult_iso by blast
  also have "\<dots> \<le> (x + y)\<^sup>\<star>"
    by simp
  finally show "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star>".
qed

lemma star_subid: "x \<le> 1 \<Longrightarrow> x\<^sup>\<star> = 1"
proof-
  assume "x \<le> 1" 
  hence "1 + x \<cdot> 1 \<le> 1"
    by (simp add: add_least)
  hence "x\<^sup>\<star> \<le> 1"
    using star_inductl by fastforce
  thus " x\<^sup>\<star> = 1"
    by (simp add: antisym one_le_star)
qed

lemma zero_star [simp]: "0\<^sup>\<star> = 1" 
  by (simp add: zero_least star_subid)

lemma one_star [simp]: "1\<^sup>\<star> = 1" 
  by (simp add: star_subid)

lemma star_sim1: "z \<cdot> x \<le> y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> z" 
proof - 
  assume "z \<cdot> x \<le> y \<cdot> z"
  hence "z + y\<^sup>\<star> \<cdot> z \<cdot> x \<le> z + y\<^sup>\<star> \<cdot> y \<cdot> z"
    by (simp add: add_iso mult_assoc mult_iso)
  also have  "\<dots> = y\<^sup>\<star> \<cdot> z"
    by (metis distr mult_1_left star_unfoldr_eq)
  finally show ?thesis
    by (simp add: star_inductr) 
qed

lemma star_sim2: "x \<cdot> z \<le> z \<cdot> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z  \<le> z \<cdot> y\<^sup>\<star>"
  by (smt add_commute add_assoc distl distr mult_1_right mult_assoc order_def star_inductl one_le_star star_unfoldl_eq)

lemma star_inductl_var: "x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y" 
proof-
  assume "x \<cdot> y \<le> y"
  hence "y + x \<cdot> y \<le> y"
    by (simp add: add_lub)
  thus "x\<^sup>\<star> \<cdot> y \<le> y"
    by (simp add: star_inductl)
qed

lemma star_inductr_var: "y \<cdot> x \<le> y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
  by (simp add: add_least star_inductr)

lemma church_rosser: "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<Longrightarrow> (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>" 
proof-
  assume h: "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  have a: "1 \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis dual_order.trans mult_1_right mult_isol one_le_star)
  have b: "x \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (simp add: mult_isor star_unfoldlr)
  have "y \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (simp add: mult_isor star_infl)
  also have "\<dots> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (simp add: h mult_isor)
  finally have "y \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis mult_assoc star_trans)
  hence "1 + (x + y) \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (simp add: a b add_lub distr)
  hence c: "(x + y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    using mult_assoc star_inductl by fastforce
  have "y\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (simp add: add_ubr star_iso)
  hence "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<star>"
    using add_commute add_ubr mult_iso star_iso by presburger
  hence "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by simp
  thus "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    using c by auto
qed

lemma power_sup: "((\<Sum>i=0..n. x^i) \<le> y) = (\<forall>i. 0 \<le> i \<and> i \<le> n \<longrightarrow> x^i \<le> y)"
proof (induct n)
  case 0
  show "(sum ((^) x) {0..0} \<le> y) = (\<forall>i. 0 \<le> i \<and> i \<le> 0 \<longrightarrow> x ^ i \<le> y)"
    by simp
next
  case (Suc n)
  fix n :: nat
  assume "(sum ((^) x) {0..n} \<le> y) = (\<forall>i. 0 \<le> i \<and> i \<le> n \<longrightarrow> x ^ i \<le> y)"
  thus "(sum ((^) x) {0..Suc n} \<le> y) = (\<forall>i. 0 \<le> i \<and> i \<le> Suc n \<longrightarrow> x ^ i \<le> y)"
    using le_Suc_eq local.add_lub by force
qed

lemma power_dist: "(\<Sum>i=0..n. x ^ i) \<cdot> x = (\<Sum>i=0..n. x ^ Suc i)"
proof (induct n)
  case 0
  show ?case by simp
next 
  case (Suc n)
  show ?case
    using Suc local.distr local.power_Suc2 local.sum.atLeast0_atMost_Suc by presburger 
qed

lemma power_sum: "(\<Sum>i=0..n. x ^ Suc i) = (\<Sum>i=1..n. x ^ i) + x ^ Suc n"
proof (induct n)
  case 0
  show ?case by simp
next 
  case (Suc n)
  show ?case
    using Suc.hyps by force
qed

lemma sum_star: "x\<^sup>\<star> = (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=0..n. x ^ i)"
proof (rule antisym)
  have "1 + (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=0..n. x ^ i) \<cdot> x = 1 + (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=0..n. x ^ Suc i)"
    using local.mult_assoc power_dist by presburger
  also have "\<dots> =  1 + (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=1..n. x ^ i) + (x ^ Suc n)\<^sup>\<star> \<cdot> x ^ Suc n"
    using local.add_assoc local.distl local.power_sum by presburger
  also have "\<dots> = (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=1..n. x ^ i) + (x ^ Suc n)\<^sup>\<star>"
    by (metis local.add.left_commute local.add_assoc star_unfoldr_eq)
  also have "\<dots> = (x ^ Suc n)\<^sup>\<star> \<cdot> (1 + (\<Sum>i=1..n. x ^ i))"
    using add_commute local.distl local.mult_1_right by presburger
  also have "\<dots> = (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=0..n. x ^ i)"
    by (simp add: local.sum.atLeast_Suc_atMost)
  finally show "x\<^sup>\<star> \<le> (x ^ Suc n)\<^sup>\<star> \<cdot> sum ((^) x) {0..n}"
    by (metis local.mult_1_left local.order_refl local.star_inductr)
next
  have a: "(x ^ Suc n)\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis star_idem star_iso star_power)
  have "(\<Sum>i=0..n. x ^ i) \<le> x\<^sup>\<star>"
    using power_sup star_power by presburger
  thus "(x ^ Suc n)\<^sup>\<star> \<cdot> sum ((^) x) {0..n} \<le> x\<^sup>\<star>"
    by (metis a local.mult_iso star_trans)
qed

end

subsection \<open>Linking Algebras with Models by Instantiation\<close>

instantiation nat :: mult_monoid
begin

instance
proof
  fix x y z :: nat
  show "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z"
    by simp
  show "1 \<cdot> x = x"
    by simp
  show "x \<cdot> 1 = x "
    by simp
qed

end

instantiation nat :: abelian_add_monoid
begin

instance
proof
  fix x y z :: nat
  show "x + (y + z) = (x + y) + z"
    by simp
  show "0 + x = x"
    by simp
  show "x + 0 = x "
    by simp
  show "x + y = y + x"
    by simp
qed

end

typedef 'a endo = "{f::'a \<Rightarrow> 'a . True}"
  by simp

setup_lifting type_definition_endo

instantiation endo :: (type) mult_monoid
begin

lift_definition one_endo :: "'a endo" is
  "Abs_endo id".

lift_definition times_endo :: "'a endo \<Rightarrow> 'a endo \<Rightarrow> 'a endo" is
  "\<lambda>x y. Abs_endo (Rep_endo x \<circ> Rep_endo y)".

instance
proof
  fix x y z :: "'a endo"
  show "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z"
    by transfer (simp add: Abs_endo_inverse fun.map_comp)
  show "1 \<cdot> x = x"
    by transfer (simp add: Abs_endo_inverse Rep_endo_inverse)
  show "x \<cdot> 1 = x "
    by transfer (simp add: Abs_endo_inverse Rep_endo_inverse)
qed

end 

instantiation set :: (type) sup_semilattice
begin

definition plus_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "plus_set x y = x \<union> y"

definition zero_set :: "'a set" where 
  "zero_set = {}"

instance 
proof
  fix x y z :: "'a set"
  show "x + y + z = x + (y + z)"
    by (simp add: KA.plus_set_def sup_assoc)
  show "0 + x = x"
    by (simp add: plus_set_def zero_set_def)
  show "x + x = x"
    by (simp add: KA.plus_set_def)
  show "x + y = y + x"
    by (simp add: KA.plus_set_def sup_commute)
  show "(x \<subseteq> y) = (x + y = y)"
    by (simp add: KA.plus_set_def subset_Un_eq)
  show "(x \<subset> y) = (x \<subseteq> y \<and> x \<noteq> y)"
    by force
qed

end

interpretation inter_sl: sup_semilattice "(\<inter>)" UNIV "(\<supseteq>)" "(\<supset>)"
proof 
  fix X Y Z :: "'a set"
  show "X \<inter> Y \<inter> Z = X \<inter> (Y \<inter> Z)"
    by (simp add: Int_assoc)
  show "X \<inter> Y = Y \<inter> X"
    by (simp add: inf_commute)
  show "UNIV \<inter> X = X"
    by simp
  show "X \<inter> X = X"
    by simp 
  show "(Y \<subseteq> X) = (X \<inter> Y = Y)"
    by blast
  show "(Y \<subset> X) = (Y \<subseteq> X \<and> X \<noteq> Y)"
    by auto
qed

context dioid
begin

lemma power_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x ^ i \<cdot> z \<le> y"
proof (induct i)
  case 0
  have "x ^ 0 \<cdot> z = z"
    by simp
  also have "\<dots> \<le> y"
    using "0.prems" local.add_lub by fastforce
  finally show ?case.
next
  case (Suc i)
  have "x ^ Suc i \<cdot> z = x \<cdot> x ^ i \<cdot> z"
    by simp
  also have "\<dots> \<le> x \<cdot> y"
    by (simp add: Suc.hyps Suc.prems local.mult_assoc local.mult_isol)
  also have "\<dots> \<le> y"
    using Suc.prems local.add_lub by auto
  finally show ?case.
qed

lemma power_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ i \<le> y"
proof (induct i)
case 0
  thus ?case
    by (simp add: add_lub)
next
  case (Suc i)
  thus ?case
    by (smt add_lub distr mult_assoc order_def power_Suc2)
qed

end

subsection \<open>Relational Model of Kleene algebra\<close>

notation relcomp (infixl ";" 70)

text \<open>rel is not a type in Isabelle, so we need to do an interpretation statement instead of an 
instantiation. That for dioids (Proposition 4.5) is trivial because relations are well supported
in Isabelle.\<close>

interpretation rel_d: dioid "(\<union>)" "{}" Id "(;)" "(\<subseteq>)" "(\<subset>)"
  by unfold_locales auto

lemma power_is_relpow: "rel_d.power R i = R ^^ i"
  by (induct i) (simp_all add: relpow_commute)

lemma rel_star_def: "R\<^sup>* = (\<Union>i. rel_d.power R i)"
  by (simp add: power_is_relpow rtrancl_is_UN_relpow)

lemma rel_star_contl: "R ; S\<^sup>* = (\<Union>i. R ; rel_d.power S i)"
proof-
  have "R ; S\<^sup>* = R ; (\<Union>i. rel_d.power S i)"
    unfolding rel_star_def by simp
  also have "\<dots> = (\<Union>i. R ; rel_d.power S i)"
    by (simp add: relcomp_UNION_distrib)
  finally show ?thesis.
qed

lemma rel_star_contr: "R\<^sup>* ; S = (\<Union>i. (rel_d.power R i) ; S)"
  by (simp add: rel_star_def relcomp_UNION_distrib2)

lemma rel_star_unfoldl: "Id \<union> R ; R\<^sup>* = R\<^sup>*"
proof-
  have "Id \<union> R ; R\<^sup>* = Id \<union> R ; (\<Union>i. rel_d.power R i)"
    by (simp add: rel_star_def)
  also have "\<dots> = Id \<union> (\<Union>i. R ; rel_d.power R i)"
    by (simp add: relcomp_UNION_distrib)
  also have "\<dots> = rel_d.power R 0  \<union> (\<Union>i. rel_d.power R (Suc i))"
    by auto
  also have "\<dots> = (\<Union>i. rel_d.power R i)"
    by (metis calculation r_comp_rtrancl_eq rel_star_def rtrancl_unfold)
  also have "\<dots> = R\<^sup>*"
    by (simp add: rel_star_def)
  finally show ?thesis.
qed

lemma rel_star_unfoldr: "Id \<union> R\<^sup>* ; R = R\<^sup>*"
  using rtrancl_unfold by blast

lemma rel_star_inductl: 
  fixes R S T :: "'a rel"
  assumes "T \<union> R ; S \<subseteq> S"
  shows "R\<^sup>* ; T \<subseteq> S"
proof-
  have "\<forall>i. rel_d.power R i ; T \<subseteq> S"
    by (meson assms rel_d.power_inductl)
  hence "(\<Union>i. (rel_d.power R i) ; T) \<subseteq> S"
    by (simp add: SUP_least)
  hence "(\<Union>i. rel_d.power R i) ; T \<subseteq> S"
    by (simp add: relcomp_UNION_distrib2)
  thus ?thesis
    unfolding rel_star_def by simp
qed

lemma rel_star_inductr: "(T::'a rel) \<union> S ; R \<subseteq> S \<Longrightarrow> T ; R\<^sup>* \<subseteq> S"
  unfolding rel_star_def by (simp add: SUP_le_iff rel_d.power_inductr relcomp_UNION_distrib)

interpretation rel_ka: kleene_algebra "(\<union>)" "{}" Id "(;)" "(\<subseteq>)" "(\<subset>)" rtrancl
proof unfold_locales
  fix x y z :: "'a rel"  
  show "Id \<union> x ; x\<^sup>* \<subseteq> x\<^sup>*"
    by (simp add: rel_star_unfoldl)
  show "Id \<union> x\<^sup>* ; x \<subseteq> x\<^sup>*"
    by fastforce
  show  "z \<union> x ; y \<subseteq> y \<Longrightarrow> x\<^sup>* ; z \<subseteq> y"
    by (simp add: rel_star_inductl)
  show "z \<union> y ; x \<subseteq> y \<Longrightarrow> z ; x\<^sup>* \<subseteq> y"
    by (simp add: rel_star_inductr)
qed

subsection \<open>State Transformer Model of Kleene Algebra\<close>

type_synonym 'a sta = "'a \<Rightarrow> 'a set"

abbreviation eta :: "'a sta" ("\<eta>") where
  "\<eta> x \<equiv> {x}"

abbreviation nsta :: "'a sta" ("\<nu>") where 
  "\<nu> x \<equiv> {}" 

definition kcomp :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" (infixl "\<circ>\<^sub>K" 75) where
  "(f \<circ>\<^sub>K g) x = \<Union>{g y |y. y \<in> f x}"

definition kadd :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" (infixl "+\<^sub>K" 65) where
  "(f +\<^sub>K g) x = f x \<union> g x" 

definition kleq :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "f \<sqsubseteq> g = (\<forall>x. f x \<subseteq> g x)"

definition kle :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
  "f \<sqsubset> g = (f \<sqsubseteq> g \<and> f \<noteq> g)"

lemma sta_iff: "((f::'a sta) = g) = (\<forall>x y. y \<in> f x \<longleftrightarrow> y \<in> g x)"
  unfolding fun_eq_iff by force
    
lemma kcomp_iff: "y \<in> (f \<circ>\<^sub>K g) x = (\<exists>z. y \<in> g z \<and> z \<in> f x)"
  unfolding kcomp_def by force

lemma kadd_iff: "y \<in> (f +\<^sub>K g) x = (y \<in> f x \<or> y \<in> g x)"
  unfolding kadd_def by simp

lemma kleq_iff: "f \<sqsubseteq> g = (\<forall>x y. y \<in> f x \<longrightarrow> y \<in> g x)"
  unfolding kleq_def by blast

named_theorems sta_unfolds

declare
sta_iff [sta_unfolds]
kcomp_iff [sta_unfolds]
kadd_iff [sta_unfolds]
kleq_iff [sta_unfolds]

lemma kcomp_assoc: "(f \<circ>\<^sub>K g) \<circ>\<^sub>K h = f \<circ>\<^sub>K (g \<circ>\<^sub>K h)"
proof-
  {fix x y
  have "y \<in> ((f \<circ>\<^sub>K g) \<circ>\<^sub>K h) x = (\<exists>v. y \<in> h v \<and> (\<exists>w. v \<in> g w \<and> w \<in> f x))"
    unfolding sta_unfolds by simp
  also have "\<dots> = (\<exists>v w. y \<in> h v \<and> v \<in> g w \<and> w \<in> f x)"
    by blast
  also have "\<dots> = (\<exists>w. (\<exists>v. y \<in> h v \<and> v \<in> g w) \<and> w \<in> f x)"
    by blast
  also have "\<dots> = (y \<in> (f \<circ>\<^sub>K (g \<circ>\<^sub>K h)) x)"
    unfolding sta_unfolds by simp
  finally have "y \<in> ((f \<circ>\<^sub>K g) \<circ>\<^sub>K h) x = (y \<in> (f \<circ>\<^sub>K (g \<circ>\<^sub>K h)) x)".}
  thus ?thesis
    unfolding sta_unfolds by simp
qed

interpretation sta_monm: monoid_mult "\<eta>" "(\<circ>\<^sub>K)"
  by unfold_locales (auto simp: sta_unfolds)

interpretation sta_di: dioid "(+\<^sub>K)" "\<nu>" "\<eta>" "(\<circ>\<^sub>K)" "(\<sqsubseteq>)" "(\<sqsubset>)"
  by unfold_locales (auto simp: sta_unfolds kle_def)

abbreviation "kpow \<equiv> sta_monm.power"

definition kstar :: "'a sta \<Rightarrow> 'a sta" where
  "kstar f x = (\<Union>i. kpow f i x)"

lemma kstar_iff: "y \<in> kstar f x = (\<exists>i. y \<in> kpow f i x)"
  unfolding kstar_def by blast

declare kstar_iff [sta_unfolds]

lemma kstar_unfoldl: "\<eta> +\<^sub>K f \<circ>\<^sub>K kstar f \<sqsubseteq> kstar f"
  by (unfold sta_unfolds, metis (mono_tags) kcomp_iff power.power_eq_if sta_monm.power_Suc)

lemma kstar_unfoldr: "\<eta> +\<^sub>K kstar f \<circ>\<^sub>K f \<sqsubseteq> kstar f"
  by (unfold sta_unfolds, metis (mono_tags, lifting) kcomp_iff power.power.power_0 sta_monm.power_Suc2) 

lemma kstar_contl: "(f \<circ>\<^sub>K kstar g) x = (\<Union>i. (f \<circ>\<^sub>K kpow g i) x)"
proof-
  {fix y
  have "y \<in> (f \<circ>\<^sub>K kstar g) x = (\<exists>z. z \<in> f x \<and> (\<exists>i. y \<in> kpow g i z))"
    unfolding sta_unfolds  by auto 
  also have "\<dots> = (\<exists>i. (\<exists>z. z \<in> f x \<and> y \<in> kpow g i z))"
    by blast
  also have "\<dots> = (\<exists>i. (y \<in> (f \<circ>\<^sub>K kpow g i) x))"
    by (meson kcomp_iff)
  also have "\<dots> = (y \<in> (\<Union>i. (f \<circ>\<^sub>K kpow g i) x))"
    by blast
  finally have  "y \<in> (f \<circ>\<^sub>K kstar g) x = (y \<in> (\<Union>i. (f \<circ>\<^sub>K kpow g i) x))"
    by blast}
  thus ?thesis
    by blast
qed

lemma kstar_contr: "(kstar f \<circ>\<^sub>K g) x = (\<Union>i. (kpow f i \<circ>\<^sub>K g) x)"
  by (force simp: set_eq_iff sta_unfolds)

lemma kstar_inductl: "h +\<^sub>K f \<circ>\<^sub>K g \<sqsubseteq> g \<Longrightarrow> kstar f \<circ>\<^sub>K h \<sqsubseteq> g"
proof-
  assume "h +\<^sub>K f \<circ>\<^sub>K g \<sqsubseteq> g"
  hence "\<forall>i. kpow f i \<circ>\<^sub>K h \<sqsubseteq> g"
    using sta_di.power_inductl by blast
  thus "kstar f \<circ>\<^sub>K h \<sqsubseteq> g"
    by (unfold sta_unfolds, metis UN_E kstar_contr)
qed

lemma kstar_inductr: "h +\<^sub>K g \<circ>\<^sub>K f \<sqsubseteq> g \<Longrightarrow> h \<circ>\<^sub>K kstar f \<sqsubseteq> g"
proof-
  assume "h +\<^sub>K g \<circ>\<^sub>K f \<sqsubseteq> g"
  hence "\<forall>i. h \<circ>\<^sub>K kpow f i  \<sqsubseteq> g"
    using sta_di.power_inductr by blast
  thus "h \<circ>\<^sub>K kstar f  \<sqsubseteq> g"
    by (unfold sta_unfolds, metis UN_E kstar_contl)
qed

interpretation sta_ka: kleene_algebra "(+\<^sub>K)" "\<nu>" "\<eta>" "(\<circ>\<^sub>K)" "(\<sqsubseteq>)" "(\<sqsubset>)" kstar
  by unfold_locales (simp_all add: kstar_unfoldl kstar_unfoldr kstar_inductl kstar_inductr)


subsection \<open>Isomorphism between the models\<close>

definition r2s :: "'a rel \<Rightarrow> 'a sta" ("\<S>") where
  "\<S> R = Image R \<circ> \<eta>" 

definition s2r :: "'a sta \<Rightarrow> 'a rel" ("\<R>") where
  "\<R> f = {(x,y). y \<in> f x}"

lemma r2s_iff: "y \<in> \<S> R x \<longleftrightarrow> (x,y) \<in> R"
  by (simp add: r2s_def)

lemma s2r_iff: "(x,y) \<in> \<R> f \<longleftrightarrow> y \<in> f x"
  by (simp add: s2r_def)

text \<open>The functors form a bijective pair.\<close>

lemma r2s2r_inv1 [simp]: "\<R> \<circ> \<S> = id"
  unfolding s2r_def r2s_def by force

lemma s2r2s_inv2 [simp]: "\<S> \<circ> \<R> = id"
  unfolding s2r_def r2s_def by force

lemma r2s2r_galois: "(\<R> f = R) = (\<S> R = f)"
  by (force simp: s2r_def r2s_def)

lemma r2s_inj: "inj \<S>"
  by (meson inj_on_inverseI r2s2r_galois)

lemma s2r_inj: "inj \<R>"
  unfolding inj_def using r2s2r_galois by metis

lemma r2s_surj: "surj \<S>"
  by (metis r2s2r_galois surj_def)

lemma s2r_surj: "surj \<R>"
  using r2s2r_galois by auto

lemma r2s_bij: "bij \<S>"
  by (simp add: bijI r2s_inj r2s_surj)

lemma s2r_bij: "bij \<R>"
  by (simp add: bij_def s2r_inj s2r_surj)

lemma s2r_comp: "\<S> (R ; S) = \<S> R \<circ>\<^sub>K \<S> S"
  unfolding sta_unfolds r2s_iff by force

lemma r2s_comp: "\<R> (f \<circ>\<^sub>K g) = \<R> f ; \<R> g"
  by (metis s2r_comp r2s2r_galois)

lemma s2r_id: "\<S> Id = \<eta>"
  by (metis empty_iff insert_iff pair_in_Id_conv r2s_iff subsetI subset_singletonD)

lemma r2s_id: "\<R> \<eta> = Id"
  by (metis R_O_Id power.power.power_0 r2s_comp r2s2r_galois rel_d.power_Suc rel_d.power_Suc2 sta_monm.mult_1_right)

lemma s2r_zero: "\<S> {} = \<nu>"
  unfolding r2s_def by force

lemma r2s_zero: "\<R> \<nu> = {}"
  by (simp add: s2r_def)

lemma r2s_add: "\<S> (R \<union> S) = \<S> R +\<^sub>K \<S> S"
  unfolding sta_unfolds r2s_iff by force

lemma s2r_add: "\<R> (f +\<^sub>K g) = \<R> f \<union> \<R> g"
  by (metis r2s_add r2s2r_galois)

lemma s2r_pow: "\<S> (rel_d.power R i) = kpow (\<S> R) i"
proof (induct i)
  case 0
  thus "\<S> (rel_d.power R 0) = kpow (\<S> R) 0"
    by (metis power.power.power_0 r2s2r_galois r2s_id)
next
  case (Suc i)
  assume h: "\<S> (rel_d.power R i) = kpow (\<S> R) i"
  have "\<S> (rel_d.power R (Suc i)) =\<S> R \<circ>\<^sub>K \<S> (rel_d.power R i)"
    by (simp add: s2r_comp)
  also have "... = \<S> R \<circ>\<^sub>K  kpow (\<S> R) i"
    by (simp add: h)
  also have "\<dots> = kpow (\<S> R) (Suc i)"
    by simp
  finally show "\<S> (rel_d.power R (Suc i)) = kpow (\<S> R) (Suc i)"
    by blast
qed

lemma s2r_star: "\<S> (R\<^sup>*) = kstar (\<S> R)"
proof-
  {fix x y
    have "y \<in> \<S> (R\<^sup>*) x = (\<exists>i. (x,y) \<in> rel_d.power R i)"
      by (simp add: power_is_relpow r2s_iff rtrancl_power)
  also have "\<dots> = (y \<in> (\<Union>i. \<S> (rel_d.power R i) x))"
    by (simp add: r2s_iff)
  also have "\<dots> = (y \<in> (\<Union>i. kpow (\<S> R) i x))"
    by (simp add: s2r_pow)
  also have "\<dots> = (y \<in> kstar (\<S> R) x)"
    by (simp add: kstar_iff)
  finally have "y \<in> \<S> (R\<^sup>*) x = (y \<in> kstar (\<S> R) x)".}
  thus ?thesis
    by blast
qed

lemma r2s_pow: "rel_d.power (\<R> f) i = \<R> (kpow f i)"
  by (metis s2r_pow r2s2r_galois)

lemma r2s_star: "\<R> (kstar f) = (\<R> f)\<^sup>*"
  by (metis s2r_star r2s2r_galois)

lemma kcomp_assoc2: "(f \<circ>\<^sub>K g) \<circ>\<^sub>K h = f \<circ>\<^sub>K (g \<circ>\<^sub>K h)"
proof-
  have "(f \<circ>\<^sub>K g) \<circ>\<^sub>K h = \<S> (\<R> ((f \<circ>\<^sub>K g) \<circ>\<^sub>K h))"
    by (metis r2s2r_galois)
  also have "\<dots> = \<S> ((\<R> f ; \<R> g) ; \<R> h)"
    by (simp add: r2s_comp)
  also have "\<dots> = \<S> (\<R> f ; (\<R> g ; \<R> h))"
    by (simp add: rel_d.mult_assoc)
  also have "\<dots> = \<S> (\<R> (f \<circ>\<^sub>K (g \<circ>\<^sub>K h)))"
    by (simp add: r2s_comp)
  also have "\<dots> = f \<circ>\<^sub>K (g \<circ>\<^sub>K h)"
    using r2s2r_galois by blast
  finally show ?thesis.
qed


subsection \<open>Embedding Predicates into State Transformers and Relations\<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

notation inf (infixl "\<sqinter>" 70) 
notation sup (infixl "\<squnion>" 65)

text \<open>First we consider relations.\<close>

definition p2r :: "'a pred \<Rightarrow> 'a rel" ("\<lceil>_\<rceil>\<^sub>r") where
  "\<lceil>P\<rceil>\<^sub>r = {(s,s) |s. P s}"

definition r2p :: "'a rel \<Rightarrow> 'a pred" ("\<lfloor>_\<rfloor>\<^sub>r")where
  "\<lfloor>R\<rfloor>\<^sub>r \<equiv> (\<lambda>s. s \<in> Domain R)"

lemma r2p2r [simp]: "\<lfloor>\<lceil>P\<rceil>\<^sub>r\<rfloor>\<^sub>r = P"
  unfolding p2r_def r2p_def by force

lemma p2r2p: "R \<subseteq> Id \<Longrightarrow> \<lceil>\<lfloor>R\<rfloor>\<^sub>r\<rceil>\<^sub>r = R"
  unfolding p2r_def r2p_def by force

lemma p2r_r2p_galois: "R \<subseteq> Id \<Longrightarrow> (\<lfloor>R\<rfloor>\<^sub>r = P) = (R = \<lceil>P\<rceil>\<^sub>r)"
  using p2r2p by auto

lemma p2r_comp [simp]: "\<lceil>P\<rceil>\<^sub>r ; \<lceil>Q\<rceil>\<^sub>r = \<lceil>\<lambda>s. P s \<and> Q s\<rceil>\<^sub>r" 
  unfolding p2r_def by auto

lemma r2p_comp: "R \<subseteq> Id \<Longrightarrow> S \<subseteq> Id \<Longrightarrow> \<lfloor>R ; S\<rfloor>\<^sub>r = (\<lambda>s. \<lfloor>R\<rfloor>\<^sub>r s \<and> \<lfloor>S\<rfloor>\<^sub>r s)" 
  unfolding r2p_def by force

lemma p2r_imp [simp]: "\<lceil>P\<rceil>\<^sub>r \<subseteq> \<lceil>Q\<rceil>\<^sub>r = (\<forall>s. P s \<longrightarrow> Q s)"
  unfolding p2r_def by force

text \<open>Next we repeat the development with state transformers.\<close>

definition p2s :: "'a pred \<Rightarrow> 'a sta" ("\<lceil>_\<rceil>\<^sub>s") where
  "\<lceil>P\<rceil>\<^sub>s x \<equiv> if P x then {x} else {}"

definition s2p :: "'a sta \<Rightarrow> 'a pred" ("\<lfloor>_\<rfloor>\<^sub>s")where
  "\<lfloor>f\<rfloor>\<^sub>s s \<equiv> (f s \<noteq> {})"

lemma s2p2s [simp]: "\<lfloor>\<lceil>P\<rceil>\<^sub>s\<rfloor>\<^sub>s = P"
  unfolding p2s_def s2p_def by force

lemma p2s2p: "f \<sqsubseteq> \<eta> \<Longrightarrow> \<lceil>\<lfloor>f\<rfloor>\<^sub>s\<rceil>\<^sub>s = f"
  unfolding p2s_def s2p_def sta_iff kleq_iff by force 

lemma p2s_s2p_galois: "f \<sqsubseteq> \<eta> \<Longrightarrow> (\<lfloor>f\<rfloor>\<^sub>s = P) = (f = \<lceil>P\<rceil>\<^sub>s)"
  unfolding p2s_def s2p_def sta_iff kleq_iff by force

lemma p2s_comp [simp]: "\<lceil>P\<rceil>\<^sub>s \<circ>\<^sub>K \<lceil>Q\<rceil>\<^sub>s = \<lceil>\<lambda>s. P s \<and> Q s\<rceil>\<^sub>s" 
  unfolding  p2s_def s2p_def sta_iff kcomp_iff by force

lemma s2p_comp: "f \<sqsubseteq> \<eta> \<Longrightarrow> g \<sqsubseteq> \<eta> \<Longrightarrow> \<lfloor>f \<circ>\<^sub>K g\<rfloor>\<^sub>s = (\<lambda>s. \<lfloor>f\<rfloor>\<^sub>s s \<and> \<lfloor>g\<rfloor>\<^sub>s s)" 
  unfolding s2p_def kleq_iff kcomp_iff kcomp_def by blast

lemma p2s_imp [simp]: "\<lceil>P\<rceil>\<^sub>s \<sqsubseteq> \<lceil>Q\<rceil>\<^sub>s = (\<forall>s. P s \<longrightarrow> Q s)"
  unfolding  p2s_def s2p_def kleq_iff by simp

lemma p2r2s: "\<lceil>P\<rceil>\<^sub>s = \<S> \<lceil>P\<rceil>\<^sub>r"
  unfolding p2r_def p2s_def sta_iff r2s_iff by simp

lemma p2s2r: "\<lceil>P\<rceil>\<^sub>r = \<R> \<lceil>P\<rceil>\<^sub>s"
  by (metis (no_types) p2r2s r2s2r_galois)

end





