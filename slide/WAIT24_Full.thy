chapter \<open>Coinductive Reasoning in Isabelle/HOL\<close>

text \<open>
Dmitriy Traytel
University of Copenhagen

Disclaimer:
parts of this theory follow a chapter on coinductive methods
by Damien Pous and myself in the forthcoming book

Proof Assistants and Their Applications in Mathematics and Computer Science

(edited by Jasmin Blanchette and Assia Mahboubi)
\<close>

theory WAIT24_Full
  imports
    "HOL-Library.FSet"
    "HOL-Library.BNF_Corec"
    "HOL-Library.Code_Lazy"
    "HOL-Library.Simps_Case_Conv"
begin

hide_const (open) even
hide_const (open) odd
hide_const (open) zip

declare [[inductive_internals,function_internals,bnf_internals]]

section \<open>Knaster--Tarski and Inductive Predicates\<close>

thm lfp_fixpoint gfp_fixpoint
thm lfp_induct coinduct

inductive appends where
  appends_Nil[intro!]: "appends [] ys ys"
| appends_Cons[intro!]: "appends xs ys zs \<Longrightarrow> appends (x # xs) ys (x # zs)"

inductive_cases appends_NilE[elim!]: "appends [] ys zs"
inductive_cases appends_ConsE[elim!]: "appends (x # xs) ys zs"

thm appends.intros
thm appends.induct

lemma "appends [1, 2, 3] [4, 5] [1,2,3,4,5]"
  by (simp add: appends.intros(1) appends.intros(2))

lemma appends_eq_Nil: "appends xs ys zs \<Longrightarrow> xs = zs \<Longrightarrow> ys = []"
  apply (induct xs ys zs rule: appends.induct)
  subgoal for ys by simp
  subgoal for xs ys zs x by simp
  done

lemma appends_inject: "appends xs ys zs \<Longrightarrow> appends xs ys zs' \<Longrightarrow> zs = zs'"
  apply (induct xs ys zs arbitrary: zs' rule: appends.induct)
  subgoal for ys zs' by blast
  subgoal for xs yz zs x zs' by blast
  done

lemma appends_assoc:
  assumes "appends xs ys xys" "appends xys zs xyzs" "appends ys zs yzs"
  shows "appends xs yzs xyzs"
  using assms
  apply (induct xs ys xys arbitrary: zs yzs xyzs rule: appends.induct)
   apply (auto dest: appends_inject)
  done

thm appends_def[simplified]

definition "appends2 \<equiv>
  lfp (\<lambda>p as bs cs. as = [] \<and> bs = cs \<or>
                    (\<exists>xs ys zs x. as = x # xs \<and> bs = ys \<and> cs = x # zs \<and> p xs ys zs))"

lemma appends2_Nil: "appends2 [] ys ys"
  unfolding appends2_def
  apply (subst lfp_unfold)
  subgoal unfolding mono_def by (auto simp add: le_fun_def)
  subgoal
    apply (rule disjI1)
    apply blast
    done
  done

lemma appends2_Cons: "appends2 xs ys zs \<Longrightarrow> appends2 (x # xs) ys (x # zs)"
  apply (subst appends2_def)
  apply (subst lfp_unfold)
  subgoal unfolding mono_def by (auto simp add: le_fun_def)
  subgoal
    apply (subst appends2_def[symmetric])
    apply (rule disjI2)
    apply blast
    done
  done

lemma appends2_induct:
  "appends2 as bs cs \<Longrightarrow>
   (\<And>ys. P [] ys ys) \<Longrightarrow>
   (\<And>xs ys zs x. appends2 xs ys zs \<Longrightarrow> P xs ys zs \<Longrightarrow> P (x # xs) ys (x # zs)) \<Longrightarrow>
   P as bs cs"
  apply (subst (asm) appends2_def)
  apply (drule lfp_induct[where P = P, unfolded le_fun_def le_bool_def, rule_format, rotated -1])
  subgoal unfolding monotone_def by auto
  subgoal for xs ys zs
    apply (subst (asm) appends2_def[symmetric])
    apply (unfold inf_fun_def inf_bool_def)
    apply auto
    done
  subgoal by assumption
  done

text \<open>Take Home Message:
Knaster--Tarski least fixpoints have nice presentations as inductive predicates
\<close>

text \<open>Q: What about greatest fixed points? A: We need some infinite objects first.\<close>


section \<open>Coinductive datatypes\<close>

text \<open>\<nat> \<union> {\<infinity>}\<close>

codatatype enat = eZero | eSuc enat

primcorec infty where
  "infty = eSuc infty"

text \<open>Infinite sequences\<close>

codatatype stream = SCons (shd: nat) (stl: stream) (infixr ":::" 55)

text \<open>Other codatatypes\<close>

codatatype 'a llist = LNil | LCons (lshd: 'a) (lstl: "'a llist")
codatatype 'a btree = BNode 'a "'a btree" "'a btree"
codatatype 'a ftree = FNode 'a "'a ftree list"
codatatype 'a ctree = CNode 'a "'a ctree llist"
codatatype 'a utree = UNode 'a "'a ctree fset"
codatatype 'a delay = Now 'a | Later "'a delay"
codatatype lang = Lang (eps: bool) (delta: \<open>char \<Rightarrow> lang\<close>)

text \<open>Take Home Message:
Codatatypes [LICS'12, ITP'14] are potentially infinitely deep trees in all shapes and forms.
\<close>

text \<open>Back to infinite sequences\<close>

section \<open>Primitive Corecursion\<close>

(* Defining streams by primitive corecursion *)

primcorec zeros where "zeros = 0 ::: zeros"

primcorec "from" where "from n = n ::: from (n + 1)"

definition "nats = from 0"

fun stake where
  "stake 0 s = []"
| "stake (Suc n) s = shd s # stake n (stl s)"

code_lazy_type stream
value "nats"
value "stake 5 nats"

primcorec pls where
  "shd (pls s t) = shd s + shd t"
| "stl (pls s t) = pls (stl s) (stl t)"

value "stake 5 (pls nats nats)"

primrec shift where
  "shift [] s = s"
| "shift (x # xs) s = x ::: shift xs s"

lemma shift_append[simp]: "shift (xs @ ys) s = shift xs (shift ys s)"
  by (induct xs arbitrary: ys) auto

lemma shift_sel[simp]:
  "shd (shift xs s) = (case xs of [] \<Rightarrow> shd s | x # xs \<Rightarrow> x)"
  "stl (shift xs s) = (case xs of [] \<Rightarrow> stl s | x # xs \<Rightarrow> shift xs s)"
  by (cases xs; auto)+

primcorec even where "even s = shd s ::: even (stl (stl s))"

definition odd where "odd s = even (stl s)"

section \<open>Friendly Corecursion\<close>

primcorec zeros' where "zeros' = 0 ::: 0 ::: zeros'" (*fails*)

corec zeros' where "zeros' = 0 ::: 0 ::: zeros'"

lemma zeros'[simp]: "shd zeros' = 0" "stl (zeros') = 0 ::: zeros'"
  by (subst zeros'.code; auto)+

primcorec zip where "zip s t = shd s ::: shd t ::: zip (stl s) (stl t)" (*fails*)

corec zip where "zip s t = shd s ::: shd t ::: zip (stl s) (stl t)"

lemma zip_simps[simp]: "shd (zip s t) = shd s" "stl (zip s t) = shd t ::: zip (stl s) (stl t)"
  by (subst zip.code; auto)+

friend_of_corec pls where "pls s t = shd s + shd t ::: pls (stl s) (stl t)"
  by (rule pls.code) transfer_prover

primcorec shf where
  "shf s t = shd s * shd t ::: pls (shf (stl s) t) (shf s (stl t))" (*fails*)

corec (friend) shf where
  "shf s t = shd s * shd t ::: pls (shf (stl s) t) (shf s (stl t))"

lemma shf_simps[simp]:
  "shd (shf s t) = shd s * shd t"
  "stl (shf s t) = pls (shf (stl s) t) (shf s (stl t))"
  by (subst shf.code; auto)+

text \<open>Take Home Message:
Friends [ICFP'15, ESOP'17] overcome limitations of primitive corecursion.
\<close>

section \<open>Coinductive Proofs\<close>

thm stream.coinduct[where R = "in_rel {(pls zeros zeros, zeros)}"]

lemma "pls zeros zeros = zeros"
  by coinduction auto

lemma pls_zeros: "pls zeros s = s"
  by (coinduction arbitrary: s) auto

lemma pls_comm[ac_simps]: "pls s t = pls t s"
  by (coinduction arbitrary: s t) auto

lemma pls_assoc[ac_simps]: "pls (pls s t) u = pls s (pls t u)"
  by (coinduction arbitrary: s t u) auto

lemma pls_assoc_comm[ac_simps]: "pls s (pls t u) = pls t (pls s u)"
  by (metis pls_comm pls_assoc)

lemmas pls_ac_simps = pls_comm pls_assoc[symmetric] pls_assoc_comm

(*example 4*)
lemma "even nats = pls nats nats"
proof -
  have "even (from (2 * n)) = pls (from n) (from n)" for n
    by (coinduction arbitrary: n) (auto intro: exI[of _ "Suc _"])
  from this[of 0] show ?thesis unfolding nats_def by simp
qed

text \<open>Take Home Message:
stream coinduction is easy;
if your statement has free variables consider making them arbitrary
\<close>

primcorec "cst" where "cst n = n ::: cst n"
(*

primcorec iterate where
  "iterate f x = x ::: iterate f (f x)"

lemma from_iterate: "from n = iterate (\<lambda>x. x + 1) n"
  by (coinduction arbitrary: n) auto

lemma cst_iterate: "cst n = iterate id n"
  by (coinduction arbitrary: n) auto

(*2st definition*)

primcorec iterate' where
  "iterate' f x = x ::: (if x = f x then cst x else iterate' f (f x))"
thm iterate'_def[unfolded]

lemma iterate_cst: "x = f x \<Longrightarrow> iterate f x = cst x"
  by (coinduction arbitrary: f x) auto

lemma "iterate f x = iterate' f x"
  by (coinduction arbitrary: f x rule: stream.coinduct_strong)
     (auto simp: iterate_cst)

thm stream.coinduct_strong
*)
section \<open>Coinduction Up-To\<close>

lemma "zeros = zeros'"
  apply (rule zeros'.unique)
  apply (coinduction)
  apply (auto intro: zeros.code)
  done

thm stream.coinduct
thm stream.coinduct_upto
thm stream.cong_intros

lemma "zeros = zeros'"
  apply (coinduction rule: stream.coinduct_upto)
  apply simp
  apply (subst (2) zeros.code)
  apply (auto intro: stream.cong_intros)
  done

lemma "zip (even s) (odd s) = s"
  apply (coinduction arbitrary: s rule: stream.coinduct_upto)
  apply (subst (2) stream.collapse[of "stl _", symmetric])
  apply (auto intro: stream.cong_intros simp del: stream.collapse simp: odd_def)
    done

lemma pls_c0[simp]: "pls (cst 0) s = s"
  by (coinduction arbitrary: s) auto

lemma shf_c0[simp]: "shf (cst 0) s = cst 0"
  apply (coinduction arbitrary: s rule: stream.coinduct_upto)
  apply (unfold shf_simps)
  apply (rule conjI[rotated])
   apply (rule stream.cong_trans)
    apply (rule stream.cong_pls[OF stream.cong_base stream.cong_base])
     apply (auto simp: stream.cong_refl)
  done

lemma shf_comm: "shf s t = shf t s"
  apply (coinduction arbitrary: s t rule: stream.coinduct_upto)
  apply (unfold shf_simps)
  apply (subst pls_comm)
   apply (auto intro: stream.cong_intros)
  done

lemma shf_pls_distrib: "shf s (pls t u) = pls (shf s t) (shf s u)"
proof (coinduction arbitrary: s t u rule: stream.coinduct_upto)
  case Eq_stream
  let ?s = "stl s" and ?t = "stl t" and ?u = "stl u"
  define cong (infix "\<approx>" 50) where
    "cong = stream.v2.congclp (\<lambda>l r. \<exists>s t u. l = shf s (pls t u) \<and> r = pls (shf s t) (shf s u))"
  have "stl (shf s (pls t u)) = pls (shf ?s (pls t u)) (shf s (pls ?t ?u))"
    by simp
  also have "\<dots> \<approx> pls (pls (shf ?s t) (shf ?s u)) (pls (shf s ?t) (shf s ?u))"
    by (unfold cong_def, rule stream.cong_pls) (auto intro: stream.cong_base)
  also have "\<dots> = stl (pls (shf s t) (shf s u))"
    by (auto simp: ac_simps)
  finally show ?case
    unfolding cong_def by (auto simp: algebra_simps)
qed

lemma shf_pls_distrib2: "shf (pls t u) s = pls (shf t s) (shf u s)"
  by (metis shf_pls_distrib shf_comm)

lemma shf_assoc: "shf (shf s t) u = shf s (shf t u)"
  by (coinduction arbitrary: s t u rule: stream.coinduct_upto)
    (force simp: shf_pls_distrib shf_pls_distrib2 ac_simps intro: stream.cong_pls stream.cong_base)

text \<open>Take Home Message:
friendly corecursion requires coinduction up-to reasoning
\<close>

text \<open>Automation opportunity:
reasoning modulo equivalence/congruence relations.
\<close>

section \<open>Coinductive Languages\<close>

fun mem :: \<open>char list \<Rightarrow> lang \<Rightarrow> bool\<close> where
  \<open>mem [] L = eps L\<close>
| \<open>mem (a # w) L = mem w (delta L a)\<close>

declare lang.coinduct_strong[unfolded rel_fun_def, simplified, case_names Lang, coinduct pred]

thm lang.coinduct[unfolded rel_fun_def, simplified, case_names Lang, coinduct pred]

primcorec zer :: \<open>lang\<close> where
  \<open>zer = Lang False (\<lambda>_. zer)\<close>

abbreviation ife :: \<open>lang \<Rightarrow> lang \<Rightarrow> lang\<close> where
  \<open>ife L M \<equiv> (if eps L then M else zer)\<close>

corec (friend) alt :: \<open>lang \<Rightarrow> lang \<Rightarrow> lang\<close> where
  \<open>alt L M = Lang (eps L \<or> eps M) (\<lambda>a. alt (delta L a) (delta M a))\<close>

lemma pls_simps[simp]:
  \<open>eps (alt L M) = (eps L \<or> eps M)\<close> \<open>delta (alt L M) = (\<lambda>a. alt (delta L a) (delta M a))\<close>
  by (subst alt.code; auto)+

corec (friend) dot :: \<open>lang \<Rightarrow> lang \<Rightarrow> lang\<close> where
  \<open>dot L M = Lang (eps L \<and> eps M) (\<lambda>a. alt (dot (delta L a) M) (ife L (delta M a)))\<close>

lemma dot_simps[simp]:
  \<open>eps (dot L M) = (eps L \<and> eps M)\<close> \<open>delta (dot L M) = (\<lambda>a. alt (dot (delta L a) M) (ife L (delta M a)))\<close>
  by (subst dot.code; auto)+

corec (friend) str :: \<open>lang \<Rightarrow> lang\<close> where
  \<open>str L = Lang True (\<lambda>a. dot (delta L a) (str L))\<close>

lemma str_simps[simp]:
  \<open>eps (str L) = True\<close> \<open>delta (str L) = (\<lambda>a. dot (delta L a) (str L))\<close>
  by (subst str.code; auto)+

theorem alt_comm: \<open>alt L M = alt M L\<close>
  apply (coinduction arbitrary: L M)
  apply auto
  done

declare rel_fun_def[simp]

theorem alt_assoc: \<open>alt (alt L M) N = alt L (alt M N)\<close>
  by (coinduction arbitrary: L M N) auto

lemma alt_zerL[simp]: \<open>alt zer L = L\<close>
  by (coinduction arbitrary: L) simp

theorem alt_idem: \<open>alt L L = L\<close>
  by (coinduction arbitrary: L) auto

lemma alt_rotate: \<open>alt L (alt M N) = alt M (alt L N)\<close>
  using alt_assoc alt_comm by metis

lemma alt_idem_assoc: \<open>alt L (alt L M) = alt L M\<close>
  by (metis alt_assoc alt_idem)

lemmas alt_ACI[simp] =  alt_comm alt_assoc alt_idem alt_rotate alt_idem_assoc

theorem dot_altL[simp]: \<open>dot (alt L M) N = alt (dot L N) (dot M N)\<close>
  by (coinduction arbitrary: L M rule: lang.coinduct_upto)
    (auto intro: lang.cong_intros split: if_splits)

lemma dot_zerL[simp]: \<open>dot zer L = zer\<close>
  by (coinduction arbitrary: L) auto

theorem dot_assoc[simp]: \<open>dot (dot L M) N = dot L (dot M N)\<close>
  by (coinduction arbitrary: L M N rule: lang.coinduct_upto)
    (auto intro: lang.cong_intros intro!: lang.cong_alt[OF lang.cong_refl[OF refl]] split: if_splits)

lemma alt_zerR[simp]: \<open>alt L zer = L\<close>
  by (coinduction arbitrary: L) simp

theorem dot_altR[simp]: \<open>dot L (alt M N) = alt (dot L M) (dot L N)\<close>
  by (coinduction arbitrary: L rule: lang.coinduct_upto)
    (auto intro: lang.cong_intros split: if_splits)

coinductive leq where
  "(eps L \<Longrightarrow> eps M) \<Longrightarrow> (\<forall>c. leq (delta L c) (delta M c)) \<Longrightarrow> leq L M"

lemma leq_eq: \<open>leq L M \<Longrightarrow> M = alt L M\<close>
  by (coinduction arbitrary: L M) (auto elim: leq.cases)

lemma eq_leq: \<open>M = alt L M \<Longrightarrow> leq L M\<close>
  by (coinduction arbitrary: L M rule: leq.coinduct) (auto elim: ssubst)

lemma leq_iff_eq: \<open>leq L M \<longleftrightarrow> M = alt L M\<close>
  by (meson eq_leq leq_eq)

lemma \<open>leq L (alt L M)\<close>
  unfolding leq_iff_eq by simp

subsection \<open>Take Home Message:
What works for streams also works for languages!
\<close>

section \<open>Lazy Lists\<close>

primcorec lapp where
  "lapp xs ys = (case xs of LNil \<Rightarrow> ys | LCons x xs \<Rightarrow> LCons x (lapp xs ys))"

simps_of_case lapp_simps[simp]: lapp.code

(*useful simplification rules*)
thm lapp.simps[no_vars]

thm lapp_simps[no_vars]

(* coinduction theorem *)
thm llist.coinduct[no_vars]

lemma lapp_LNil2[simp]: "lapp xs LNil = xs"
by (coinduction arbitrary: xs) (auto split: llist.splits)

lemma lapp_append: "lapp (lapp xs ys) zs = lapp xs (lapp ys zs)"
  by (coinduction arbitrary: xs ys zs) (fastforce split: llist.splits intro: exI[of _ LNil])

coinductive linfinite where
  "linfinite xs \<Longrightarrow> linfinite (LCons x xs)"

lemma linfinite_lapp: "linfinite xs \<Longrightarrow> lapp xs ys = xs"
  by (coinduction arbitrary: xs) (auto elim: linfinite.cases)

inductive lfinite where
  "lfinite LNil"
| "lfinite xs \<Longrightarrow> lfinite (LCons x xs)"

lemma lfinite_imp_not_linfinite: "lfinite xs \<Longrightarrow> \<not> linfinite xs"
  by (induct xs rule: lfinite.induct) (auto elim: linfinite.cases)

lemma not_lfinite_imp_linfinite: "\<not> lfinite xs \<Longrightarrow> linfinite xs"
proof (coinduction arbitrary: xs)
  case (linfinite xs)
  then show ?case
    by (cases xs) (auto simp: lfinite.intros)
qed

lemma lfinite_iff_not_linfinite: "lfinite xs = (\<not> linfinite xs)"
  by (metis lfinite_imp_not_linfinite not_lfinite_imp_linfinite)

inductive lmem :: "'a \<Rightarrow> 'a llist \<Rightarrow> bool" where
  "lmem x (LCons x xs)"
| "lmem y xs \<Longrightarrow> lmem y (LCons x xs)"

lemma lmem_LNil[simp]: "lmem x LNil \<longleftrightarrow> False"
  by (auto elim: lmem.cases)

lemma lmem_LCons[simp]: "lmem y (LCons x xs) \<longleftrightarrow> y = x \<or> lmem y xs"
  by (auto elim: lmem.cases intro: lmem.intros)

lemma lset_lapp: "lmem x (lapp xs ys) = (if lfinite xs then lmem x xs \<or> lmem x ys else lmem x xs)"
proof (cases "lfinite xs")
  case True
  then show ?thesis
    by (induct xs rule: lfinite.induct) (auto simp: lfinite.intros)
next
  case False
  then show ?thesis
    by (simp add: lfinite_iff_not_linfinite linfinite_lapp)
qed

end