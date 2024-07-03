chapter \<open>Coinductive Reasoning in Isabelle/HOL\<close>

text \<open>
Dmitriy Traytel
University of Copenhagen

Disclaimer:
my presentation follows a chapter on coinductive methods
by Damien Pous and myself in the forthcoming book

Proof Assistants and Their Applications in Mathematics and Computer Science

(edited by Jasmin Blanchette and Assia Mahboubi)
\<close>

theory WAIT24
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

section \<open>Coinductive Datatypes\<close>

text \<open>\<nat> \<union> {\<infinity>}\<close>

codatatype enat = eZero | eSuc enat

primcorec infty where
  "infty = eSuc infty"


text \<open>Infinite sequences\<close>

codatatype stream = SCons (shd: nat) (stl: stream)                (infixr ":::" 55)


text \<open>Other codatatypes\<close>

codatatype 'a llist = LNil | LCons (lhd: 'a) (ltl: "'a llist")
codatatype 'a btree = BNode 'a "'a btree" "'a btree"
codatatype 'a ftree = FNode 'a "'a ftree list"
codatatype 'a ctree = CNode 'a "'a ctree llist"
codatatype 'a utree = UNode 'a "'a utree fset"
codatatype lang = Lang (eps: bool) (delta: \<open>char \<Rightarrow> lang\<close>)


text \<open>Take Home Message:
Codatatypes [LICS'12, ITP'14] are potentially infinitely deep trees in all shapes and forms.
\<close>

section \<open>Primitive Corecursion\<close>

primcorec zeros where "zeros = 0 ::: zeros"

primcorec "from" where "from n = n ::: from (n + 1)"

definition "nats = from 0"

fun stake where
  "stake 0 s = []"
| "stake (Suc n) s = shd s # stake n (stl s)"

code_lazy_type stream

value "shd (stl nats)"
value "stake 5 (from 6)"

primcorec pls where
  "shd (pls s t) = shd s + shd t"
| "stl (pls s t) = pls (stl s) (stl t)"
thm pls.ctr


primcorec pls' where
  "pls' s t = shd s + shd t ::: pls' (stl s) (stl t)"
thm pls'.sel

value "stake 5 (pls nats nats)"

fun shift where
  "shift [] s = s"
| "shift (x # xs) s = x ::: shift xs s"

lemma shift_append[simp]: "shift (xs @ ys) s = shift xs (shift ys s)"
  by (induct xs arbitrary: ys) auto

lemma shift_sel[simp]:
  "shd (shift xs s) = (case xs of [] \<Rightarrow> shd s | x # xs \<Rightarrow> x)"
  "stl (shift xs s) = (case xs of [] \<Rightarrow> stl s | x # xs \<Rightarrow> shift xs s)"
  by (cases xs; auto)+

primcorec even where "even s = shd s ::: even (stl (stl s))"

value "stake 5 (even nats)"

definition odd where "odd s = even (stl s)"

value "stake 5 (odd nats)"

section \<open>Friendly Corecursion\<close>

corec zeros' where "zeros' = 0 ::: 0 ::: zeros'"

lemma zeros'[simp]: "shd zeros' = 0" "stl (zeros') = 0 ::: zeros'"
  by (subst zeros'.code; auto)+

corec zip where "zip s t = shd s ::: shd t ::: zip (stl s) (stl t)"

lemma zip_simps[simp]: "shd (zip s t) = shd s" "stl (zip s t) = shd t ::: zip (stl s) (stl t)"
  by (subst zip.code; auto)+

friend_of_corec pls where "pls s t = shd s + shd t ::: pls (stl s) (stl t)"
  by (rule pls.code) transfer_prover

corec shf where
  "shf s t = shd s * shd t ::: pls (shf (stl s) t) (shf s (stl t))" (*fails*)

lemma shf_simps[simp]:
  "shd (shf s t) = shd s * shd t"
  "stl (shf s t) = pls (shf (stl s) t) (shf s (stl t))"
  by (subst shf.code; auto)+

text \<open>Take Home Message:
Friends [ICFP'15, ESOP'17] overcome limitations of primitive corecursion.
\<close>

section \<open>Coinductive Proofs\<close>

thm stream.coinduct[no_vars]

lemma "pls zeros zeros = zeros"
  by coinduction auto

lemma pls_zeros: "pls zeros s = s"
  apply (coinduction arbitrary: s)
  apply auto
  done

lemma pls_comm[ac_simps]: "pls s t = pls t s"
  by (coinduction arbitrary: s t) auto

lemma pls_assoc[ac_simps]: "pls (pls s t) u = pls s (pls t u)"
  by (coinduction arbitrary: s t u) auto

lemma pls_assoc_comm[ac_simps]: "pls s (pls t u) = pls t (pls s u)"
  by (metis pls_comm pls_assoc)

lemmas pls_ac_simps = pls_comm pls_assoc[symmetric] pls_assoc_comm

text \<open>Take Home Message:
stream coinduction is easy;
if your statement has free variables consider making them arbitrary
\<close>
thm lfp_induct coinduct
section \<open>Coinduction Up-To\<close>
thm stream.coinduct_upto
thm stream.cong_intros
lemma "zeros = zeros'"

  apply (coinduction rule: stream.coinduct_upto)
  apply simp
  apply (subst (2) zeros.code)
  apply (auto intro: stream.cong_intros)
  done

text \<open>Take Home Message:
friendly corecursion requires coinduction up-to reasoning
\<close>

text \<open>Automation opportunity:
reasoning modulo equivalence/congruence relations.
\<close>
(*
  apply (rule stream.coinduct_upto[where R="in_rel {(zeros, zeros')}"])
   apply simp_all
  apply (subst (2) zeros.ctr)
  apply (simp add: stream.cong_intros)
  done
*)

section \<open>Coinductive Languages\<close>
section \<open>Lazy Lists\<close>
