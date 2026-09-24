theory Semantics
  imports Compile
begin

section \<open>Semantic values and environments\<close>

datatype sem_value =
    SUndefined
  | SBool bool
  | SInt int
  | SReal real
  | SString string
  | SObject oid
  | SCollection "sem_value list"

type_synonym sem_env = "(vname \<times> sem_value) list"

fun sem_lookup :: "sem_env \<Rightarrow> vname \<Rightarrow> sem_value" where
  "sem_lookup [] x = SUndefined"
| "sem_lookup ((y,v)#\<rho>) x = (if x = y then v else sem_lookup \<rho> x)"

primrec sem_unary :: "ocl_unop \<Rightarrow> sem_value \<Rightarrow> sem_value" where
  "sem_unary UNot v = (case v of SBool b \<Rightarrow> SBool (\<not> b) | _ \<Rightarrow> SUndefined)"
| "sem_unary UNeg v =
     (case v of SInt i \<Rightarrow> SInt (-i) | SReal r \<Rightarrow> SReal (-r)
      | _ \<Rightarrow> SUndefined)"
| "sem_unary UIsUndefined v = SBool (v = SUndefined)"
| "sem_unary USize v =
     (case v of SCollection xs \<Rightarrow> SInt (int (length xs)) | _ \<Rightarrow> SUndefined)"
| "sem_unary UIsEmpty v =
     (case v of SCollection xs \<Rightarrow> SBool (xs = []) | _ \<Rightarrow> SUndefined)"
| "sem_unary UNotEmpty v =
     (case v of SCollection xs \<Rightarrow> SBool (xs \<noteq> []) | _ \<Rightarrow> SUndefined)"
| "sem_unary USum v = SUndefined"

primrec sem_binary :: "ocl_binop \<Rightarrow> sem_value \<Rightarrow> sem_value \<Rightarrow> sem_value" where
  "sem_binary BAnd a b =
     (case (a,b) of (SBool x,SBool y) \<Rightarrow> SBool (x \<and> y) | _ \<Rightarrow> SUndefined)"
| "sem_binary BOr a b =
     (case (a,b) of (SBool x,SBool y) \<Rightarrow> SBool (x \<or> y) | _ \<Rightarrow> SUndefined)"
| "sem_binary BImplies a b =
     (case (a,b) of (SBool x,SBool y) \<Rightarrow> SBool (x \<longrightarrow> y) | _ \<Rightarrow> SUndefined)"
| "sem_binary BEq a b = SBool (a = b)"
| "sem_binary BNeq a b = SBool (a \<noteq> b)"
| "sem_binary BLt a b =
     (case (a,b) of (SInt x,SInt y) \<Rightarrow> SBool (x < y) | _ \<Rightarrow> SUndefined)"
| "sem_binary BLe a b =
     (case (a,b) of (SInt x,SInt y) \<Rightarrow> SBool (x \<le> y) | _ \<Rightarrow> SUndefined)"
| "sem_binary BGt a b =
     (case (a,b) of (SInt x,SInt y) \<Rightarrow> SBool (x > y) | _ \<Rightarrow> SUndefined)"
| "sem_binary BGe a b =
     (case (a,b) of (SInt x,SInt y) \<Rightarrow> SBool (x \<ge> y) | _ \<Rightarrow> SUndefined)"
| "sem_binary BAdd a b =
     (case (a,b) of (SInt x,SInt y) \<Rightarrow> SInt (x + y) | _ \<Rightarrow> SUndefined)"
| "sem_binary BSub a b =
     (case (a,b) of (SInt x,SInt y) \<Rightarrow> SInt (x - y) | _ \<Rightarrow> SUndefined)"
| "sem_binary BMul a b =
     (case (a,b) of (SInt x,SInt y) \<Rightarrow> SInt (x * y) | _ \<Rightarrow> SUndefined)"

fun sem_select :: "sem_value list \<Rightarrow> (sem_value \<Rightarrow> sem_value) \<Rightarrow> sem_value list" where
  "sem_select [] f = []"
| "sem_select (x#xs) f =
     (if f x = SBool True then x # sem_select xs f else sem_select xs f)"

fun sem_forall :: "sem_value list \<Rightarrow> (sem_value \<Rightarrow> sem_value) \<Rightarrow> sem_value" where
  "sem_forall [] f = SBool True"
| "sem_forall (x#xs) f =
     (if f x = SBool True then sem_forall xs f
      else if f x = SBool False then SBool False
      else SUndefined)"

fun sem_exists :: "sem_value list \<Rightarrow> (sem_value \<Rightarrow> sem_value) \<Rightarrow> sem_value" where
  "sem_exists [] f = SBool False"
| "sem_exists (x#xs) f =
     (if f x = SBool True then SBool True
      else if f x = SBool False then sem_exists xs f
      else SUndefined)"

section \<open>Independent Core and graph-query evaluators\<close>

text \<open>
  Attribute, navigation and extent lookup are parameters.  The source
  instantiation reads a snapshot; the target instantiation reads a property
  graph.  Keeping these observations independent prevents the correctness
  theorem from becoming true by definition.
\<close>

primrec eval_core ::
  "(oid \<Rightarrow> cname \<times> aname \<Rightarrow> sem_value) \<Rightarrow>
   (oid \<Rightarrow> nav_ref \<Rightarrow> sem_value list) \<Rightarrow>
   (cname \<Rightarrow> sem_value list) \<Rightarrow>
   oid \<Rightarrow> sem_env \<Rightarrow> core_expr \<Rightarrow> sem_value" where
  "eval_core A N X s \<rho> (CBool b) = SBool b"
| "eval_core A N X s \<rho> (CInt i) = SInt i"
| "eval_core A N X s \<rho> (CReal r) = SReal r"
| "eval_core A N X s \<rho> (CString x) = SString x"
| "eval_core A N X s \<rho> (CSelf c) = SObject s"
| "eval_core A N X s \<rho> (CVar x) = sem_lookup \<rho> x"
| "eval_core A N X s \<rho> (CLet x e b) =
     eval_core A N X s ((x, eval_core A N X s \<rho> e)#\<rho>) b"
| "eval_core A N X s \<rho> (CIf c t e) =
     (case eval_core A N X s \<rho> c of
        SBool True \<Rightarrow> eval_core A N X s \<rho> t
      | SBool False \<Rightarrow> eval_core A N X s \<rho> e
      | _ \<Rightarrow> SUndefined)"
| "eval_core A N X s \<rho> (CAttr e ak) =
     (case eval_core A N X s \<rho> e of SObject i \<Rightarrow> A i ak | _ \<Rightarrow> SUndefined)"
| "eval_core A N X s \<rho> (CNavOne e n) =
     (case eval_core A N X s \<rho> e of
        SObject i \<Rightarrow> (case N i n of [v] \<Rightarrow> v | _ \<Rightarrow> SUndefined)
      | _ \<Rightarrow> SUndefined)"
| "eval_core A N X s \<rho> (CNavMany k e n) =
     (case eval_core A N X s \<rho> e of
        SObject i \<Rightarrow> SCollection (N i n) | _ \<Rightarrow> SUndefined)"
| "eval_core A N X s \<rho> (CScan c) = SCollection (X c)"
| "eval_core A N X s \<rho> (CUnary op e) = sem_unary op (eval_core A N X s \<rho> e)"
| "eval_core A N X s \<rho> (CBinary op a b) =
     sem_binary op (eval_core A N X s \<rho> a) (eval_core A N X s \<rho> b)"
| "eval_core A N X s \<rho> (CSelect src x b) =
     (case eval_core A N X s \<rho> src of
        SCollection xs \<Rightarrow>
          SCollection (sem_select xs (\<lambda>v. eval_core A N X s ((x,v)#\<rho>) b))
      | _ \<Rightarrow> SUndefined)"
| "eval_core A N X s \<rho> (CCollect src x b) =
     (case eval_core A N X s \<rho> src of
        SCollection xs \<Rightarrow>
          SCollection (map (\<lambda>v. eval_core A N X s ((x,v)#\<rho>) b) xs)
      | _ \<Rightarrow> SUndefined)"
| "eval_core A N X s \<rho> (CForAll src x b) =
     (case eval_core A N X s \<rho> src of
        SCollection xs \<Rightarrow> sem_forall xs (\<lambda>v. eval_core A N X s ((x,v)#\<rho>) b)
      | _ \<Rightarrow> SUndefined)"
| "eval_core A N X s \<rho> (CExists src x b) =
     (case eval_core A N X s \<rho> src of
        SCollection xs \<Rightarrow> sem_exists xs (\<lambda>v. eval_core A N X s ((x,v)#\<rho>) b)
      | _ \<Rightarrow> SUndefined)"

primrec eval_query ::
  "(oid \<Rightarrow> property_key \<Rightarrow> sem_value) \<Rightarrow>
   (oid \<Rightarrow> query_nav \<Rightarrow> sem_value list) \<Rightarrow>
   (graph_label \<Rightarrow> sem_value list) \<Rightarrow>
   oid \<Rightarrow> sem_env \<Rightarrow> q_expr \<Rightarrow> sem_value" where
  "eval_query A N X s \<rho> (QBool b) = SBool b"
| "eval_query A N X s \<rho> (QInt i) = SInt i"
| "eval_query A N X s \<rho> (QReal r) = SReal r"
| "eval_query A N X s \<rho> (QString x) = SString x"
| "eval_query A N X s \<rho> QSelf = SObject s"
| "eval_query A N X s \<rho> (QVar x) = sem_lookup \<rho> x"
| "eval_query A N X s \<rho> (QLet x e b) =
     eval_query A N X s ((x, eval_query A N X s \<rho> e)#\<rho>) b"
| "eval_query A N X s \<rho> (QIf c t e) =
     (case eval_query A N X s \<rho> c of
        SBool True \<Rightarrow> eval_query A N X s \<rho> t
      | SBool False \<Rightarrow> eval_query A N X s \<rho> e
      | _ \<Rightarrow> SUndefined)"
| "eval_query A N X s \<rho> (QProperty e k) =
     (case eval_query A N X s \<rho> e of SObject i \<Rightarrow> A i k | _ \<Rightarrow> SUndefined)"
| "eval_query A N X s \<rho> (QNavOne e n) =
     (case eval_query A N X s \<rho> e of
        SObject i \<Rightarrow> (case N i n of [v] \<Rightarrow> v | _ \<Rightarrow> SUndefined)
      | _ \<Rightarrow> SUndefined)"
| "eval_query A N X s \<rho> (QNavMany e n) =
     (case eval_query A N X s \<rho> e of
        SObject i \<Rightarrow> SCollection (N i n) | _ \<Rightarrow> SUndefined)"
| "eval_query A N X s \<rho> (QScan l) = SCollection (X l)"
| "eval_query A N X s \<rho> (QUnary op e) = sem_unary op (eval_query A N X s \<rho> e)"
| "eval_query A N X s \<rho> (QBinary op a b) =
     sem_binary op (eval_query A N X s \<rho> a) (eval_query A N X s \<rho> b)"
| "eval_query A N X s \<rho> (QFilter src x b) =
     (case eval_query A N X s \<rho> src of
        SCollection xs \<Rightarrow>
          SCollection (sem_select xs (\<lambda>v. eval_query A N X s ((x,v)#\<rho>) b))
      | _ \<Rightarrow> SUndefined)"
| "eval_query A N X s \<rho> (QCollect src x b) =
     (case eval_query A N X s \<rho> src of
        SCollection xs \<Rightarrow>
          SCollection (map (\<lambda>v. eval_query A N X s ((x,v)#\<rho>) b) xs)
      | _ \<Rightarrow> SUndefined)"
| "eval_query A N X s \<rho> (QForAll3 src x b) =
     (case eval_query A N X s \<rho> src of
        SCollection xs \<Rightarrow> sem_forall xs (\<lambda>v. eval_query A N X s ((x,v)#\<rho>) b)
      | _ \<Rightarrow> SUndefined)"
| "eval_query A N X s \<rho> (QExists3 src x b) =
     (case eval_query A N X s \<rho> src of
        SCollection xs \<Rightarrow> sem_exists xs (\<lambda>v. eval_query A N X s ((x,v)#\<rho>) b)
      | _ \<Rightarrow> SUndefined)"

section \<open>Semantic preservation of lowering\<close>

locale adequate_observations =
  fixes \<Sigma> :: rep_spec
    and source_attr :: "oid \<Rightarrow> cname \<times> aname \<Rightarrow> sem_value"
    and source_nav :: "oid \<Rightarrow> nav_ref \<Rightarrow> sem_value list"
    and source_scan :: "cname \<Rightarrow> sem_value list"
    and graph_attr :: "oid \<Rightarrow> property_key \<Rightarrow> sem_value"
    and graph_nav :: "oid \<Rightarrow> query_nav \<Rightarrow> sem_value list"
    and graph_scan :: "graph_label \<Rightarrow> sem_value list"
  assumes attr_adequate:
      "graph_attr i (sigma_attr_key \<Sigma> ak) = source_attr i ak"
    and nav_adequate:
      "graph_nav i (lower_nav \<Sigma> n k) = source_nav i n"
    and scan_adequate:
      "graph_scan (sigma_class_label \<Sigma> c) = source_scan c"
begin

theorem lower_expr_semantic_preservation:
  "eval_query graph_attr graph_nav graph_scan self \<rho> (lower_expr \<Sigma> e) =
   eval_core source_attr source_nav source_scan self \<rho> e"
proof (induction e arbitrary: self \<rho>)
  case (CAttr e ak)
  then show ?case by (simp add: attr_adequate split: sem_value.splits)
next
  case (CNavOne e n)
  then show ?case by (simp add: nav_adequate split: sem_value.splits list.splits)
next
  case (CNavMany k e n)
  then show ?case by (simp add: nav_adequate split: sem_value.splits)
next
  case (CScan c)
  then show ?case by (simp add: scan_adequate)
qed (simp_all split: sem_value.splits list.splits bool.splits)

definition core_violations :: "core_invariant \<Rightarrow> oid set \<Rightarrow> oid set" where
  "core_violations CI context =
     {i \<in> context.
       eval_core source_attr source_nav source_scan i [] (core_inv_body CI)
         \<noteq> SBool True}"

definition query_violations :: "graph_query \<Rightarrow> oid set \<Rightarrow> oid set" where
  "query_violations q context =
     {i \<in> context.
       eval_query graph_attr graph_nav graph_scan i [] (query_predicate q)
         \<noteq> SBool True}"

theorem lower_invariant_preserves_violations:
  assumes "graph_context = source_context"
  shows "query_violations (lower_invariant \<Sigma> CI) graph_context =
         core_violations CI source_context"
  using assms lower_expr_semantic_preservation
  unfolding query_violations_def core_violations_def lower_invariant_def by auto

definition ocl_violations ::
  "ocl_model \<Rightarrow> ocl_invariant \<Rightarrow> oid set \<Rightarrow> oid set" where
  "ocl_violations M I context =
     (case front M I of
        None \<Rightarrow> {}
      | Some CI \<Rightarrow> core_violations CI context)"

theorem compile_invariant_preserves_violations:
  assumes COMPILE: "compile_invariant \<Sigma> M I = Some q"
      and CONTEXT: "graph_context = source_context"
  shows "query_violations q graph_context =
         ocl_violations M I source_context"
proof -
  obtain CI where FRONT: "front M I = Some CI"
      and Q: "q = lower_invariant \<Sigma> CI"
    using compile_success_is_lowered_front[OF COMPILE] by blast
  have "query_violations (lower_invariant \<Sigma> CI) graph_context =
        core_violations CI source_context"
    using lower_invariant_preserves_violations[OF CONTEXT] .
  with FRONT Q show ?thesis
    unfolding ocl_violations_def by simp
qed

theorem transformation_correct_pointwise:
  assumes "compile_invariant \<Sigma> M I = Some q"
      and "graph_context = source_context"
      and "i \<in> source_context"
  shows "i \<in> ocl_violations M I source_context \<longleftrightarrow>
         i \<in> query_violations q graph_context"
  using compile_invariant_preserves_violations[OF assms(1,2)] by blast

end

end
