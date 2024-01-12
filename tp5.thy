theory tp5
  imports Main tp2 "~~/src/HOL/Library/Code_Target_Nat"
begin

type_synonym address= "nat*nat*nat*nat"
datatype rule= Drop "(address list)" | Accept "(address list)" 
type_synonym chain= "rule list"

definition "aChain1= [(Drop [(1,1,1,1)]),(Accept [(1,1,1,1),(2,2,2,2)])]"
definition "aChain2= [(Accept [(1,1,1,1),(2,2,2,2)]),(Drop [(1,1,1,1)])]"

(* ---------   This is the TRUSTED BASE! So do not modify those two functions! ------------ *)
(* But, you SHOULD carefully read their code to understand how chains are used *)

(* The function defining if an address is accepted by a chain *)
fun filter:: "address \<Rightarrow> chain \<Rightarrow> bool"
  where
"filter a [] = False" |
"filter a ((Accept al)#r) = (if (List.member al a) then True else (filter a r))"|
"filter a ((Drop al)#r) = (if (List.member al a) then False else (filter a r))" 

value "accept (1,1,1,1) aChain1"
value "accept (1,1,1,1) aChain2"
value "accept (2,2,2,2) aChain1"
value "accept (2,2,2,2) aChain2"

(* ------------------------------------------------------------------------------------------ *)

(* The function/predicate to program and to prove! *)

(* -- function to get the set difference operation A - B -- *)
fun set_difference :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where 
  "set_difference [] _ = []" |
  "set_difference (x#xs) s2 = 
    (if (List.member s2 x) then (set_difference xs s2) else (x#(set_difference xs s2)) )"

(* the 2 lemmas proving this function works as intended *)
lemma set_diff_works:
  "\<forall> x::'a. (List.member s2 x) \<longrightarrow> \<not>(List.member (set_difference s1 s2) x)"
  apply (induct s1)
      apply simp
  apply auto
  done

lemma x_in_set_diff:
  "List.member (set_difference s1 s2) x \<longrightarrow> List.member s1 x"
  apply (induct s1)
   apply auto
  done

(* another small lemma to be sure *)
lemma not_in_s2:
  "(List.member s1 x) \<and> \<not>(List.member s2 x) \<longleftrightarrow> List.member (set_difference s1 s2) x"
  apply (induct s1)
   apply auto
  done

(* lemma stating that if A is a set, then the output will always be a set  *)
lemma set_diff_set: 
  "(isSet s1) \<longrightarrow> isSet (set_difference s1 s2)" 
  apply (induct s1)
  (* s1 = [] *) apply simp
  using x_in_set_diff by force


(* ---- function used to get the set of accepted addresses by given chain ---- *)

(* the idea is that as unspecified addresses are rejected, we can simplify 
  the chain and find out directly the list of accepted addresses. *)
fun find_accepted_set :: "chain \<Rightarrow> address list"
  where
  "find_accepted_set [] = []" |
  "find_accepted_set ((Drop l) # cs) = set_difference (find_accepted_set cs) l " |
  "find_accepted_set ((Accept l) # cs) = clean (l @ (find_accepted_set cs))"

(* lemma stating that the result of the function is always a set. *)
lemma find_is_set:
  "isSet (find_accepted_set c)"
  apply (induct c)
   apply simp (* c = [] *)
  apply (case_tac a)
   apply clarify (* Drop *)
   apply (simp add:set_diff_set) 
  apply simp by (metis clean_isSet)

(* -- lemmas stating proving find_accepted_set_works -- *)

lemma find_set_works_impl:
  "\<forall> x. (filter x c) \<longrightarrow> (List.member (find_accepted_set c) x)"
  apply (induct c)
   apply simp (* c = [] *)
  apply (case_tac a) (* true for c, see for a # c *)
   apply (rename_tac l)
   apply (simp add: not_in_s2)
  apply (rename_tac l)
   apply (meson not_in_s2)
  by (metis Un_iff find_accepted_set.simps(3) in_set_member member_clean set_append tp5.filter.simps(2))

lemma find_set_works_rev_impl:
  "\<forall> x. (List.member (find_accepted_set c) x) \<longrightarrow>  (filter x c)"
  apply (induct c)
   apply simp
  apply (case_tac a)
    using not_in_s2 apply fastforce
  by (metis Un_iff find_accepted_set.simps(3) in_set_member member_clean set_append tp5.filter.simps(2))

(* ~~~~  proof that find_accepted_set works ! ~~~~ *)
lemma find_set_works:
  "\<forall> x. (List.member (find_accepted_set c) x) = (filter x c)"
  using find_set_works_impl find_set_works_rev_impl by blast

(* ---- Equal function ---- *)
fun equal :: "chain \<Rightarrow> chain \<Rightarrow> bool"
  where
  "equal c1 c2 = (tp2.equal ((find_accepted_set c1)) ( (find_accepted_set c2)) )"

(* lemmas to prove equal true *)
lemma eq_filter_sets_impl:
  "\<forall> c1 c2.  
  (\<forall> x. filter x c1 = filter x c2)
  \<longrightarrow> (tp2.equal (find_accepted_set c1) (find_accepted_set c2) )"
  by (simp add: find_is_set find_set_works lem_inclu_2)

lemma eq_filter_impl:
  "\<forall> c1 c2. (\<forall> x. filter x c1 = filter x c2)
  \<longrightarrow> ( tp5.equal c1 c2 )"
  using eq_filter_sets_impl apply simp
  done

(* rev impl *)

lemma eq_all_rev_impl:
  "\<forall> c1 c2. (tp5.equal c1 c2)
  \<longrightarrow> (\<forall> x. List.member (find_accepted_set c1) x = List.member (find_accepted_set c2) x)"
  using equal_set find_is_set by auto

lemma eq_find_rev_impl:
  "\<forall> c1 c2. (tp5.equal c1 c2)
  \<longrightarrow> (tp2.equal (find_accepted_set c1) (find_accepted_set c2) )"
  using equal_set find_is_set by auto

lemma eq_filter_rev_impl:
  "\<forall> c1 c2. (tp5.equal c1 c2)
  \<longrightarrow> (\<forall> x. (filter x c1) = (filter x c2) )"
  using eq_all_rev_impl find_set_works by blast

(* ~~~~ final lemma proving equal works ! ! ~~~~ *)
lemma equal_works:
  "\<forall> c1 c2. ( tp5.equal c1 c2 \<longleftrightarrow> (\<forall> x. filter x c1 = filter x c2) )"
  using eq_filter_impl eq_filter_rev_impl by blast

(* Code exportation directive *)
export_code equal in Scala
end