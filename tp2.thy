theory tp2
imports Main
begin

fun member::"'a \<Rightarrow> 'a list \<Rightarrow> bool"
  where
  "member x l = List.member l x"

declare List.member_rec[simp]

(** Question 1 **)

fun isSet::"'a list \<Rightarrow> bool"
  where
  "isSet [] = True" |
  "isSet (x#xs) = ((\<not>(List.member xs x)) \<and> (isSet xs))"

fun clean::"'a list \<Rightarrow> 'a list"
  where
  "clean [] = []" |
  "clean (x#xs) = (if (List.member xs x) then (clean xs) else (x#(clean xs)))"

lemma member_clean: "(List.member l x) = (List.member (clean l) x)"
  apply (induct l)
   (* l = [] *) apply simp
   (* l = Cons x xs *) apply (case_tac "a = x")
      (* a = x *) apply simp
      (* a != x *) apply simp
  done

lemma clean_isSet: "isSet (clean l)"
  (* using [[simp_trace=true]] *)
  apply (induct l)
   (* l = [] *) apply simp 
   (* l = Cons x xs *) apply simp by (metis member_clean)


(** Question 2 **)
fun delete::"'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
  "delete _ [] = []" |
  "delete a (x#xs) = (if (x = a) then xs else (x#(delete a xs)))"

fun deleteAll::"'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
  "deleteAll _ [] = []" |
  "deleteAll y (x#xs) = (if (y = x) then (deleteAll y xs) else (x#(deleteAll y xs)))"

lemma delete_set_member:"( (isSet l) \<and> (List.member l x)) 
     \<longrightarrow> (\<not>(List.member (delete x l) x))"
  apply (induct l)
  (* l = [] *) apply simp
  (* l = Cons x xs *) apply simp
  done

lemma deleteAll_works:"(\<not>(List.member (deleteAll x l1) x))"
  apply (induct l1)
    (* l = Nil *) apply simp
    (* l = Cons x xs *) apply auto (* whyyyyy ? ? ? *) 
  done

(** Question 3 **)

fun intersection::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
  "intersection [] _ = []" |
  "intersection (x#xs) l = (if (List.member l x) then (x # (intersection xs l)) else (intersection xs l))"

lemma intersection_x_x:"(((List.member l1 x) \<and> (List.member l2 x)) = (List.member (intersection l1 l2) x))"
  apply (induct l1)
    (* l1 = Nil *) apply simp
    (* l1 = Cons x xs *) apply auto (* ? ? ? *)
  done

lemma intersection_isSet:"((isSet l1) \<and> (isSet l2)) \<longrightarrow> (isSet (intersection l1 l2))"
  apply (induct l1)
    (* [] *) apply simp
    (* x xs *) apply simp by (metis intersection_x_x)

(** Question 4 **)
(*4 - UNION*)
fun union::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
"union [] E2 = E2"|
"union (x#x1) e2 = (if List.member e2 x then union x1 e2 else (x#(union x1 e2)))"

(*Prop entre member & union :*)
lemma member_union:"List.member (union E1 E2) x = (List.member E1 x \<or> List.member E2 x)"
  apply (induct E1)
   apply simp
  apply auto
  done

(*union satisfait le prédicat isSet*)
lemma isSet_union:"(isSet E1 \<and> isSet E2) \<Longrightarrow> isSet (union E1 E2)"
  apply (induct E1)
   apply simp
  apply simp
  by (metis member_union)

lemma union_x_or_x:"List.member (union l1 l2) x = (List.member l1 x \<or> List.member l2 x)"
  apply (induct l1)
    (* l1 = Nil *) apply simp (* (simp add:mon_lemme) *)
    (* l1 = Cons x xs *) apply auto (* ? ? ? *)
  done

fun inclusion::"'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
  "inclusion [] _ = True" |
  "inclusion (x#xs) l2 = (if (List.member l2 x) then (inclusion xs l2) else False)"

lemma lem_inclu:
  "(isSet l1 \<and> isSet l2) 
  \<longrightarrow> (inclusion l1 l2) 
  \<longleftrightarrow> (\<forall> x. (List.member l1 x) \<longrightarrow> (List.member l2 x))" 
  apply (induct l1)
  (* l1 = [] *) apply simp
  (* l1 = Cons x xs *) apply auto
  done

lemma lem_inclu_2:
  "\<forall> l1 l2. (isSet l1 \<and> isSet l2)
  \<longrightarrow> (\<forall> x. (List.member l1 x = List.member l2 x))
  \<longrightarrow> (inclusion l1 l2 \<and> inclusion l2 l1)"
  by (simp add: lem_inclu)

(** Question 5 **)

fun equal::"'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
  "equal l1 l2 = ((inclusion l1 l2) \<and> (inclusion l2 l1))"

lemma equal_set:
  "(isSet l1 \<and> isSet l2)
  \<longrightarrow> ( (\<forall>x.(List.member l1 x = List.member l2 x)) = (equal l1 l2))"
  using lem_inclu by auto

end