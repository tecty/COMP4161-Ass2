theory a2
imports Main
begin

section "Part 1"

datatype condition =
  Above nat nat | Joinable nat nat

inductive_set connection :: "condition set \<Rightarrow> condition set"
  for A :: "condition set" where
  con_refl:
    "Above a a \<in> connection A"
| con_in:
    "\<phi> \<in> A \<Longrightarrow> \<phi> \<in> connection A"
| con_mirror:
    "Joinable a b \<in> connection A
     \<Longrightarrow> Joinable b a \<in> connection A"
| con_trans:
    "\<lbrakk>Above a b \<in> connection A;
      Above b c \<in> connection A\<rbrakk>
     \<Longrightarrow> Above a c \<in> connection A"
| con_join:
    "\<lbrakk>Above a b \<in> connection A;
      Above c b \<in> connection A\<rbrakk>
     \<Longrightarrow> Joinable a c \<in> connection A"
| con_ext_join:
    "\<lbrakk>Above a b \<in> connection A;
      Joinable b c \<in> connection A\<rbrakk>
     \<Longrightarrow> Joinable a c \<in> connection A"

primrec is_refl :: "_" where
  "is_refl(Above a b) = (a = b)"
| "is_refl(Joinable a b) = (a = b)"

section "Question 1 (a)"

definition router1 
  where "router1= 0"
definition router2 
  where "router2= 1"
definition computer1 
  where "computer1= 2"
definition computer2 
  where "computer2= 3"
definition computer3 
  where "computer3= 4"

definition example_network where
"example_network = {
  Above computer1 router1, Above  computer2 router1, 
  Above computer2 router1, Above  computer3 router2}"

lemma "Joinable computer1 computer2 \<in> connection example_network"
  apply (unfold example_network_def)
  apply (rule_tac b=router1 in con_join)
   apply (rule con_in, blast) +
  done

subsection "Questions 1 (b)-(j)"

(* 1-b *)
lemma connection_monotonic:
  assumes "\<phi> \<in> connection A"
  shows   "\<phi> \<in> connection(A \<union> B)"
  using assms
  apply (induct)
  by (simp_all add:connection.intros)
  

(* 1-c *)
lemma connection_monotonic_simp:
  "connection A \<subseteq> connection (A \<union> B)"
  using connection_monotonic 
  by blast

lemma connection_idem:
  shows "connection(connection A) = connection A"
  apply safe
   apply (erule connection.induct)
  by (auto intro:connection.intros)
  

(* 1-d *)
lemma connection_decompose:
  assumes "\<phi> \<in> connection(A \<union> B)"
  shows   "\<exists>C D. C \<subseteq> connection A \<and>
                 D \<subseteq> connection B \<and>
                 \<phi> \<in> connection(C \<union> D)"
  using assms
  using connection_monotonic_simp connection_idem 
  by (meson connection.con_in subsetI)

(* 1-e *)
lemma connection_nil:
  assumes "\<phi> \<in> connection {}"
  shows "is_refl \<phi>"
  apply (rule connection.induct)
        apply (simp_all)
  using assms by blast+

(* 1-f *)
lemma join_refl: "Joinable a a \<in> connection A"
  apply (rule_tac b="a" in con_join) 
  by (rule con_refl)+

lemma con_is_refl:
  assumes "is_refl \<phi>"
  shows "\<phi> \<in> connection A"
  using assms 
  apply (unfold is_refl_def)
  apply induct
   apply simp_all
   apply (rule con_refl)
  apply (rule join_refl)
  done

(* 1-g *)  
lemma connection_filter_refl:
  assumes "\<phi> \<in> connection A"
  shows "\<phi> \<in> connection(A - {\<phi>. is_refl \<phi>})"
  using assms
  using con_is_refl
  apply induct
  apply (simp_all add:connection.intros)
  by (metis DiffI connection.con_in mem_Collect_eq)
  
(* 1-h *)

lemma not_refl_wont_derive_no_reason:
  "\<lbrakk>a \<noteq> b; Above a b \<notin> A; Above a c \<in> A \<and> Above c b \<in> A \<rbrakk> \<Longrightarrow> Above a b \<in> connection A"
  using connection.con_in connection.con_trans 
  by blast
  

lemma no_above_from_join_lemma:
  assumes "Above a b \<in> connection A"
  and "\<And>a b. Above a b \<notin> A" 
shows "a = b"
  using assms 
  apply - 
  apply (induct "Above a b" arbitrary: a b rule:connection.inducts)
  by simp+

(* 1-i *)
lemma connection_compose:
  assumes "\<phi> \<in> connection(C \<union> D)"
  and     "C \<subseteq> connection A"
  and     "D \<subseteq> connection B"
  shows   "\<phi> \<in> connection(A \<union> B)"
  using connection_decompose
  proof -
  have f1: "\<forall>C Ca. (C::condition set) \<union> Ca = Ca \<or> Ca \<union> C \<noteq> Ca"
    by blast
    have f2: "\<forall>C Ca. (Ca::condition set) \<union> (C \<union> C) = Ca \<union> C"
      by blast
    have f3: "D \<union> connection B = connection B"
      using assms(3) by blast
    have f4: "\<forall>Ca. \<phi> \<in> connection Ca \<or> Ca \<union> (C \<union> D) \<noteq> Ca"
  using f1 by (metis assms(1) connection_monotonic)
    have f5: "C \<union> connection A = connection A"
  using assms(2) by blast
    have "\<forall>C. D \<union> connection C = connection C \<or> C \<union> B \<noteq> C"
      using f3 f1 by (metis connection_monotonic_simp le_iff_sup sup_assoc)
    then have "C \<union> (D \<union> connection (A \<union> B)) = connection (A \<union> B)"
      using f5 f2 by (metis (no_types) connection_monotonic_simp le_iff_sup sup_assoc)
    then show ?thesis
      using f4 by (metis (no_types) connection_idem le_iff_sup sup.order_iff sup_assoc)
  qed


(* 1-j *)
lemma connection_union_simp:
  "connection (connection A \<union> connection B) = connection (A \<union> B)"
  using connection_compose
  apply safe
   apply blast
  by (smt connection_decompose connection_idem)


lemma connection_compositional:
  assumes "connection A = connection B"
  shows   "connection(A \<union> C) = connection(B \<union> C)"
  using assms 
  using connection_compose 
  by (metis connection_union_simp)


section "Part 2"

datatype process =
  Cond condition
  | Par process process
  | Input nat process
  | Output nat process
  | Nil

datatype action =
  LInput nat | LOutput nat | LTau

primrec frame :: "process \<Rightarrow> condition set" where
  "frame Nil = {}"
| "frame(Cond \<phi>) = {\<phi>}"
| "frame(Par P Q) = frame P \<union> frame Q"
| "frame(Input \<phi> P) = {}"
| "frame(Output \<phi> P) = {}"

inductive semantics :: "condition set \<Rightarrow> process \<Rightarrow> action \<Rightarrow> process \<Rightarrow> bool"
  where
  semantics_input:
     "semantics A (Input n P) (LInput n) P"
| semantics_output:
    "semantics A (Output n P) (LOutput n) P"
| semantics_par_l:
    "semantics (A \<union> frame Q) P \<alpha> P'
     \<Longrightarrow> semantics A (Par P Q) \<alpha> (Par P' Q)"
| semantics_par_r:
    "semantics (A \<union> frame P) Q \<alpha> Q'
     \<Longrightarrow> semantics A (Par P Q) \<alpha> (Par P Q')"
| semantics_com_l:
    "\<lbrakk>semantics (A \<union> frame Q) P (LOutput n) P';
      semantics (A \<union> frame P) Q (LInput m) Q';
      Joinable n m \<in> connection(A \<union> frame P \<union> frame Q)\<rbrakk>
     \<Longrightarrow> semantics A (Par P Q) LTau (Par P' Q')"
| semantics_com_r:
    "\<lbrakk>semantics (A \<union> frame Q) P (LInput n) P';
      semantics (A \<union> frame P) Q (LOutput m) Q';
      Joinable n m \<in> connection(A \<union> frame P \<union> frame Q)\<rbrakk>
     \<Longrightarrow> semantics A (Par P Q) LTau (Par P' Q')"


inductive_cases
  par: "semantics A (Par P Q) x R" and
  nil: "semantics A Nil x R" and
  cond: "semantics A (Cond cond) x R"
print_theorems

subsection "Questions 2 (a)-(c)"



(* 2-a *)
lemma semantics_monotonic:
  assumes "semantics A P \<alpha> Q"
  shows "semantics (A \<union> B) P \<alpha> Q"
  using assms connection_monotonic
  apply induct 
      apply (simp_all add:semantics.intros)
     apply (metis semantics_par_l sup_assoc sup_commute)
    apply (simp add: Un_left_commute semantics_par_r sup.commute)
   apply (simp add: semantics_par_l sup_assoc)
  apply (smt inf_sup_aci(5) semantics_com_l subset_iff sup.assoc)
  by (smt inf_sup_aci(5) semantics_com_r sup.assoc)
thm semantics_monotonic[OF semantics_par_l]

(* 2-b *)
lemma semantics_monotonic_par_l:
  "semantics (A \<union> frame Q) P \<alpha> P' \<Longrightarrow> semantics (A \<union> B) (Par P Q) \<alpha> (Par P' Q)"
  by (frule semantics_monotonic[OF semantics_par_l])

lemma semantics_monotonic_par_r:
  "semantics (A \<union> frame P) Q \<alpha> Q' \<Longrightarrow> semantics (A \<union> B) (Par P Q) \<alpha> (Par P Q')"
  by (frule semantics_monotonic[OF semantics_par_r])

lemma semantics_empty_env:
  assumes "semantics A P \<alpha> Q"
  shows "\<exists>\<beta> Q'. semantics {} P \<beta> Q'"
  using assms 
  apply (induct,simp_all add:semantics.intros)
  using semantics_input apply blast
  using semantics_output apply blast
  using semantics_monotonic semantics_par_l apply blast
  using semantics_monotonic semantics_par_r apply blast
  using semantics_monotonic semantics_par_r apply blast
  by (meson semantics_monotonic semantics_par_r)

(* 2-c *)
lemma semantics_swap_frame_with_con:
  assumes "semantics A P \<alpha> Q"
  and "B = connection A"
  shows "semantics B P \<alpha> Q"
  using assms 
  by (metis connection.con_in le_iff_sup semantics_monotonic subsetI)

lemma semantics_mono_gen: 
  "semantics A P \<alpha> Q \<Longrightarrow> A \<subseteq> B \<Longrightarrow> semantics B P \<alpha> Q"
  using semantics_monotonic
  by (metis sup.order_iff sup_commute)
lemma connection_mono_gen:
  "A \<subseteq> connection A"
  by (simp add: connection.con_in subsetI)

lemma connection_mono_gen2:
  "A \<subseteq> connection B \<Longrightarrow> connection A \<subseteq> connection B"
  by (metis connection_idem connection_monotonic_simp le_iff_sup)

lemma semantics_frame_simple:
  "semantics {} P \<alpha> R \<Longrightarrow> semantics (frame P) P \<alpha> R"
  using semantics_mono_gen by blast

lemma semantics_simple_par:
  "semantics A P \<alpha> Q  \<Longrightarrow> semantics (A \<union> frame P \<union> frame Q) P \<alpha> Q "
  by (simp add: semantics_monotonic)


thm semantics.inducts
lemma semantics_mono_con_gen:
  "semantics A P \<alpha> Q \<Longrightarrow> A \<subseteq> connection B \<Longrightarrow> semantics B P \<alpha> Q"
  apply (induct A P \<alpha> Q arbitrary: B rule:semantics.inducts)
       apply (auto intro:semantics.intros )
     apply (meson connection_mono_gen connection_monotonic_simp
      inf_sup_ord(4) semantics_par_l subset_trans)
    apply (meson Un_upper2 connection_mono_gen 
      connection_monotonic_simp dual_order.trans semantics_par_r)
   apply (smt connection_compose connection_mono_gen 
      connection_monotonic_simp le_sup_iff semantics_com_l subset_trans)
  by (smt connection_compose connection_mono_gen
      connection_monotonic_simp le_sup_iff semantics_com_r subset_trans)

(*
lemma 
  "semantics A P \<alpha> R \<Longrightarrow> semantics A (Par P Q) \<alpha> R"
  sorry 



lemma semantics_swap_frame_with_con_rev:
  assumes "semantics A P \<alpha> Q"
  and "A = connection B"
  shows "semantics B P \<alpha> Q"
  using assms semantics_mono_con_gen by blast
*)

thm connection.inducts
lemma semantics_swap_frame:
  assumes "semantics A P \<alpha> Q"
  and "connection A = connection B"
  shows "semantics B P \<alpha> Q"
  using assms 
  apply - 
  oops 


section "Part 3"

definition stuck :: "process \<Rightarrow> bool"
where
  "stuck P \<equiv> \<forall>\<alpha> P'. semantics {} P \<alpha> P' \<longrightarrow> False"

primrec list_trans :: "_" where
  "list_trans A P [] Q = (P = Q)"
| "list_trans A P (\<alpha>#tr) Q =
    (\<exists>R. semantics A P \<alpha> R \<and> list_trans A R tr Q)"


definition traces_of :: "process \<Rightarrow> action list set"
  where "traces_of P = {tr | tr. \<exists>Q. list_trans {} P tr Q \<and> stuck Q}"


definition trace_eq :: "process \<Rightarrow> process \<Rightarrow> bool"
  where "trace_eq P Q = (traces_of P = traces_of Q)"

lemmas par_simp = semantics.simps[where ?a2.0="Par P Q" for P Q,simplified]

(*Some general lemma *)
lemma par_connection:
 "connection (A \<union> frame P \<union> frame Q) = connection (A \<union> frame (Par P Q))" by (simp add: sup_assoc)

lemma par_connection_swap:
 "connection (A \<union> frame (Par Q P)) = connection (A \<union> frame (Par P Q))"

  by (simp add: sup_commute)

lemma par_connection_assoc:
"connection (A \<union> frame (Par (Par P Q) R)) = connection (A \<union> frame (Par P (Par Q R)))"
  by (metis connection_union_simp par_connection)
  


subsection "Question 3 (a)"

lemma trace_eq_refl:
  shows "trace_eq P P"
  by (simp add: trace_eq_def)

lemma trace_eq_sym:
  assumes "trace_eq P Q"
    shows "trace_eq Q P"
  using assms trace_eq_def by auto 
  

lemma trace_eq_trans:
  assumes "trace_eq P Q"
      and "trace_eq Q R"
    shows "trace_eq P R"
  using assms 
  by (simp add:trace_eq_def)

subsection "Question 3 (b)"

lemma trace_eq_stuck:
  assumes "stuck P"
      and "stuck Q"
    shows "trace_eq P Q"
  using assms 
  apply (unfold trace_eq_def traces_of_def)
  apply (unfold stuck_def)
  apply safe
  apply (metis list.exhaust list_trans.simps(1) list_trans.simps(2))
  by (metis list.exhaust list_trans.simps(1) list_trans.simps(2))
  

subsection "Question 3 (c)"
lemma trace_stuck_is_nil:
  "stuck P \<Longrightarrow> trace_eq P Nil"
  apply (unfold trace_eq_def stuck_def traces_of_def)
  apply safe 
  apply (metis list_trans.simps(1) list_trans.simps(2) neq_Nil_conv nil)
  by (metis list.exhaust list_trans.simps(1) list_trans.simps(2) nil)

lemma stuck_is_stuck:
  "stuck P \<Longrightarrow> list_trans {} P [] P \<and> stuck P"
  by auto

lemma stuck_is_empty_list:
  "stuck P \<Longrightarrow> traces_of P = {[]}"
  apply (unfold traces_of_def)
  apply auto
  by (metis list.exhaust list_trans.simps(2) stuck_def)

lemma "\<forall>p. \<not> stuck p \<or> traces_of p = {[]}"
  using stuck_is_empty_list traces_of_def by auto

lemma "semantics A P (LInput x) Q \<Longrightarrow> stuck R \<Longrightarrow> 
  \<exists>P'. Q = Par P' R \<and> semantics A P (LInput x) P'"
  oops

lemma semantics_trace_subset: 
  " semantics A P tr Q \<Longrightarrow> stuck R \<Longrightarrow> semantics A (Par P R) tr Q "
  unfolding stuck_def
  apply (induct tr arbitrary: A P  R)
    apply (simp add:par_simp)
    apply (rule disjI1)
    oops 
  
    

lemma traces_of_monotonic:
  assumes "stuck R"
  shows "traces_of P \<subseteq> traces_of (Par P R)"
  using assms 
  apply -
  unfolding traces_of_def  stuck_def 
  apply safe 
  apply (induct "Par P R" arbitrary: P)

  sorry

subsection "Question 3 (d)"

text \<open>Feel free to give this answer in free-text comments,
      or as Isabelle definitions. \<close>

subsection "Question 3 (e)"


lemma traces_of_not_antimonotonic:
  assumes "\<And>P R. stuck R \<Longrightarrow> traces_of (Par P R) \<subseteq> traces_of P"
  shows "False"
  using assms 
  apply -
  unfolding stuck_def traces_of_def 
  sorry

subsection "Question 3 (f)"
lemma semantics_par_assoc0:
  assumes "semantics A (Par P Q) \<alpha> R"
  shows "\<exists>P' Q' .
           R = Par P' Q' \<and>
           semantics A (Par P Q) \<alpha> (Par P' Q')"
  using assms 
  apply - 
  unfolding stuck_def traces_of_def 
  using par_simp by auto


lemma semantics_par_assoc1:
  assumes "semantics A (Par P (Par Q S)) \<alpha> R"
  shows "\<exists>P' Q' S'.
           R = Par P' (Par Q' S') \<and>
           semantics A (Par (Par P Q) S) \<alpha> (Par (Par P' Q') S')"
  using assms
  apply -
  apply (simp add:par_simp semantics.intros)
  apply (induct \<alpha>)
    apply (simp_all add:semantics.intros)
    apply (smt sup_commute sup_left_commute)
   apply (smt sup_assoc sup_commute)
  
  apply (safe)
          apply (simp add: Un_commute inf_sup_aci(7))
         apply (simp add: Un_commute Un_left_commute)
        apply (simp add: inf_sup_aci(6))
proof -
  fix n :: nat and P' :: process and m :: nat and Q' :: process and Q'a :: process
  assume a1: "R = Par P' (Par Q Q'a)"
  assume a2: "semantics (A \<union> (frame Q \<union> frame S)) P (LInput n) P'"
  assume a3: "Joinable n m \<in> connection (A \<union> frame P \<union> (frame Q \<union> frame S))"
  assume a4: "semantics (A \<union> frame P \<union> frame Q) S (LOutput m) Q'a"
  have f5: "\<forall>n p. Input n p \<noteq> R"
    using a1 by (meson process.simps(14))
  have f6: "\<forall>n p. Output n p \<noteq> R"
    using a1 by blast
  have f7: "\<forall>c. Cond c \<noteq> R"
    using a1 by (meson process.distinct(1))
  have "process.Nil \<noteq> R"
    using a1 by blast
  then have "Par (sK71 R) (sK72 R) = R"
    using f7 f6 f5
    by (metis process.exhaust) (* > 1.0 s, timed out *)
  then have "\<exists>n p pa na. semantics (A \<union> frame (Par Q S)) P (LInput na) pa \<and> Par P' (Par Q Q'a) = Par pa (Par Q p) \<and> semantics (A \<union> (frame P \<union> frame Q)) S (LOutput n) p \<and> Joinable na n \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S)"
    using a4 a3 a2 by (metis (no_types) frame.simps(3) inf_sup_aci(6))
  then have "\<exists>n p pa na. semantics (A \<union> (frame S \<union> frame Q)) P (LInput na) pa \<and> Par P' (Par Q Q'a) = Par pa (Par Q p) \<and> semantics (A \<union> (frame P \<union> frame Q)) S (LOutput n) p \<and> Joinable na n \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S)"
    by (simp add: inf_sup_aci(5))
  then show "\<exists>p pa pb. Par P' (Par Q Q'a) = Par p (Par pa pb) \<and> (pb = S \<and> (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P LTau p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q LTau pa \<or> (\<exists>n. semantics (A \<union> frame S \<union> frame Q) P (LOutput n) p \<and> (\<exists>na. semantics (A \<union> frame S \<union> frame P) Q (LInput na) pa \<and> Joinable n na \<in> connection (A \<union> frame S \<union> frame P \<union> frame Q))) \<or> (\<exists>n. semantics (A \<union> frame S \<union> frame Q) P (LInput n) p \<and> (\<exists>na. semantics (A \<union> frame S \<union> frame P) Q (LOutput na) pa \<and> Joinable n na \<in> connection (A \<union> frame S \<union> frame P \<union> frame Q)))) \<or> p = P \<and> pa = Q \<and> semantics (A \<union> (frame P \<union> frame Q)) S LTau pb \<or> (\<exists>n. (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput n) p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q (LOutput n) pa) \<and> (\<exists>na. semantics (A \<union> (frame P \<union> frame Q)) S (LInput na) pb \<and> Joinable n na \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S))) \<or> (\<exists>n. (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P (LInput n) p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q (LInput n) pa) \<and> (\<exists>na. semantics (A \<union> (frame P \<union> frame Q)) S (LOutput na) pb \<and> Joinable n na \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S))))"
    by (metis (no_types) inf_sup_aci(6))
next
  fix n :: nat and P' :: process and m :: nat and Q' :: process and P'a :: process
  assume a1: "semantics (A \<union> (frame Q \<union> frame S)) P (LInput n) P'"
  assume a2: "Joinable n m \<in> connection (A \<union> frame P \<union> (frame Q \<union> frame S))"
  assume "semantics (A \<union> frame P \<union> frame S) Q (LOutput m) P'a"
  then have f3: "semantics (A \<union> frame (Par P S)) Q (LOutput m) P'a"
    by (simp add: Un_left_commute sup.commute)
  have "Joinable n m \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S))))"
    using a2 by (simp add: connection_def)
  then have "\<exists>p n na pa. semantics (frame Q \<union> (A \<union> frame S)) P (LInput na) p \<and> semantics (A \<union> frame (Par P S)) Q (LOutput n) pa \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> Par P' (Par P'a S) = Par p (Par pa S)"
    using f3 a1 by (metis Un_left_commute)
  then have "\<exists>p n na pa. semantics (A \<union> frame (Par P S)) Q (LOutput n) pa \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> semantics (A \<union> frame S \<union> frame Q) P (LInput na) p \<and> Par P' (Par P'a S) = Par p (Par pa S)"
    by (metis sup.commute)
  then have "\<exists>p n na pa. semantics (frame P \<union> (A \<union> frame S)) Q (LOutput n) pa \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> semantics (A \<union> frame S \<union> frame Q) P (LInput na) p \<and> Par P' (Par P'a S) = Par p (Par pa S)"
    by (simp add: Un_left_commute)
  then have "\<exists>p n na pa. Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> semantics (A \<union> frame S \<union> frame P) Q (LOutput n) pa \<and> semantics (A \<union> frame S \<union> frame Q) P (LInput na) p \<and> Par P' (Par P'a S) = Par p (Par pa S)"
    by (metis sup.commute)
  then have "\<exists>p n na pa. Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> frame Q \<union> (frame P \<union> (A \<union> frame S)))) \<and> semantics (A \<union> frame S \<union> frame P) Q (LOutput n) pa \<and> semantics (A \<union> frame S \<union> frame Q) P (LInput na) p \<and> Par P' (Par P'a S) = Par p (Par pa S)"
    by (simp add: Un_left_commute)
  then show "\<exists>p pa pb. Par P' (Par P'a S) = Par p (Par pa pb) \<and> (pb = S \<and> (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P LTau p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q LTau pa \<or> (\<exists>n. semantics (A \<union> frame S \<union> frame Q) P (LOutput n) p \<and> (\<exists>na. semantics (A \<union> frame S \<union> frame P) Q (LInput na) pa \<and> Joinable n na \<in> connection (A \<union> frame S \<union> frame P \<union> frame Q))) \<or> (\<exists>n. semantics (A \<union> frame S \<union> frame Q) P (LInput n) p \<and> (\<exists>na. semantics (A \<union> frame S \<union> frame P) Q (LOutput na) pa \<and> Joinable n na \<in> connection (A \<union> frame S \<union> frame P \<union> frame Q)))) \<or> p = P \<and> pa = Q \<and> semantics (A \<union> (frame P \<union> frame Q)) S LTau pb \<or> (\<exists>n. (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput n) p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q (LOutput n) pa) \<and> (\<exists>na. semantics (A \<union> (frame P \<union> frame Q)) S (LInput na) pb \<and> Joinable n na \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S))) \<or> (\<exists>n. (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P (LInput n) p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q (LInput n) pa) \<and> (\<exists>na. semantics (A \<union> (frame P \<union> frame Q)) S (LOutput na) pb \<and> Joinable n na \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S))))"
    by (metis connection_def sup.commute)
next

  fix n :: nat and P' :: process and m :: nat and Q' :: process and Q'a :: process
  assume a1: "semantics (A \<union> (frame Q \<union> frame S)) P (LOutput n) P'"
  assume a2: "Joinable n m \<in> connection (A \<union> frame P \<union> (frame Q \<union> frame S))"
  assume "semantics (A \<union> frame P \<union> frame Q) S (LInput m) Q'a"
  then have f3: "semantics (A \<union> frame (Par P Q)) S (LInput m) Q'a"
    by (simp add: sup.commute sup_left_commute)
  have "Joinable n m \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S))))"
    using a2 by (simp add: connection_def sup.commute)
  then have "\<exists>n p pa na. semantics (A \<union> (frame Q \<union> frame S)) P (LOutput na) pa \<and> semantics (A \<union> frame (Par P Q)) S (LInput n) p \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> Par P' (Par Q Q'a) = Par pa (Par Q p)"
    using f3 a1 by blast
  then have "\<exists>n p pa na. semantics (frame Q \<union> (A \<union> frame S)) P (LOutput na) pa \<and> semantics (A \<union> frame (Par P Q)) S (LInput n) p \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> Par P' (Par Q Q'a) = Par pa (Par Q p)"
    by (simp add: sup_left_commute)
  then have "\<exists>n p pa na. semantics (A \<union> frame (Par P Q)) S (LInput n) p \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput na) pa \<and> Par P' (Par Q Q'a) = Par pa (Par Q p)"
    by (metis sup.commute)
  then have "\<exists>n p pa na. Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> semantics (A \<union> (frame P \<union> frame Q)) S (LInput n) p \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput na) pa \<and> Par P' (Par Q Q'a) = Par pa (Par Q p)"
    by (metis frame.simps(3))
  then have "\<exists>n p pa na. Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> frame S \<union> (A \<union> (frame P \<union> frame Q)))) \<and> semantics (A \<union> (frame P \<union> frame Q)) S (LInput n) p \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput na) pa \<and> Par P' (Par Q Q'a) = Par pa (Par Q p)"
    by (simp add: sup.commute sup_left_commute)
  then show "\<exists>p pa pb. Par P' (Par Q Q'a) = Par p (Par pa pb) \<and> (pb = S \<and> (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P LTau p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q LTau pa \<or> (\<exists>n. semantics (A \<union> frame S \<union> frame Q) P (LOutput n) p \<and> (\<exists>na. semantics (A \<union> frame S \<union> frame P) Q (LInput na) pa \<and> Joinable n na \<in> connection (A \<union> frame S \<union> frame P \<union> frame Q))) \<or> (\<exists>n. semantics (A \<union> frame S \<union> frame Q) P (LInput n) p \<and> (\<exists>na. semantics (A \<union> frame S \<union> frame P) Q (LOutput na) pa \<and> Joinable n na \<in> connection (A \<union> frame S \<union> frame P \<union> frame Q)))) \<or> p = P \<and> pa = Q \<and> semantics (A \<union> (frame P \<union> frame Q)) S LTau pb \<or> (\<exists>n. (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput n) p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q (LOutput n) pa) \<and> (\<exists>na. semantics (A \<union> (frame P \<union> frame Q)) S (LInput na) pb \<and> Joinable n na \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S))) \<or> (\<exists>n. (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P (LInput n) p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q (LInput n) pa) \<and> (\<exists>na. semantics (A \<union> (frame P \<union> frame Q)) S (LOutput na) pb \<and> Joinable n na \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S))))"
    by (metis connection_def sup.commute)
next
  fix n :: nat and P' :: process and m :: nat and Q' :: process and P'a :: process
  assume a1: "semantics (A \<union> (frame Q \<union> frame S)) P (LOutput n) P'"
  assume a2: "Joinable n m \<in> connection (A \<union> frame P \<union> (frame Q \<union> frame S))"
  assume "semantics (A \<union> frame P \<union> frame S) Q (LInput m) P'a"
  then have f3: "semantics (A \<union> frame (Par P S)) Q (LInput m) P'a"
    by (simp add: inf_sup_aci(5) inf_sup_aci(7))
  have "Joinable n m \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S))))"
    using a2 by (simp add: connection_def inf_sup_aci(5))
  then have "\<exists>p n pa na. semantics (A \<union> (frame Q \<union> frame S)) P (LOutput na) p \<and> semantics (A \<union> frame (Par P S)) Q (LInput n) pa \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> Par P' (Par P'a S) = Par p (Par pa S)"
    using f3 a1 by blast
  then have "\<exists>p n pa na. semantics (frame Q \<union> (A \<union> frame S)) P (LOutput na) p \<and> semantics (A \<union> frame (Par P S)) Q (LInput n) pa \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> Par P' (Par P'a S) = Par p (Par pa S)"
    by (simp add: inf_sup_aci(7))
  then have "\<exists>p n pa na. semantics (A \<union> frame (Par P S)) Q (LInput n) pa \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput na) p \<and> Par P' (Par P'a S) = Par p (Par pa S)"
    by (metis inf_sup_aci(5))
  then have "\<exists>p n pa na. semantics (frame P \<union> (A \<union> frame S)) Q (LInput n) pa \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput na) p \<and> Par P' (Par P'a S) = Par p (Par pa S)"
    by (simp add: inf_sup_aci(7))
  then have "\<exists>p n pa na. Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> semantics (A \<union> frame S \<union> frame P) Q (LInput n) pa \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput na) p \<and> Par P' (Par P'a S) = Par p (Par pa S)"
    by (metis inf_sup_aci(5))
  then have "\<exists>p n pa na. Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> frame Q \<union> (frame P \<union> (A \<union> frame S)))) \<and> semantics (A \<union> frame S \<union> frame P) Q (LInput n) pa \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput na) p \<and> Par P' (Par P'a S) = Par p (Par pa S)"
    by (simp add: inf_sup_aci(7))
  then show "\<exists>p pa pb. Par P' (Par P'a S) = Par p (Par pa pb) \<and> (pb = S \<and> (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P LTau p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q LTau pa \<or> (\<exists>n. semantics (A \<union> frame S \<union> frame Q) P (LOutput n) p \<and> (\<exists>na. semantics (A \<union> frame S \<union> frame P) Q (LInput na) pa \<and> Joinable n na \<in> connection (A \<union> frame S \<union> frame P \<union> frame Q))) \<or> (\<exists>n. semantics (A \<union> frame S \<union> frame Q) P (LInput n) p \<and> (\<exists>na. semantics (A \<union> frame S \<union> frame P) Q (LOutput na) pa \<and> Joinable n na \<in> connection (A \<union> frame S \<union> frame P \<union> frame Q)))) \<or> p = P \<and> pa = Q \<and> semantics (A \<union> (frame P \<union> frame Q)) S LTau pb \<or> (\<exists>n. (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput n) p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q (LOutput n) pa) \<and> (\<exists>na. semantics (A \<union> (frame P \<union> frame Q)) S (LInput na) pb \<and> Joinable n na \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S))) \<or> (\<exists>n. (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P (LInput n) p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q (LInput n) pa) \<and> (\<exists>na. semantics (A \<union> (frame P \<union> frame Q)) S (LOutput na) pb \<and> Joinable n na \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S))))"
    by (metis connection_def inf_sup_aci(5))
next
  fix Q' :: process and n :: nat and P' :: process and m :: nat and Q'a :: process
  assume a1: "semantics (A \<union> frame P \<union> frame S) Q (LInput n) P'"
  assume a2: "semantics (A \<union> frame P \<union> frame Q) S (LOutput m) Q'a"
  assume a3: "Joinable n m \<in> connection (A \<union> frame P \<union> frame Q \<union> frame S)"
  have f4: "semantics (A \<union> frame (Par P S)) Q (LInput n) P'"
    using a1 by (simp add: sup.left_commute sup_commute)
  have f5: "semantics (A \<union> frame (Par P Q)) S (LOutput m) Q'a"
    using a2 by (simp add: sup.left_commute sup_commute)
  have "Joinable n m \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S))))"
    using a3 by (simp add: connection_def sup.left_commute)
  then have "\<exists>n p na pa. semantics (A \<union> (frame P \<union> frame S)) Q (LInput na) pa \<and> semantics (A \<union> frame (Par P Q)) S (LOutput n) p \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> Par P (Par P' Q'a) = Par P (Par pa p)"
    using f5 f4 by auto
  then have "\<exists>n p na pa. semantics (frame P \<union> (A \<union> frame S)) Q (LInput na) pa \<and> semantics (A \<union> frame (Par P Q)) S (LOutput n) p \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> Par P (Par P' Q'a) = Par P (Par pa p)"
    by (simp add: sup.left_commute)
  then have "\<exists>n p na pa. semantics (A \<union> frame (Par P Q)) S (LOutput n) p \<and> Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> semantics (A \<union> frame S \<union> frame P) Q (LInput na) pa \<and> Par P (Par P' Q'a) = Par P (Par pa p)"
    by (metis sup_commute)
  then have "\<exists>n p na pa. Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> A \<union> frame (Par P (Par Q S)))) \<and> semantics (A \<union> (frame P \<union> frame Q)) S (LOutput n) p \<and> semantics (A \<union> frame S \<union> frame P) Q (LInput na) pa \<and> Par P (Par P' Q'a) = Par P (Par pa p)"
    by (metis frame.simps(3))
  then have "\<exists>n p na pa. Joinable na n \<in> Collect (connectionp (\<lambda>c. c \<in> frame S \<union> (A \<union> (frame P \<union> frame Q)))) \<and> semantics (A \<union> (frame P \<union> frame Q)) S (LOutput n) p \<and> semantics (A \<union> frame S \<union> frame P) Q (LInput na) pa \<and> Par P (Par P' Q'a) = Par P (Par pa p)"
    by (simp add: sup.left_commute sup_commute)
  then show "\<exists>p pa pb. Par P (Par P' Q'a) = Par p (Par pa pb) \<and> (pb = S \<and> (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P LTau p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q LTau pa \<or> (\<exists>n. semantics (A \<union> frame S \<union> frame Q) P (LOutput n) p \<and> (\<exists>na. semantics (A \<union> frame S \<union> frame P) Q (LInput na) pa \<and> Joinable n na \<in> connection (A \<union> frame S \<union> frame P \<union> frame Q))) \<or> (\<exists>n. semantics (A \<union> frame S \<union> frame Q) P (LInput n) p \<and> (\<exists>na. semantics (A \<union> frame S \<union> frame P) Q (LOutput na) pa \<and> Joinable n na \<in> connection (A \<union> frame S \<union> frame P \<union> frame Q)))) \<or> p = P \<and> pa = Q \<and> semantics (A \<union> (frame P \<union> frame Q)) S LTau pb \<or> (\<exists>n. (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput n) p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q (LOutput n) pa) \<and> (\<exists>na. semantics (A \<union> (frame P \<union> frame Q)) S (LInput na) pb \<and> Joinable n na \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S))) \<or> (\<exists>n. (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P (LInput n) p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q (LInput n) pa) \<and> (\<exists>na. semantics (A \<union> (frame P \<union> frame Q)) S (LOutput na) pb \<and> Joinable n na \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S))))"
    by (metis connection_def sup_commute)
next
  fix Q' :: process and n :: nat and P' :: process and m :: nat and Q'a :: process
  assume a1: "R = Par P (Par P' Q'a)"
  assume a2: "semantics (A \<union> frame P \<union> frame S) Q (LOutput n) P'"
  assume a3: "semantics (A \<union> frame P \<union> frame Q) S (LInput m) Q'a"
  assume "Joinable n m \<in> connection (A \<union> frame P \<union> frame Q \<union> frame S)"
  then have "Joinable n m \<in> connection (A \<union> frame (Par P (Par Q S)))"
    by (simp add: inf_sup_aci(6))
  then have "\<exists>n p na pa. Par P (Par pa p) = R \<and> semantics (A \<union> frame (Par P S)) Q (LOutput na) pa \<and> semantics (A \<union> frame (Par P Q)) S (LInput n) p \<and> Joinable na n \<in> connection (A \<union> frame (Par P (Par Q S)))"
    using a3 a2 a1 by (metis (full_types) frame.simps(3) inf_sup_aci(6))
  then have "\<exists>n p na pa. semantics (A \<union> (frame S \<union> frame P)) Q (LOutput na) pa \<and> semantics (A \<union> frame (Par P Q)) S (LInput n) p \<and> Joinable na n \<in> connection (A \<union> frame (Par P (Par Q S))) \<and> Par P (Par P' Q'a) = Par P (Par pa p)"
    using a1 by (simp add: inf_sup_aci(5))
  then show "\<exists>p pa pb. Par P (Par P' Q'a) = Par p (Par pa pb) \<and> (pb = S \<and> (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P LTau p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q LTau pa \<or> (\<exists>n. semantics (A \<union> frame S \<union> frame Q) P (LOutput n) p \<and> (\<exists>na. semantics (A \<union> frame S \<union> frame P) Q (LInput na) pa \<and> Joinable n na \<in> connection (A \<union> frame S \<union> frame P \<union> frame Q))) \<or> (\<exists>n. semantics (A \<union> frame S \<union> frame Q) P (LInput n) p \<and> (\<exists>na. semantics (A \<union> frame S \<union> frame P) Q (LOutput na) pa \<and> Joinable n na \<in> connection (A \<union> frame S \<union> frame P \<union> frame Q)))) \<or> p = P \<and> pa = Q \<and> semantics (A \<union> (frame P \<union> frame Q)) S LTau pb \<or> (\<exists>n. (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P (LOutput n) p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q (LOutput n) pa) \<and> (\<exists>na. semantics (A \<union> (frame P \<union> frame Q)) S (LInput na) pb \<and> Joinable n na \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S))) \<or> (\<exists>n. (pa = Q \<and> semantics (A \<union> frame S \<union> frame Q) P (LInput n) p \<or> p = P \<and> semantics (A \<union> frame S \<union> frame P) Q (LInput n) pa) \<and> (\<exists>na. semantics (A \<union> (frame P \<union> frame Q)) S (LOutput na) pb \<and> Joinable n na \<in> connection (A \<union> (frame P \<union> frame Q) \<union> frame S))))"
    by (metis (no_types) frame.simps(3) inf_sup_aci(6))
qed

text \<open>
  This similar lemma will be needed later.
  You may use it without proof. \<close>
lemma semantics_par_assoc2:
  "semantics A (Par (Par P Q) S) \<alpha> R \<Longrightarrow>
  \<exists> P' Q' S'. R = Par (Par P' Q') S' \<and> semantics A (Par P (Par Q S)) \<alpha> (Par P' (Par Q' S'))"
  sorry

subsection "Question 3 (g)"
lemma list_trans_par_assoc:
  "list_trans A (Par (Par P Q) S) tr (Par (Par P' Q') S') =
       list_trans A (Par P (Par Q S)) tr (Par P' (Par Q' S'))"
  (* TODO *)
  apply (unfold list_trans_def)
  apply safe
  thm semantics.inducts
   apply induct
  
  apply (induct A "(Par (Par P Q) S)" tr "(Par (Par P' Q') S')" rule:semantics.inducts)
  sorry

subsection "Question 3 (h)"
lemma stuck_par:
  "stuck(Par P Q) = (stuck P \<and> stuck Q)"
  apply safe 
  using semantics_monotonic semantics_par_l stuck_def apply fastforce 
  using semantics_monotonic semantics_par_r stuck_def apply fastforce
  by (smt Collect_mono_iff list_trans.simps(1) stuck_def traces_of_def 
      traces_of_monotonic)

subsection "Question 3 (i)"
lemma trace_eq_par_assoc:
  shows "trace_eq (Par (Par P Q) S) (Par P (Par Q S))"
  apply (unfold trace_eq_def traces_of_def stuck_def)
  apply safe 
  using list_trans_par_assoc
  apply clarsimp

  sorry

subsection "Question 3 (j)"
thm semantics.inducts
lemma trace_eq_nil_par:
  shows "trace_eq P (Par P Nil)"
  apply (unfold trace_eq_def traces_of_def list_trans_def)
  apply safe 

  sorry

subsection "Question 3 (k)"

lemma trace_eq_par_comm:
  shows "trace_eq (Par P Q) (Par Q P)"
  apply (unfold trace_eq_def traces_of_def )
  apply safe
   apply simp_all

  sorry

end