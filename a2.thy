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
  (* TODO *)
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
lemma joinable_or_above:
  "x \<in> A \<Longrightarrow>\<exists> a b. x = Joinable a b \<or> x = Above a b"
  apply induct by blast +

lemma only_joinable_set:
  "\<And>a b. Above a b \<notin> A \<Longrightarrow> (\<forall> x. x \<in> A \<Longrightarrow> x = Joinable c d)"
  by simp

lemma not_refl_wont_derive_nil:
  "\<And>a b . a \<noteq> b \<Longrightarrow> Above a b \<notin> connection {} "
  apply safe
  using connection.inducts
  using connection_nil 
  using is_refl.simps(1) by blast

lemma not_refl_wont_derive_no_reason:
  "\<lbrakk>a \<noteq> b; Above a b \<notin> A; Above a c \<in> A \<and> Above c b \<in> A \<rbrakk> \<Longrightarrow> Above a b \<in> connection A"
  using connection.con_in connection.con_trans 
  by blast

lemma no_above_from_join_lemma_gen:
  "\<forall> x \<in> A. x = Above c c \<Longrightarrow> Above a b \<in> connection A \<Longrightarrow> a = b"
  using connection_idem connection_monotonic not_refl_wont_derive_nil
  using le_iff_sup subsetI
  by (metis con_is_refl is_refl.simps(1) subset_eq)

lemma must_jump_by_above:
  " a \<noteq> c \<Longrightarrow>(\<exists>b. a \<noteq>b \<and> Above a b\<in> A\<and> Above b c \<in> A) = (Above a c \<in> connection A )"
  (* TODO *)
  apply (safe)
  using connection.con_in connection.con_trans apply blast
  using not_refl_wont_derive_no_reason no_above_from_join_lemma_gen
  sorry

lemma no_above_from_join_lemma:
  assumes "Above a b \<in> connection A"
  and "\<And>a b. Above a b \<notin> A" 
  shows "a = b"
  using connection_filter_refl 
  using assms 
  using must_jump_by_above
  by meson


(* 1-i *)
lemma connection_compose:
  assumes "\<phi> \<in> connection(C \<union> D)"
  and     "C \<subseteq> connection A"
  and     "D \<subseteq> connection B"
  shows   "\<phi> \<in> connection(A \<union> B)"
  (* TODO *)
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

lemma semantics_mono_con_gen: 
  "semantics A P \<alpha> Q \<Longrightarrow> A \<subseteq> connection B \<Longrightarrow> semantics B P \<alpha> Q"
  apply (frule semantics.induct)
        apply (simp_all add:semantics.intros semantics_monotonic)
  sorry



lemma semantics_swap_frame_with_con_rev:
  assumes "semantics A P \<alpha> Q"
  and "A = connection B"
  shows "semantics B P \<alpha> Q"
  using assms semantics_mono_con_gen by blast

lemma semantics_swap_frame:
  assumes "semantics A P \<alpha> Q"
  and "connection A = connection B"
  shows "semantics B P \<alpha> Q"
  using assms 
  using semantics_swap_frame_with_con_rev
  using semantics_swap_frame_with_con by blast

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
  "stuck P  \<Longrightarrow> list_trans {} P [] P \<and> stuck P"
  by auto

lemma stuck_is_empty_list:
  "stuck P \<Longrightarrow> traces_of P = {[]}"
  apply (unfold traces_of_def)
  apply auto
  by (metis list.exhaust list_trans.simps(2) stuck_def)

lemma nil_is_smallest_trace:
  "traces_of P \<subseteq> traces_of (Par P Nil)"
  apply (unfold traces_of_def)
 
  sorry 

lemma traces_of_monotonic:
  assumes "stuck R"
  shows "traces_of P \<subseteq> traces_of (Par P R)"
  using assms 
  apply -
  apply (induction P arbitrary:R)
      apply (unfold traces_of_def)
  sledgehammer
  sorry

subsection "Question 3 (d)"

text \<open>Feel free to give this answer in free-text comments,
      or as Isabelle definitions. \<close>

subsection "Question 3 (e)"

lemma traces_of_not_antimonotonic:
  assumes "\<And>P R. stuck R \<Longrightarrow> traces_of (Par P R) \<subseteq> traces_of P"
  shows "False"
  (* TODO *)

  sorry

subsection "Question 3 (f)"

lemma semantics_par_assoc1:
  assumes "semantics A (Par P (Par Q S)) \<alpha> R"
  shows "\<exists>P' Q' S'.
           R = Par P' (Par Q' S') \<and>
           semantics A (Par (Par P Q) S) \<alpha> (Par (Par P' Q') S')"
  (* TODO *)
  
  sorry

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
  sorry

subsection "Question 3 (h)"
lemma stuck_par:
  "stuck(Par P Q) = (stuck P \<and> stuck Q)"
  apply safe 
  using semantics_monotonic semantics_par_l stuck_def apply fastforce 
  using semantics_monotonic semantics_par_r stuck_def apply fastforce

  apply (unfold stuck_def traces_of_def)
  using traces_of_monotonic
  apply (induct)  
    apply (smt Collect_mono_iff list_trans.simps(1) stuck_def traces_of_def)
   apply (smt Collect_mono_iff list_trans.simps(1) stuck_def sup_bot_left 
      traces_of_def traces_of_monotonic)
  by (smt Collect_mono_iff list_trans.simps(1) stuck_def 
      sup_bot_left traces_of_def traces_of_monotonic)
  
subsection "Question 3 (i)"
lemma trace_eq_par_assoc:
  shows "trace_eq (Par (Par P Q) S) (Par P (Par Q S))"
  apply (unfold trace_eq_def traces_of_def stuck_def)
  apply safe 
   apply (rule list.induct)
    apply (simp_all add:semantics.intros)
  sorry

subsection "Question 3 (j)"

lemma trace_eq_nil_par:
  shows "trace_eq P (Par P Nil)"
  apply (unfold trace_eq_def traces_of_def list_trans_def)
  sorry

subsection "Question 3 (k)"

lemma trace_eq_par_comm:
  shows "trace_eq (Par P Q) (Par Q P)"
  apply (unfold trace_eq_def traces_of_def )
  apply safe
   apply simp_all
  apply (rule list.induct)

  sorry

end