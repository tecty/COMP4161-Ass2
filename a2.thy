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

thm semantics.cases

inductive_cases
  par: "semantics A (Par P Q) x R" and
  nil: "semantics A Nil x R" and
  cond: "semantics A (Cond cond) x R"
print_theorems
thm par 

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

lemma semantics_par_stuck: 
  "semantics A P \<alpha> P' \<Longrightarrow> stuck Q \<Longrightarrow> semantics A (Par P Q) \<alpha> (Par P' Q)"
  by (simp add: semantics_monotonic semantics_par_l)

lemma semantics_par_mono: 
  "semantics A P \<alpha> P'\<Longrightarrow> semantics A (Par P Q) \<alpha> (Par P' Q)"
  by (simp add: semantics_monotonic semantics_par_l)

lemma par_stuck_stuck_is_stuck: 
  "\<lbrakk>stuck P; stuck Q\<rbrakk> \<Longrightarrow> stuck (Par P Q)"
  proof -
    assume a1: "stuck P"
    assume a2: "stuck Q"
    obtain aa :: "process \<Rightarrow> action" and pp :: "process \<Rightarrow> process" where
      f3: "\<forall>p. (stuck p \<or> semantics {} p (aa p) (pp p)) \<and> ((\<forall>a pa. \<not> semantics {} p a pa) \<or> \<not> stuck p)"
  using stuck_def by moura
    obtain aaa :: "process \<Rightarrow> action" and ppa :: "process \<Rightarrow> process" where
      f4: "\<forall>C p a pa. semantics {} p (aaa p) (ppa p) \<or> \<not> semantics C p a pa"
      using semantics_empty_env by moura
    then have f5: "\<forall>p C a. \<not> semantics C Q a p"
      using f3 a2 by blast
    have "\<forall>p C a. \<not> semantics C P a p"
      using f4 f3 a1 by blast
  then have "\<not> semantics {} (Par P Q) (aa (Par P Q)) (pp (Par P Q))"
    using f5 par_simp by presburger
  then show ?thesis
    using f3 by blast
  qed

lemma semantics_par_stuck_to_stuck: 
  "semantics A P \<alpha> P'\<Longrightarrow>stuck P' \<Longrightarrow> stuck Q 
  \<Longrightarrow> stuck (Par P' Q) \<and> semantics A (Par P Q) \<alpha> (Par P' Q)"
  apply (rule conjI)
   apply (erule par_stuck_stuck_is_stuck, assumption)
  by (erule semantics_par_mono)

lemma list_trans_stuck_one:
  "list_trans A P \<alpha> P' \<Longrightarrow> stuck Q \<Longrightarrow>list_trans A (Par P Q) \<alpha> (Par P' Q)"
  apply (induct \<alpha> arbitrary:A P P' Q )
  apply (force)
  apply (clarsimp)
  apply (rule_tac x="Par R Q" in exI)
  apply (rule conjI)
   apply (simp add: semantics_par_stuck)
  by auto 

lemma traces_of_monotonic:
  assumes "stuck R"
  shows "traces_of P \<subseteq> traces_of (Par P R)"
  using assms
  unfolding traces_of_def  stuck_def 
  apply clarsimp
  apply (rule_tac x="Par Q R" in  exI)
  thm semantics_par_stuck
  apply (rule conjI)
   apply (rule list_trans_stuck_one)
    apply assumption +
   apply (unfold stuck_def, force)
  using par_stuck_stuck_is_stuck stuck_def by auto


\<comment> \<open>Some 3-d helper lemma\<close>

lemma cond_stuck:
  "p = Cond \<phi> \<Longrightarrow> stuck p"
  apply (unfold stuck_def)
  using cond by blast

lemma sub_stuck_par_stuck:
  "stuck (Par Q R) \<Longrightarrow> stuck Q \<and> stuck R"
  unfolding stuck_def
  apply (rule conjI)  
  using semantics_par_mono apply blast
  using semantics_mono_con_gen semantics_par_r by blast

lemma sub_stuck_par_stuck2:
  " stuck Q \<and> stuck R \<Longrightarrow> stuck (Par Q R)"
  by (simp add: par_stuck_stuck_is_stuck)

lemma input_is_not_stuck:
  "stuck (Input n P) \<Longrightarrow> false"
  using semantics_input stuck_def by blast

lemma output_is_not_stuck:
  "stuck (Output n P) \<Longrightarrow> false"
  using semantics_output stuck_def by blast

lemma nil_stuck:
  "stuck Nil"
  using nil stuck_def by auto 

lemma par_either: 
  "semantics (A \<union> frame Q) P \<alpha> P' \<or> semantics (A \<union> frame P) Q \<alpha> Q'
   \<Longrightarrow> \<exists>P' Q'. semantics A (Par P Q) \<alpha> (Par P' Q')"
  using semantics_par_l semantics_par_r by blast

subsection "Question 3 (d)"

text \<open>Feel free to give this answer in free-text comments,
      or as Isabelle definitions. \<close>

\<comment> \<open>the basic situation, the x is in traces of (Par P Q) while not in traces of  P\<close>

definition proc1 where "proc1=Par (Input 0 Nil) (Output 1 Nil)"
definition proc2 where "proc2=Cond (Joinable 0 1)"

lemma proc2_stuck : "stuck proc2"
  using cond_stuck proc2_def by blast 

lemma joinable_not_in_proc1: "Joinable 0 1 \<notin> connection (frame proc1)"
  by (metis connection_compositional connection_idem 
      connection_mono_gen connection_nil frame.simps(3)
      frame.simps(4) frame.simps(5) is_refl.simps(2) 
      proc1_def sup.order_iff zero_neq_one)

lemma joinable_in_par_both:
  "Joinable 0 1 \<in> connection ({} \<union> frame proc1 \<union> frame proc2)"
  unfolding proc1_def proc2_def
  using connection.con_in by auto

lemma proc_input_is_0:
  "semantics {} (Input 0 process.Nil) (LInput n) process.Nil = (n = 0)"
  apply safe 
   apply (induct "({}:: condition set)" "(Input 0 process.Nil)" "(LInput n)"
          "process.Nil" rule:semantics.inducts)
   apply auto 
  by (rule semantics_input)

lemma proc_output_is_1:
  "semantics {} (Output 1 process.Nil) (LOutput n) process.Nil = (n = 1)"
  apply safe 
   apply (induct "({}:: condition set)" "(Output 1 process.Nil)" "(LOutput n)"
          "process.Nil" rule:semantics.inducts)
   apply auto 
  by (rule semantics_output)

lemma proc_input_by_output_false:
  "semantics {} (Input 0 process.Nil) (LOutput n) process.Nil \<Longrightarrow> false"
  by (induct "({}:: condition set)" "(Input 0 process.Nil)" "(LOutput n)"
          "process.Nil" rule:semantics.inducts)

lemma ltau_not_in_proc1:
  "\<not> semantics {} proc1 LTau (Par Nil Nil)"
  unfolding proc1_def
  apply safe
  apply (induct rule:semantics.cases)
       apply (simp_all add:semantics.intros)
   apply clarsimp
   apply (erule proc_input_by_output_false)
  by (metis One_nat_def frame.simps(3) frame.simps(4) frame.simps(5)
      joinable_not_in_proc1 proc1_def proc_input_is_0 proc_output_is_1)

lemma ltau_not_in_proc1_gen:
  "\<not> semantics {} proc1 LTau P"
  apply safe 
  apply (induct "{}::condition set" "proc1" LTau P arbitrary:P rule:semantics.induct)
  unfolding proc1_def 
     apply (simp_all add:semantics.intros)
     apply clarsimp
     apply (erule semantics.cases; simp)+
  apply clarsimp
  using connection_nil is_refl.simps(2) by blast

lemma ltau_in_par_both:
  "Q=(Par (Par Nil Nil) proc2)
   \<Longrightarrow>stuck Q \<and> semantics {} (Par proc1 proc2) LTau (Par (Par Nil Nil) proc2)"
  apply safe 
  apply (simp add: nil_stuck par_stuck_stuck_is_stuck proc2_stuck)
  apply (rule semantics_par_l)
  apply (unfold proc1_def proc2_def)
  apply (rule_tac n=0 and m=1 in semantics_com_r)
    apply (rule semantics_input)
   apply (rule semantics_output)
  apply (auto intro:connection.intros)
  done 

lemma frame_from_stuck_action:
  "stuck R \<Longrightarrow> semantics (A \<union> frame R) P \<alpha> P' \<Longrightarrow>
    semantics A (Par P R) \<alpha> (Par P' R)"
  by (auto intro:semantics.intros)

\<comment> \<open>The LTau must in traces of (par proc1 proc2) while not in proc2\<close>

lemma ltau_in_traces_both: 
  "[LTau] \<in> traces_of (Par proc1 proc2)"
  unfolding traces_of_def
  using ltau_in_par_both proc1_def proc2_def by auto

lemma ltau_not_in_trace_proc1:
  "[LTau] \<notin> traces_of proc1"
  unfolding traces_of_def proc1_def proc2_def 
  apply clarsimp
  by (metis One_nat_def ltau_not_in_proc1_gen proc1_def)

\<comment> \<open>The reconstruced version of the 3-d is\<close>
lemma traces_of_not_antimonotonic_example: 
  "stuck proc2 \<Longrightarrow> traces_of (Par proc1 proc2) \<subseteq> traces_of proc1 \<Longrightarrow> false"
  using ltau_in_traces_both ltau_not_in_trace_proc1 by blast

subsection "Question 3 (e)"
lemma traces_of_not_antimonotonic:
  assumes "\<And>P R. stuck R \<Longrightarrow> traces_of (Par P R) \<subseteq> traces_of P"
  shows "False"
  using assms 
  using proc2_stuck traces_of_not_antimonotonic_example by auto

subsection "Question 3 (f)"
lemma semantics_par_assoc0:
  assumes "semantics A (Par P Q) \<alpha> R"
  shows "\<exists>P' Q' .
           R = Par P' Q' \<and>
           semantics A (Par P Q) \<alpha> (Par P' Q')"
  using assms 
  unfolding stuck_def traces_of_def 
  using par_simp by auto

lemma semantics_par_par_l_ltau: 
  "semantics (A \<union> frame P \<union> frame S) Q (LOutput n) Q' \<Longrightarrow>
   semantics (A \<union> frame P \<union> frame Q) S (LInput m) S' \<Longrightarrow>
   Joinable n m \<in> connection (A \<union> frame P \<union> frame Q \<union> frame S) 
  \<Longrightarrow> semantics A (Par (Par P Q) S) LTau (Par (Par P Q') S')"
  apply (simp add: semantics.simps[where ?a2.0="(Par (Par P Q) S)"])
  by (smt Un_commute semantics_par_r sup_assoc)
  
lemma semantics_par_par_r_ltau:
  "semantics (A \<union> frame P \<union> frame S) Q (LInput n) P' \<Longrightarrow>
  semantics (A \<union> frame P \<union> frame Q) S (LOutput m) Q'a \<Longrightarrow>
  Joinable n m \<in> connection (A \<union> frame P \<union> frame Q \<union> frame S)
     \<Longrightarrow> semantics A (Par (Par P Q) S) LTau (Par (Par P P') Q'a)"
  apply (simp add: semantics.simps[where ?a2.0="(Par (Par P Q) S)"])
  by (smt Un_commute semantics_par_r sup_assoc)


lemma semantics_com_par_par_l_ltau:
  "semantics (A \<union> (frame Q \<union> frame S)) P (LOutput n) P' \<Longrightarrow>
   semantics (A \<union> frame P) (Par Q S) (LInput m) Q' \<Longrightarrow>
   Joinable n m \<in> connection (A \<union> frame P \<union> (frame Q \<union> frame S))
    \<Longrightarrow> \<exists>Q'a S'. Q' = Par Q'a S' \<and> 
      semantics A (Par (Par P Q) S) LTau (Par (Par P' Q'a) S')"
  apply (subst (asm) par_simp)
  apply clarsimp
  apply safe 
   apply (smt semantics_com_l semantics_par_l sup_assoc sup_commute)
  by (smt frame.simps(3) semantics_com_l semantics_par_l sup.commute sup.left_commute)

lemma semantics_com_par_par_r_ltau:
  "semantics (A \<union> (frame Q \<union> frame S)) P (LInput n) P' \<Longrightarrow>
   semantics (A \<union> frame P) (Par Q S) (LOutput m) Q' \<Longrightarrow>
   Joinable n m \<in> connection (A \<union> frame P \<union> (frame Q \<union> frame S))
    \<Longrightarrow> \<exists>Q'a S'. Q' = Par Q'a S' \<and>
    semantics A (Par (Par P Q) S) LTau (Par (Par P' Q'a) S')"
  apply (subst (asm) par_simp)
  apply clarsimp
  apply safe 
   apply (simp add: inf_sup_aci(5) inf_sup_aci(7) semantics.intros(6) semantics_par_l)
  by (smt frame.simps(3) semantics_com_r semantics_par_l sup_commute sup_left_commute)


lemma semantics_par_assoc1:
  assumes "semantics A (Par P (Par Q S)) \<alpha> R"
  shows "\<exists>P' Q' S'.
           R = Par P' (Par Q' S') \<and>
           semantics A (Par (Par P Q) S) \<alpha> (Par (Par P' Q') S')"
  using assms
  apply -
  apply (erule semantics.cases)
       apply (simp_all add:semantics.intros)
     apply clarsimp
     apply (simp add: inf_sup_aci(7) semantics_par_l sup.commute)
  apply (erule semantics.cases ;simp add:semantics.intros)
       apply (smt Un_left_commute inf_sup_aci(5) semantics_par_l semantics_par_r)
      apply (metis Un_assoc frame.simps(3) semantics_par_r)
     apply (simp add:semantics_par_par_l_ltau)
    apply (simp add: semantics_par_par_r_ltau)
   apply clarsimp
   apply (simp add: semantics_com_par_par_l_ltau)
  apply clarsimp
  apply (simp add: semantics_com_par_par_r_ltau)
  done
 

text \<open>
  This similar lemma will be needed later.
  You may use it without proof. \<close>
lemma semantics_par_assoc2:
  "semantics A (Par (Par P Q) S) \<alpha> R \<Longrightarrow>
  \<exists> P' Q' S'. R = Par (Par P' Q') S' \<and> semantics A (Par P (Par Q S)) \<alpha> (Par P' (Par Q' S'))"
  apply (erule semantics.cases)
       apply (simp_all add:semantics.intros)
     apply clarsimp
     apply (subst (asm) par_simp)
     apply (smt Un_commute frame.simps(3) semantics.intros(6)
        semantics_com_l semantics_par_l semantics_par_r sup_assoc)
    apply (metis frame.simps(3) semantics_par_r sup_assoc)
   apply clarsimp
  apply (subst (asm) par_simp, clarsimp)
  apply (smt frame.simps(3) inf_sup_aci(6) semantics_com_l semantics_par_r sup.commute)
  apply clarsimp
  apply (subst (asm) par_simp, clarsimp)
  apply safe 
   apply (smt Un_assoc frame.simps(3) inf_sup_aci(5) semantics.intros(6) semantics_par_r)
  by (smt semantics.intros(6) semantics_par_r sup.assoc sup.commute)


subsection "Question 3 (g)"
lemma list_trans_par_assoc:
  "list_trans A (Par (Par P Q) S) tr (Par (Par P' Q') S') =
       list_trans A (Par P (Par Q S)) tr (Par P' (Par Q' S'))"
  apply (unfold list_trans_def)
  apply (rule iffI)
   apply (induct arbitrary: A P Q S P' Q' S' rule:list.induct; simp)
   apply (metis (no_types, lifting) semantics_par_assoc2)
  apply (induct arbitrary: A P Q S P' Q' S' rule:list.induct; simp)
  by (metis (no_types, lifting) semantics_par_assoc1)

subsection "Question 3 (h)"
lemma stuck_par:
  "stuck(Par P Q) = (stuck P \<and> stuck Q)"
  apply safe 
  using semantics_monotonic semantics_par_l stuck_def apply fastforce 
  using semantics_monotonic semantics_par_r stuck_def apply fastforce
  by (smt Collect_mono_iff list_trans.simps(1) stuck_def traces_of_def 
      traces_of_monotonic)

subsection "Question 3 (i)"
lemma stuck_assoc:
  "stuck (Par (Par P Q) S) = stuck (Par P (Par Q S))"
  using stuck_par by presburger

lemma semantics_par_must_par_in_post:
  "semantics A (Par P Q) \<alpha> S \<Longrightarrow> \<exists> P' Q'. semantics A (Par P Q) \<alpha> (Par P' Q')"
  apply (frule semantics.cases)
  by (auto intro:semantics.intros)

lemma semantics_par_par_must_par_par_in_post1:
  "semantics A (Par P (Par Q R)) \<alpha> S 
    \<Longrightarrow> \<exists> P' Q' R'. semantics A (Par P (Par Q R)) \<alpha> (Par P' (Par Q' R'))"
  using semantics_par_assoc1 by blast

lemma semantics_par_par_must_par_par_in_post2:
  "semantics A (Par (Par P Q) R) \<alpha> S 
    \<Longrightarrow> \<exists> P' Q' R'. semantics A (Par (Par P Q) R) \<alpha> (Par (Par P' Q') R')"
  using semantics_par_assoc2 by blast

lemma semantics_par_assoc1_gen:
  "semantics A (Par (Par P Q) R) x S 
     \<Longrightarrow> \<exists>S'. semantics A (Par P (Par Q R)) x S'"
  apply (drule semantics_par_par_must_par_par_in_post2)
  apply (erule exE)+
  apply (rule_tac x="(Par  P'(Par Q' R'))" in exI)
  using semantics_par_assoc2 by force

lemma semantics_par_assoc2_gen:
  "semantics A (Par P (Par Q R)) x S 
     \<Longrightarrow> \<exists>S'. semantics A (Par (Par P Q) R) x S'"
  using semantics_par_assoc1 by blast

lemma semantics_par_assoc1_stuck_gen:
  "semantics A (Par (Par P Q) R) x S \<Longrightarrow> stuck S 
     \<Longrightarrow> \<exists>S'. semantics A (Par P (Par Q R)) x S' \<and> stuck S'"
  using semantics_par_assoc2 stuck_assoc by blast

lemma semantics_par_assoc2_stuck_gen:
  "semantics A (Par P (Par Q R)) x S \<Longrightarrow> stuck S 
     \<Longrightarrow> \<exists>S'. semantics A (Par (Par P Q) R) x S' \<and> stuck S'"
  using semantics_par_assoc1 stuck_assoc by blast

lemma list_trace_par_par_post1:
  "list_trans A (Par (Par P Q) R) x S 
     \<Longrightarrow> \<exists>P' Q' R'. S = (Par (Par P' Q') R')"
  unfolding list_trans_def 
  apply (induct arbitrary: A P Q R S rule:list.inducts,force)
  by (smt list.simps(7) semantics_par_assoc2)

lemma list_trace_par_par_post2:
  "list_trans A (Par  P (Par Q R)) x S 
     \<Longrightarrow> \<exists>P' Q' R'. S = (Par  P' (Par Q' R'))"
  unfolding list_trans_def 
  apply (induct arbitrary: A P Q R S rule:list.inducts,force)
  by (smt list.simps(7) semantics_par_assoc1)

lemma list_trans_par_assoc_gen1:
  "list_trans A (Par (Par P Q) R) tr S \<Longrightarrow>
    \<exists> S'. list_trans A (Par P (Par Q R)) tr S'"
  using list_trace_par_par_post1 list_trans_par_assoc by blast

lemma list_trans_par_assoc_gen2:
  "list_trans A (Par P (Par Q R)) tr S \<Longrightarrow>
    \<exists> S'. list_trans A (Par (Par P Q) R) tr S'"
  using list_trace_par_par_post2 list_trans_par_assoc by blast

lemma trace_eq_par_assoc:
  shows "trace_eq (Par (Par P Q) S) (Par P (Par Q S))"
  apply (unfold trace_eq_def traces_of_def )
  apply (rule equalityI)
   apply clarsimp
   using list_trace_par_par_post1 list_trans_par_assoc stuck_assoc apply blast
  apply clarsimp
  using list_trace_par_par_post2 list_trans_par_assoc stuck_assoc by blast
 
subsection "Question 3 (j)"
\<comment> \<open>TODO\<close>

lemma par_nil_is_origin:
  "semantics A (Par P Nil) tr (Par P' Nil) \<Longrightarrow> semantics A P tr P'"
  using nil par_simp by auto

lemma par_nil_has_nil_in_post:
  "semantics A (Par P Nil) tr S \<Longrightarrow>\<exists> P'. S = (Par P' Nil) \<and> semantics A (Par P Nil) tr (Par P' Nil)"
  apply (subst (asm) par_simp)
  apply clarsimp
  apply safe 
     apply (auto intro: semantics_par_mono nil)
  done

lemma par_nil_is_origin_gen:
  "semantics A (Par P Nil) tr S \<Longrightarrow>\<exists> S'.  semantics A P tr S'"
  apply (frule par_nil_has_nil_in_post)
  using par_nil_is_origin by blast

lemma list_trans_par_nil:
  "list_trans A (Par P Nil) tr (Par P' Nil) \<Longrightarrow> list_trans A P tr P'"
  apply (induct tr arbitrary:A P P', force)
  apply clarsimp
  apply (frule par_nil_has_nil_in_post)
  apply (erule exE)
  apply (rule_tac x="P'a" in exI)
  using par_nil_is_origin by blast

lemma list_trans_par_has_par_in_post:
  "list_trans A (Par P Nil) tr S 
     \<Longrightarrow> \<exists> P'. S= (Par P' Nil) \<and> list_trans A (Par P Nil ) tr (Par P' Nil)"
  apply (induct tr arbitrary:A P P', force)
  using list_trans.simps(2) par_nil_has_nil_in_post by blast

lemma list_trans_par_nil_gen: 
  "list_trans A (Par P Nil) tr S \<Longrightarrow> \<exists> S'. list_trans A P tr S'"
  apply (induct tr arbitrary: A P S)
  apply auto[1]
  using list_trans_par_has_par_in_post list_trans_par_nil by blast 
  
lemma trace_eq_nil_par:
  shows "trace_eq P (Par P Nil)"
  apply (unfold trace_eq_def traces_of_def)
  apply (rule equalityI)
  apply clarsimp
  using list_trans_stuck_one nil_stuck par_stuck_stuck_is_stuck apply blast
  apply clarsimp
  using list_trans_par_has_par_in_post list_trans_par_nil sub_stuck_par_stuck 
  by blast

subsection "Question 3 (k)"

lemma list_trans_assoc: 
  "list_trans A (Par P Q) tr S
     \<Longrightarrow> \<exists> P' Q'. S= (Par P' Q') \<and> list_trans A (Par Q P) tr (Par Q' P')"
  apply (induct tr arbitrary: A P Q S)
  sorry 

lemma trace_eq_par_comm:
  shows "trace_eq (Par P Q) (Par Q P)"
  apply (unfold trace_eq_def traces_of_def )
  apply safe
  by (metis list_trans_assoc stuck_par sub_stuck_par_stuck)+

end