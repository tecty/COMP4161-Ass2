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

print_theorems

primrec is_refl :: "_" where
  "is_refl(Above a b) = (a = b)"
| "is_refl(Joinable a b) = (a = b)"

section "Question 1 (a)"


(*4 is router1 5 is router2*)
definition example_network where
"example_network = {
Above 1 4 , Above 2 4, Above 2 5 , Above 3 5
}"  (* TODO *)

lemma "Joinable 1 2 \<in> connection example_network"
  apply (unfold example_network_def)
  apply (rule_tac b=4 in con_join)
   apply (rule con_in)
   apply (blast)
  apply (simp add:con_in)
  done 

subsection "Questions 1 (b)-(j)"

(* 1-b *)
lemma connection_monotonic:
  assumes "\<phi> \<in> connection A"
  shows   "\<phi> \<in> connection(A \<union> B)"
  using assms
  apply (induct rule:connection.induct)
       apply (auto intro:connection.intros)
  done

lemma connection_mono : 
  "connection (connection A) \<subseteq> connection A"
  apply (safe)
  apply (erule connection.induct)
  apply (simp_all add: connection.intros)
  done

(* 1-c *)
lemma connection_idem:
  shows "connection(connection A) = connection A"
  apply (rule equalityI)
  apply (simp add:  connection_mono)
  apply (auto intro:connection.intros)
  done

(* 1-d *)
lemma connection_decompose:
  assumes "\<phi> \<in> connection(A \<union> B)"
  shows   "\<exists>C D. C \<subseteq> connection A \<and>
                 D \<subseteq> connection B \<and>
                 \<phi> \<in> connection(C \<union> D)"
  using assms
  apply -
  apply (simp add: connection.induct)
  apply (auto intro:connection.intros)
  done

(* 1-e *)

lemma connection_not_in_nil:
  "x1 \<noteq> x2 \<Longrightarrow> Above x1 x2 \<notin>connection {}"
  apply safe 
  oops 

lemma connection_nil:
  assumes "\<phi> \<in> connection {}"
  shows "is_refl \<phi>"
  (* TODO *)
  using assms 
  apply - 
  apply (induct \<phi>)
   apply (simp_all add: connection.induct)
   
  oops

(* 1-f *)
lemma con_is_refl:
  assumes "is_refl \<phi>"
  shows "\<phi> \<in> connection A"
  (* TODO *)
  using assms 
  apply - 
  apply (induct)
   apply (simp_all add: connection.inducts)
  apply (auto intro:connection.intros)
  done 
  

(* 1-g *)
lemma connection_filter_refl:
  assumes "\<phi> \<in> connection A"
  shows "\<phi> \<in> connection(A - {\<phi>. is_refl \<phi>})"
  using assms 
  apply - 


  (* TODO *)
  oops

(* 1-h *)
lemma no_above_from_join_lemma:
  assumes "Above a b \<in> connection A"
  and "\<And>a b. Above a b \<notin> A" 
  shows "a = b"
  (* TODO *)
  using assms
  apply - 
  
  oops

(* 1-i *)
lemma connection_compose:
  assumes "\<phi> \<in> connection(C \<union> D)"
  and     "C \<subseteq> connection A"
  and     "D \<subseteq> connection B"
  shows   "\<phi> \<in> connection(A \<union> B)"
  (* TODO *)
  using assms 
  apply - 
  apply (intro connection_monotonic) 

   
  
  oops

(* 1-j *)
lemma connection_compositional:
  assumes "connection A = connection B"
  shows   "connection(A \<union> C) = connection(B \<union> C)"
  (* TODO *)
  using assms 
  apply - 
   
  apply (simp_all add:assms)
   
  oops

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
  (* TODO *)
  oops

(* 2-b *)
lemma semantics_empty_env:
  assumes "semantics A P \<alpha> Q"
  shows "\<exists>\<beta> Q'. semantics {} P \<beta> Q'"
  (* TODO *)
  oops

(* 2-c *)
lemma semantics_swap_frame:
  assumes "semantics A P \<alpha> Q"
  and "connection A = connection B"
  shows "semantics B P \<alpha> Q"
  (* TODO *)
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

subsection "Question 3 (a)"

lemma trace_eq_refl:
  shows "trace_eq P P"
  (* TODO *)
  oops

lemma trace_eq_sym:
  assumes "trace_eq P Q"
    shows "trace_eq Q P"
  (* TODO *)
  oops

lemma trace_eq_trans:
  assumes "trace_eq P Q"
      and "trace_eq Q R"
    shows "trace_eq P R"
  (* TODO *)
  oops

subsection "Question 3 (b)"

lemma trace_eq_stuck:
  assumes "stuck P"
      and "stuck Q"
    shows "trace_eq P Q"
  (* TODO *)
  oops

subsection "Question 3 (c)"

lemma traces_of_monotonic:
  assumes "stuck R"
  shows "traces_of P \<subseteq> traces_of (Par P R)"
  (* TODO *)
  oops

subsection "Question 3 (d)"

text \<open>Feel free to give this answer in free-text comments,
      or as Isabelle definitions. \<close>

subsection "Question 3 (e)"

lemma traces_of_not_antimonotonic:
  assumes "\<And>P R. stuck R \<Longrightarrow> traces_of (Par P R) \<subseteq> traces_of P"
  shows "False"
  (* TODO *)
  oops

subsection "Question 3 (f)"

lemma semantics_par_assoc1:
  assumes "semantics A (Par P (Par Q S)) \<alpha> R"
  shows "\<exists>P' Q' S'.
           R = Par P' (Par Q' S') \<and>
           semantics A (Par (Par P Q) S) \<alpha> (Par (Par P' Q') S')"
  (* TODO *)
  oops

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
  oops

subsection "Question 3 (h)"

lemma stuck_par:
  "stuck(Par P Q) = (stuck P \<and> stuck Q)"
  (* TODO *)
  oops

subsection "Question 3 (i)"

lemma trace_eq_par_assoc:
  shows "trace_eq (Par (Par P Q) S) (Par P (Par Q S))"
  (* TODO *)
  oops

subsection "Question 3 (j)"

lemma trace_eq_nil_par:
  shows "trace_eq P (Par P Nil)"
  (* TODO *)
  oops

subsection "Question 3 (k)"

lemma trace_eq_par_comm:
  shows "trace_eq (Par P Q) (Par Q P)"
  (* TODO *)
  oops

end