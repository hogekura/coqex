Definition tautology : forall P : Prop, P -> P := fun p x => x.

Definition Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P
  := fun p q pq =>
       fun p => 
         match pq with
           | conj not_q pq => not_q (pq p)
         end.
Definition Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q
  := fun p q p_or_q not_p =>
       match p_or_q with
         | or_introl p => match not_p p with end
         | or_intror q => q
       end.

Definition tautology_on_Set : forall A : Set, A -> A
  := fun a x => x.

Definition Modus_tollens_on_Set : forall A B : Set, (B -> Empty_set) * (A -> B) -> (A -> Empty_set)
  := fun a b x => fun a =>
       match x with
         | (b_e, a_b) => b_e (a_b a)
       end.

Definition Disjunctive_syllogism_on_Set : forall A B : Set, (A + B) -> (A -> Empty_set) -> B
  := fun a b x y =>
       match x with
         | inl a => match y a with end
         | inr b => b
       end.
