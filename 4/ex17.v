(* Ex 17 *)
Theorem hoge : forall P Q R : Prop, P \/ ~(Q \/ R) -> (P \/ ~Q) /\ (P \/ ~R).
Proof.
  refine (fun P Q R => _).
  refine (fun H => _).
  refine (match H with or_introl HP => _ | or_intror HnQR => _ end).
  - refine (conj _ _).
    + refine (or_introl _). 
      refine (HP).
    + refine (or_introl _). 
      refine (HP).
  - refine (conj _ _).
    + refine (or_intror _).
      refine (fun Hq => _).
      refine (HnQR _).
      refine (or_introl _).
      refine (Hq).
    + refine (or_intror _).
      refine (fun Hr => _).
      refine (HnQR _).
      refine (or_intror _).
      refine Hr.
Qed.
