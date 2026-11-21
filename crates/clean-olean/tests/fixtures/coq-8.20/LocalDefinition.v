(* Copyright 2026 Andrew Yates, Apache-2.0. Rebuild with Coq 8.20.1:
   coqc -q LocalDefinition.v *)
Inductive flag : Set := on | off.
Module Profile.
  Definition endian : flag := off.
End Profile.
Inductive equal (x : flag) : flag -> Prop := same : equal x x.
Theorem target_endian : equal Profile.endian off.
Proof. exact (same off). Qed.
Axiom type_only : equal on off.

Theorem target_on : equal on on.
Proof. exact (same on). Qed.
Module ProfileAlias := Profile.
Module Type T. Parameter i : flag. End T.
Module WithArgument (Input : T).
  Definition copy := Input.i.
End WithArgument.
