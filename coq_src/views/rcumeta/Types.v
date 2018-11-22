(*This document first introduces the definitions for RCU types
that are defined in Section 4.1. Then the subtyping shown in 
Figure 3. follows.
*)
Require Import Basics.
Require Import SetoidClass.
Require Import MySetoids.
Require Import Tactics.
Require Import Bool.


(*RCU Types*)
Inductive RCUTypes:=
| rcuItrW: Path -> NextMap -> RCUType
| rcuItrR: RCUType
| rcuFresh: NextMap -> RCUType
| unlinked: RCUType
| undef: RCUType.
| freeable: RCUType
| rcuRoot: RCUType.
   