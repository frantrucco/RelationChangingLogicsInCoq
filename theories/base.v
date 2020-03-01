From Mtac2 Require Export Mtac2.
From Coq.Sets Require Export Constructive_sets.
From Coq.Relations Require Export Relations.
From Coq.Logic Require Export Classical.
From Coq.Lists Require Export List.
From RCLIC Require Export utilities.
From mathcomp Require Export ssreflect ssrnat ssrbool eqtype.

(* This removes the requirement to have all goals with the same
   hierarchy. For instance, without it, one must write:

   have a_hypothesis : some_prop.
   - the proof of some_prop.
   - the proof continues here.

   which is less convenient than

   have a_hypothesis : some_prop.
   - the proof of some_prop.
   the proof continues here.
*)
Global Set Bullet Behavior "None".


Export Tactics.
Export Sets.
