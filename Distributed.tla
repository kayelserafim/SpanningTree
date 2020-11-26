------------------------------ MODULE Distributed ------------------------------
EXTENDS Integers, FiniteSets

(***************************************************************************)
(* We represent the graph by a set of Nodes of nodes and a set Edges of    *)
(* edges.  We assume that there are no edges from a node to itself and     *)
(* there is at most one edge joining any two nodes.  We represent an edge  *)
(* joining nodes m and n by the set {m, n}.  We let Root be the root node. *)
(***************************************************************************)
CONSTANTS Nodes, Edges, Root, MaxCardinality

(***************************************************************************)
(* This assumption asserts mathematically what we are assuming about the   *)
(* constants.                                                               *)
(***************************************************************************)
ASSUME /\ Root \in Nodes
       /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

(***************************************************************************)
(* Message from a origin to a destination carrying distance information.   *)
(***************************************************************************)
Message == 
       [orig : Nodes , 
        dest : Nodes, 
        dist : Nat]

(***************************************************************************)
(* The spec is a straightforward TLA+ spec of the algorithm described      *)
(* above.                                                                  *)
(***************************************************************************)       
VARIABLES mom, dist, msgs
vars == <<mom, dist, msgs>>

TypeOK == /\ mom  \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> Nat]
          /\ msgs \subseteq Message
          
          

Init == /\ mom  = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
        /\ msgs = {[ orig |-> Root, dest |-> Root, dist |-> 0]}
        
        
Send(m) == msgs' = msgs \cup {m}

(***************************************************************************)
(* The following INSTANCE statement omits the redundant clause             *)
(*                                                                         *)
(*    WITH votes <- votes, maxBal <- maxBal,                               *)
(*         Value <- Value, Acceptor <- Acceptor, Quorum <- Quorum          *)
(***************************************************************************)
S == INSTANCE SpanTree

HandleNbrs ==
        \E n \in Nodes :
            /\ Send([ orig |-> n, dest |-> n, dist |-> MaxCardinality])

HandleRoot(n) == 
        /\ n = Root
        /\ Send([ orig |-> Root, dest |-> Root, dist |-> 0])
        /\ HandleNbrs
        
HandleDist(n) ==
        \E m \in S!Nbrs(n) :
            /\ \E d \in (dist[m]+1) .. (dist[n] - 1) :
                /\ dist' = [dist EXCEPT ![n] = d]
                /\ mom'  = [mom  EXCEPT ![n] = m]
                /\ Send([ orig |-> n, dest |-> m, dist |-> d])

Next == \E n \in Nodes :
          \/ HandleRoot(n)
          \/ HandleDist(n)
                    
                    
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
   (************************************************************************)
   (* The formula WF_vars(Next) asserts that a behavior must not stop if   *)
   (* it's possible to take a Next step.  Thus, the algorithm must either  *)
   (* terminate (because Next equals FALSE for all values of dist' and     *)
   (* mom') or else it continues taking Next steps forever.  Don't worry   *)
   (* about it if you haven't learned how to express liveness in TLA+.     *)
   (************************************************************************)
-----------------------------------------------------------------------------

PostCondition == 
  \A n \in Message :
    \/ 
       /\ mom[n] = n.orig
       /\ n.orig = Root 
       /\ n.dist = 0
    \/ 
       /\ mom[n] = n.orig
       /\ \A m \in S!Nbrs(n.orig) : dist[m] = MaxCardinality
       /\ n.dist = MaxCardinality 
    \/ 
       /\ n.dest \in S!Nbrs(n.orig)
       /\ dist[n.orig] \in 1..(MaxCardinality-1)
       /\ n.dist = dist[mom[n.orig]] + 1

(***************************************************************************)
(* ENABLED Next is the TLA+ formula that is true of a state iff (if and    *)
(* only if) there is a step satisfying Next starting in the state.  Thus,  *)
(* ~ ENABLED Next asserts that the algorithm has terminated.  The safety   *)
(* property that algorithm should satisfy, that it's always true that if   *)
(* the algorith has terminated then PostCondition is true, is asserted by  *)
(* this formula.                                                           *)
(***************************************************************************)
Safety == []((~ ENABLED Next) => PostCondition)

(***************************************************************************)
(* This formula asserts the liveness condition that the algorithm          *)
(* eventually terminates                                                   *)
(***************************************************************************)
Liveness == <>(~ ENABLED Next) 


THEOREM Implementation  ==  Spec => S!Spec
-----------------------------------------------------------------------------

=============================================================================
\* Modification History
\* Last modified Sun Nov 29 05:44:53 BRST 2020 by kayel
\* Last modified Sun Nov 29 00:09:15 BRST 2020 by kayelz
\* Last modified Mon Jun 17 05:52:09 PDT 2019 by lamport
\* Created Fri Jun 14 03:07:58 PDT 2019 by lamport
