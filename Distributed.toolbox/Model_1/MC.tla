---- MODULE MC ----
EXTENDS Distributed, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
n1, n2, n3, n4, n5
----

\* MV CONSTANT definitions Nodes
const_16066358970552519000 == 
{n1, n2, n3, n4, n5}
----

\* CONSTANT definitions @modelParameterConstants:0Edges
const_16066358970662520000 == 
{{n1, n2}, {n1, n3}, {n2, n3}, {n2, n4}, {n3, n4}, {n3, n5}, {n4, n5}}
----

\* CONSTANT definitions @modelParameterConstants:1MaxCardinality
const_16066358970762521000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:3Root
const_16066358970862522000 == 
n1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_16066358970972523000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_16066358971072524000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_16066358971172525000 ==
Safety
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_16066358971282526000 ==
Liveness
----
=============================================================================
\* Modification History
\* Created Sun Nov 29 05:44:57 BRST 2020 by kayel
