------ MODULE positions ----
(*

Abstraction of Morpho Blue's Position protocol.  Assumes a single market.
This only contains the core logic for maintaining positions.  It does not 
take into account accured interest or converting shares/assets.

User's are mapped to a Position.  At every step, we check collatoral >= borrowed 
and that the market is liquid.  

*)
EXTENDS Naturals

CONSTANT Amounts, Users

VARIABLE positions, totalAssets, totalDebt, totalCollatoral
vars == <<positions, totalAssets, totalDebt, totalCollatoral>>

ASSUME  Users \subseteq Nat \ {0}
ASSUME  Amounts \subseteq Nat \ {0}

(* ~~~ Actions ~~~ *)

(* Supplier *)

\* Supply assets to be borrowed.  Note: we restrict supply assets 
\* to avoid state space explosion.  Normally, you can supply assets 
\* whenever you want.
SupplyAssets(u, amt) == 
    /\ positions[u].assets = 0
    /\ positions' = [positions EXCEPT ![u].assets = @ + amt]
    /\ totalAssets' = totalAssets + amt
    /\ UNCHANGED  <<totalDebt, totalCollatoral>>

\* Withdraw assets
WithdrawAssets(u, amt) ==
    LET diff == totalAssets - amt
    IN
    /\ positions[u].assets >= amt
    /\ totalDebt <= diff
    /\ positions' = [positions EXCEPT ![u].assets = @ - amt] 
    /\ totalAssets' = diff
    /\ UNCHANGED <<totalDebt, totalCollatoral>>

(*  Borrower *)

\* Supply collatoral. Requied to borrow. Note: we restrict supply assets 
\* to avoid state space explosion.  Normally, you can supply assets 
\* whenever you want.
SupplyCollatoral(u, amt) == 
    /\ positions[u].collatoral = 0
    /\ positions' = [positions EXCEPT ![u].collatoral = @ + amt]
    /\ totalCollatoral' = totalCollatoral + amt
    /\ UNCHANGED <<totalAssets, totalDebt>>

\* Withdraw collatoral
WithdrawCollatoral(u, amt) == 
    /\ positions[u].collatoral >= positions[u].borrowed + amt
    /\ positions' = [positions EXCEPT ![u].collatoral = @ - amt]
    /\ totalCollatoral' = totalCollatoral - amt
    /\ UNCHANGED <<totalAssets, totalDebt>>

\* Borrow from assets
Borrow(u, amt) ==
    /\ positions[u].borrowed = 0  \* bound the number of possible states
    /\ positions[u].collatoral >= amt
    /\ totalAssets >= totalDebt + amt
    /\ positions' = [positions EXCEPT ![u].borrowed = @ + amt]
    /\ totalDebt' = totalDebt + amt
    /\ totalAssets' = totalAssets - amt
    /\ UNCHANGED totalCollatoral

\* Repay what you borrowed
Repay(u, amt) == 
    /\ positions[u].borrowed >= amt 
    /\ positions' = [positions EXCEPT ![u].borrowed = @ - amt]
    /\ totalDebt' = totalDebt - amt 
    /\ totalAssets' = totalAssets + amt 
    /\ UNCHANGED totalCollatoral


Init == 
    /\ totalDebt = 0
    /\ totalAssets = 0
    /\ totalCollatoral = 0
    /\ positions = [u \in Users |-> [collatoral |-> 0, borrowed |-> 0, assets |-> 0]]

Next == 
    \E u \in Users, a \in Amounts:
        \/ SupplyCollatoral(u,a)
        \/ SupplyAssets(u,a)
        \/ Borrow(u,a)
        \/ Repay(u,a)
        \/ WithdrawCollatoral(u,a)
        \/ WithdrawAssets(u,a)
   
Spec == 
    /\ Init 
    /\ [][Next]_vars


(*  ~~~ Invariants / Safety ~~~ *)

\* A borrower's position always has enough collatoral
CollatoralGTEBorrowed == 
    \A u \in Users: 
        positions[u].collatoral >= positions[u].borrowed

\* The market is liquid at every state
AssetToDebt == totalAssets + totalCollatoral >= totalDebt

====