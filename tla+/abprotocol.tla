----------------------------- MODULE ABP -----------------------------
EXTENDS Naturals, Sequences

CONSTANT K

VARIABLES ch12, ch21, sap1, sap2, bit1, bit2
vars == << ch12, ch21, sap1, sap2, bit1, bit2 >>

Bit == {0,1}
headok(ch) == Len(ch) > 0

Init ==
  /\ ch12 = << >>
  /\ ch21 = << >>
  /\ sap1 = 0
  /\ sap2 = 0
  /\ bit1 = 0
  /\ bit2 = 0

\* Sender: enqueue <<payload, bit1>>
SendMSG ==
  /\ ch12' = Append(ch12, << sap1, bit1 >>)
  /\ UNCHANGED << ch21, sap1, sap2, bit1, bit2 >>

\* Sender: expected ACK (bit only)
ReceiveExpectedACK ==
  /\ headok(ch21)
  /\ LET v == Head(ch21) IN
       /\ v = bit1
       /\ ch21' = Tail(ch21)
       /\ bit1' = (bit1 + 1) % 2
       /\ sap1' = sap1 + 1
  /\ UNCHANGED << ch12, sap2, bit2 >>

\* Sender: unexpected/stale ACK -> drop it
ReceiveUnexpectedACK ==
  /\ headok(ch21)
  /\ LET v == Head(ch21) IN
       /\ v # bit1
       /\ ch21' = Tail(ch21)
  /\ UNCHANGED << ch12, sap1, sap2, bit1, bit2 >>

\* Receiver: expected data bit -> deliver once, ACK that bit, toggle
ReceiveMSG ==
  /\ headok(ch12)
  /\ LET v == Head(ch12) IN
       /\ v[2] = bit2
       /\ ch12' = Tail(ch12)
       /\ sap2' = v[1]
       /\ ch21' = Append(ch21, bit2)
       /\ bit2' = (bit2 + 1) % 2
  /\ UNCHANGED << bit1, sap1 >>

\* Receiver: duplicate data bit -> do NOT deliver, re-ACK last accepted bit
ReceiveDuplicate ==
  /\ headok(ch12)
  /\ LET v == Head(ch12) IN
       /\ v[2]
       /\ ch12' = Tail(ch12)
       /\ ch21' = Append(ch21, (1 - bit2))
  /\ UNCHANGED << sap1, sap2, bit1, bit2 >>

Liveness(K) == \A x \in 0..K : (sap1 = x) ~> (sap2 = x)

Next ==
  \/ SendMSG
  \/ ReceiveExpectedACK
  \/ ReceiveUnexpectedACK
  \/ ReceiveMSG
  \/ ReceiveDuplicate

Spec == Init /\ [][Next]_vars /\ WK_vars(ReceiveExpectedACK) /\ WK_vars(ReceiveMSG)

THEOREM Spec => Liveness(K)
=============================================================================
